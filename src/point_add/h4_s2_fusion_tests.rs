//! Test-only finite H4 class-selected ancilla-free S2 prototype.
//! Not a streaming-decoder production replacement. No pool or production edits.
use crate::point_add::arith::ttk_add;
use crate::point_add::builder::{B, G};
use crate::point_add::mask::{Dec, Lad, Mscr, Src, mc_xor, mup, mdown, top_carry};
use crate::circuit::{QubitId, Op, OperationType, NO_QUBIT};
use sha3::digest::{ExtendableOutput, Update};

struct C {
    b: B, t: Vec<QubitId>, s: Vec<QubitId>, m: Vec<QubitId>,
    p0: QubitId, p1: QubitId, p2: QubitId, tt: QubitId,
    dep0: QubitId, par: QubitId, dirty: Vec<QubitId>,
    f: QubitId, pre: Vec<QubitId>, live: Vec<QubitId>,
}
fn layout(n: usize, reference: bool) -> (C, Option<QubitId>) {
    let mut b=B::new();
    let t=b.alloc_n(n); let s=b.alloc_n(n); let m=b.alloc_n(4);
    let p0=b.alloc(); let p1=b.alloc(); let p2=b.alloc(); let tt=b.alloc();
    let dep0=b.alloc(); let par=b.alloc(); let dirty=b.alloc_n(3);
    let f=b.alloc(); let pre=b.alloc_n(2);
    let c=if reference {Some(b.alloc())} else {None};
    let mut live=t.clone();live.extend(&s);live.extend(&m);
    live.extend([p0,p1,p2,tt,dep0,par]);live.extend(&dirty);
    (C{b,t,s,m,p0,p1,p2,tt,dep0,par,dirty,f,pre,live},c)
}
fn windows(n:usize,mode:usize)->(usize,usize) {
    match mode {0=>(n,0),1=>((n+1)/2,(n+1)/2),2=>(1,n.saturating_sub(1)),_=>unreachable!()}
}
fn srcs(c:&C,n:usize,mode:usize)->Vec<Src> {
    let (hi,lo)=windows(n,mode);
    vec![Src{lo:0,hi,v:c.m[..2].to_vec(),a:0,d:1,pre:vec![c.pre[0]],late:false},
         Src{lo,hi:n,v:c.m[2..].to_vec(),a:-1,d:1,pre:vec![c.pre[1]],late:false}]
}
fn active(n:usize,mode:usize,m:usize)->Vec<usize> {
    let(hi,lo)=windows(n,mode); let mut f=false;let mut out=vec![];
    for l in 0..n {
        let a=l<hi; let z=l>=lo;
        if a && (m&3)==l {f=!f;}
        if z && l>=1 && (m>>2)==l-1 {f=!f;}
        if !(a||z)||f {out.push(l)}
    } out
}
fn guarded(b:&mut B,r:&[G],inv:bool,controls:&[(QubitId,bool)],dirty:&[QubitId]) {
    let emit=|b:&mut B,g:G| {
        let mut cs=controls.to_vec();
        let target=match g {
            G::X(t)=>t,
            G::Cx(a,t)=>{cs.push((a,false));t},
            G::Ccx(a,d,t)=>{cs.push((a,false));cs.push((d,false));t},
            _=>panic!("subtractor must be phase-free X/CX/CCX"),
        };
        assert!(cs.iter().all(|x|x.0!=target));
        mc_xor(b,&cs,target,&[],dirty);
    };
    if inv {for &g in r.iter().rev(){emit(b,g)}} else {for &g in r{emit(b,g)}}
}
fn sub_record(b:&mut B,t:&[QubitId],s:&[QubitId],flag:QubitId,dirty:QubitId)->Vec<G> {
    b.begin();
    if t.len()==1 {
        b.x(t[0]);b.ccx(s[0],t[0],flag);b.cx(s[0],t[0]);b.x(t[0]);
    } else if !t.is_empty() {
        for &q in t {b.x(q)}
        ttk_add(b,s,t,None,Some((flag,dirty)));
        for &q in t {b.x(q)}
    }
    b.end()
}
fn prototype(n:usize,mode:usize,inverse:bool)->C {
    let(mut c,_)=layout(n,false);
    let mut da=Dec::new(&c.m[..2],&c.pre[..1]);
    let mut db=Dec::new(&c.m[2..],&c.pre[1..]);
    c.b.begin();
    for m in 0..16 {
        let a=da.ctrls(&mut c.b,m&3);let z=db.ctrls(&mut c.b,m>>2);
        assert_eq!(a.len(),1);assert_eq!(z.len(),1);
        c.b.and_c(a[0].0,z[0].0,c.f);
        let ac=active(n,mode,m);
        let t:Vec<_>=ac.iter().map(|&i|c.t[i]).collect();
        let s:Vec<_>=ac.iter().map(|&i|c.s[i]).collect();
        let u=sub_record(&mut c.b,&t,&s,c.p2,c.dirty[0]);
        let al=[(c.f,false),(c.p0,false),(c.p1,true)];
        let dv=[(c.f,false),(c.p0,true),(c.p1,false)];
        guarded(&mut c.b,&u,false,&al,&c.dirty);
        let mut l=al.to_vec();l.push((c.p2,false));
        mc_xor(&mut c.b,&l,c.tt,&[],&c.dirty);
        guarded(&mut c.b,&u,true,&al,&c.dirty);
        guarded(&mut c.b,&u,false,&dv,&c.dirty);
        c.b.begin();
        if t.len()==1 {c.b.ccx(c.p2,s[0],t[0]);}
        else if !t.is_empty(){ttk_add(&mut c.b,&s,&t,Some(c.p2),None);}
        let restore=c.b.end();
        guarded(&mut c.b,&restore,false,&dv,&c.dirty);
        mc_xor(&mut c.b,&dv,c.p2,&[],&c.dirty);
        c.b.and_u(a[0].0,z[0].0,c.f);
    }
    da.clear(&mut c.b);db.clear(&mut c.b);
    let r=c.b.end();c.b.play(&r,inverse);
    check_distinct(&c.b.ops);
    c
}
fn reference(n:usize,mode:usize)->C {
    let(mut c,carry)=layout(n,true);let ss=srcs(&c,n,mode);
    let sc=Mscr{f:c.f,t:NO_QUBIT,gf:NO_QUBIT,chain:c.pre.clone(),dirty:c.dirty.clone()};
    let ld=Lad{t:&c.t,s:&c.s,c0:carry.unwrap(),srcs:&ss,f0:false,cmpl:true,sc:&sc,keep_f:true};
    let u=mup(&mut c.b,&ld);let d=mdown(&mut c.b,&ld,Some(c.p2));
    c.b.play(&u,false);let ct=top_carry(&ld);
    mc_xor(&mut c.b,&[(c.p0,true),(c.p1,false),(ct,true)],c.p2,&[],&c.dirty);
    mc_xor(&mut c.b,&[(c.p0,false),(c.p1,true),(ct,false)],c.tt,&[],&c.dirty);
    c.b.play(&d,false);check_distinct(&c.b.ops);c
}
fn check_distinct(ops:&[Op]) {
    for o in ops {
        if matches!(o.kind,OperationType::CX|OperationType::CCX|OperationType::CZ|OperationType::Swap) {
            assert_ne!(o.q_target,o.q_control1);
            if o.kind==OperationType::CCX {assert_ne!(o.q_target,o.q_control2);assert_ne!(o.q_control1,o.q_control2)}
        }
    }
}
fn run(c:&C,w:Vec<u64>)->Vec<u64> {
    let mut h=sha3::Shake256::default();h.update(b"h4-s2-native-finite");let mut x=h.finalize_xof();
    let mut sim=crate::sim::Simulator::new(w.len(),1,&mut x);sim.qubits=w;
    sim.apply_iter(c.b.ops.iter());assert_eq!(sim.phase,0,"native phase");sim.qubits
}
fn put(w:&mut[u64],qs:&[QubitId],shot:usize,value:usize) {
    for(i,q)in qs.iter().enumerate(){if value>>i&1!=0{w[q.0 as usize]|=1u64<<shot}}
}
fn decode(c:&C,z:usize,w:&mut[u64],shot:usize) {
    for(i,q)in c.live.iter().enumerate(){if z>>i&1!=0{w[q.0 as usize]|=1u64<<shot}}
}
fn get(z:usize,shift:usize,n:usize)->usize {(z>>shift)&((1<<n)-1)}
fn compressed(v:usize,a:&[usize])->usize {a.iter().enumerate().fold(0,|r,(j,&i)|r|((v>>i&1)<<j))}
fn replace(v:usize,a:&[usize],x:usize)->usize {a.iter().enumerate().fold(v,|r,(j,&i)|(r&!(1<<i))|((x>>j&1)<<i))}
fn formula(n:usize,mode:usize,z:usize,inverse:bool)->usize {
    let m=get(z,2*n,4);let p0=get(z,2*n+4,1);let p1=get(z,2*n+5,1);
    let p=get(z,2*n+6,1);let tt=get(z,2*n+7,1);
    let s=get(z,n,n);let t=get(z,0,n);let a=active(n,mode,m);
    let modulus=1usize<<a.len();let ss=compressed(s,&a);let mut x=compressed(t,&a);
    let mut po=p;let mut to=tt;
    if p0==1&&p1==0 {to^=p^usize::from(ss>x)}
    if p0==0&&p1==1 {
        if inverse {
            x=(x+p*ss)%modulus;
            po=(1^p)^usize::from(ss>x);
        } else {
            let borrow=usize::from(ss>x);let h=p^borrow;
            x=(x+modulus-ss+h*ss)%modulus;po=1^h;
        }
    }
    let tnew=replace(t,&a,x);
    (z&!((1<<n)-1)&!(1<<(2*n+6))&!(1<<(2*n+7)))|tnew|(po<<(2*n+6))|(to<<(2*n+7))
}
#[test]
fn h4_s2_native_finite_fusion() {
    let mut forward=0u64;let mut inverse=0u64;let mut roundtrip=0u64;let mut differential=0u64;
    let mut configs=0u64;
    for n in 1..=4 {for mode in 0..3 {
        let f=prototype(n,mode,false);let i=prototype(n,mode,true);let r=reference(n,mode);
        assert_eq!(r.b.width(),f.b.width()+1);
        let total=1usize<<f.live.len();configs+=1;
        println!("GEOMETRY n={n} mode={mode} basis={total} proto_width={} proto_peak={} proto_ops={} proto_T={} inverse_ops={} inverse_T={} ref_width={} ref_ops={} ref_T={} clean_owners=mask1+prefix2 carry0 flag=p2 dirty3",f.b.width(),f.b.peak,f.b.ops.len(),f.b.tof,i.b.ops.len(),i.b.tof,r.b.width(),r.b.ops.len(),r.b.tof);
        for start in (0..total).step_by(64) {
            let mut raw=vec![0;f.b.width() as usize];let mut expected=raw.clone();let mut iexpected=raw.clone();
            for k in 0..64 {
                let z=start+k;decode(&f,z,&mut raw,k);
                decode(&f,formula(n,mode,z,false),&mut expected,k);
                decode(&f,formula(n,mode,z,true),&mut iexpected,k);
            }
            let out=run(&f,raw.clone());assert_eq!(out,expected,"forward n{n} mode{mode} start{start}");
            let inv=run(&i,raw.clone());assert_eq!(inv,iexpected,"raw inverse-first n{n} mode{mode} start{start}");
            let rt=run(&i,out.clone());assert_eq!(rt,raw,"roundtrip n{n} mode{mode} start{start}");
            forward+=64;inverse+=64;roundtrip+=64;
            // The reference's supported image requires clean p2; dirty-p2 extension is deliberately not equated.
            let mask=if ((start>>(2*n+6))&1)==0 {u64::MAX}else{0};
            if mask!=0 {
                let mut rr=raw.clone();rr.push(0);let ro=run(&r,rr);
                for &q in &f.live {assert_eq!(ro[q.0 as usize],out[q.0 as usize],"reference n{n} mode{mode} q{q:?} start{start}")}
                for(q,v)in ro.iter().enumerate(){if !r.live.iter().any(|a|a.0 as usize==q){assert_eq!(*v,0,"reference scratch")}}
                differential+=64;
            }
        }
    }}
    println!("PASS configs={configs} forward_basis={forward} independent_raw_inverse_first_basis={inverse} roundtrip_basis={roundtrip} clean_p2_original_differential_basis={differential} total_direction_basis={}",forward+inverse+roundtrip);
    println!("Widths1..4; all target/source bits, all16 joint metadata classes, all4 p0/p1 codes, both p2, arbitrary dep4/dep0/par, all8 independent dirty3 assignments. All output wires/scratch and native phase checked. Production support p2=0; AL dep4=0 is only required to interpret XOR output as a turn flag. Class enumeration replaces the streaming decoder, is not a production integration, and establishes no whole-circuit Q point.");
}

#[test]
fn h4_s2_done_parking_support() {
    let mut cases=0;
    let (mut c,_)=layout(1,false);
    c.b.begin();c.b.cx(c.p2,c.dep0);
    mc_xor(&mut c.b,&[(c.p0,true),(c.p1,true),(c.dep0,false)],c.p2,&[],&c.dirty);
    let gates=c.b.end();c.b.play(&gates,false);
    let (mut ci,_)=layout(1,false);ci.b.play(&gates,true);
    let mut native_cases=0;
    for start in (0..128).step_by(64) {
        let mut raw=vec![0;c.b.width() as usize];let mut expected=raw.clone();let mut inverse=raw.clone();
        for k in 0..64 {
            let z=start+k;let p0=z&1;let p1=z>>1&1;let p2=z>>2&1;let d=z>>3&1;let dirty=z>>4;
            put(&mut raw,&[c.p0,c.p1,c.p2,c.dep0],k,z&15);put(&mut raw,&c.dirty,k,dirty);
            let dd=d^p2;let pp=p2^((1^p0)&(1^p1)&dd);
            put(&mut expected,&[c.p0,c.p1,c.p2,c.dep0],k,p0|(p1<<1)|(pp<<2)|(dd<<3));put(&mut expected,&c.dirty,k,dirty);
            let pi=p2^((1^p0)&(1^p1)&d);let di=d^pi;
            put(&mut inverse,&[c.p0,c.p1,c.p2,c.dep0],k,p0|(p1<<1)|(pi<<2)|(di<<3));put(&mut inverse,&c.dirty,k,dirty);
        }
        let out=run(&c,raw.clone());assert_eq!(out,expected);assert_eq!(run(&ci,raw.clone()),inverse);assert_eq!(run(&ci,out),raw);native_cases+=64;
    }
    for phase in 0..5 {for dep0 in 0..2 {
        // AL/RT/DONE have depth0=0; DV/CO allow either bit.
        if (phase==0||phase>=3)&&dep0!=0{continue}
        let(p0,p1,p2)=match phase{0=>(1,0,0),1=>(0,1,0),2=>(1,1,0),3=>(0,0,0),_=>(0,0,1)};
        let parked=dep0^p2;let p2out=p2^((1^p0)&(1^p1)&parked);
        assert_eq!(p2out,0);cases+=1;
    }}
    assert_eq!(0^((1^0)&(1^0)&1),1,"unsupported RT dep0=1 witness");
    println!("PASS exact DONE-parking supported phase/dep0 cases={cases}; native_total_permutation_forward_basis={native_cases} raw_inverse_basis={native_cases} roundtrip_basis={native_cases}; unsupported RT dep0=1 p2=0 yields p2=1");
}

#[test]
fn h4_s2_literal_alias_finite_obstruction() {
    let mut tested=0;let mut failures=[0usize;2];
    for flip in 0..2 {
        let(mut c,_)=layout(1,false);
        let ss=vec![Src{lo:0,hi:1,v:c.m[..2].to_vec(),a:0,d:1,pre:vec![c.pre[0]],late:false}];
        let sc=Mscr{f:c.f,t:NO_QUBIT,gf:NO_QUBIT,chain:c.pre.clone(),dirty:c.dirty.clone()};
        let ld=Lad{t:&c.t,s:&c.s,c0:c.p2,srcs:&ss,f0:false,cmpl:true,sc:&sc,keep_f:true};
        let u=mup(&mut c.b,&ld);let d=mdown(&mut c.b,&ld,Some(c.p2));
        c.b.play(&u,false);if flip!=0{c.b.x(c.p2)}c.b.play(&d,false);check_distinct(&c.b.ops);
        let mut raw=vec![0;c.b.width() as usize];
        for k in 0..32 {put(&mut raw,&c.t,k,k&1);put(&mut raw,&c.s,k,k>>1&1);put(&mut raw,&c.dirty,k,k>>2)}
        let out=run(&c,raw);
        for k in 0..32 {
            let t=k&1;let s=k>>1&1;let wantp=usize::from(t>=s);let wantt=if wantp!=0{t-s}else{t};
            let getq=|q:QubitId|((out[q.0 as usize]>>k)&1)as usize;
            let bad=getq(c.p2)!=wantp||getq(c.t[0])!=wantt||getq(c.s[0])!=s;
            if bad {failures[flip]+=1;if k==0{println!("WITNESS unary_top_flip={flip} T=0 S=0 mask=1 carry_in=0 actual_T={} actual_S={} actual_p2={} required_T=0 required_S=0 required_DIV=1",getq(c.t[0]),getq(c.s[0]),getq(c.p2));}}
            tested+=1;
        }
        assert!(failures[flip]>0);
    }
    println!("PASS literal-alias finite obstruction: both 2/2 reversible unary top maps rejected; native cases={tested}, failures_identity={} failures_complement={}; unchanged masked up/down with c0=p2=g, one fully active lane. Not a general fusion lower bound.",failures[0],failures[1]);
}

#[test]
fn h4_s2_phase_tape_controls() {
    struct Tape(u64);
    impl sha3::digest::XofReader for Tape {fn read(&mut self,out:&mut[u8]) {assert_eq!(out.len(),8);out.copy_from_slice(&self.0.to_le_bytes())}}
    let c=prototype(2,0,false);let total=1usize<<c.live.len();let initial_phase=0xa56936c396a5c33c;
    let mut cases=0;
    for word in [0,u64::MAX,0x9696a5a55a5a9696] {
        for start in (0..total).step_by(64) {
            let mut raw=vec![0;c.b.width()as usize];let mut expected=raw.clone();
            for k in 0..64 {decode(&c,start+k,&mut raw,k);decode(&c,formula(2,0,start+k,false),&mut expected,k)}
            let mut tape=Tape(word);let mut sim=crate::sim::Simulator::new(raw.len(),1,&mut tape);sim.phase=initial_phase;sim.qubits=raw;
            sim.apply_iter(c.b.ops.iter());assert_eq!(sim.phase,initial_phase);assert_eq!(sim.qubits,expected);cases+=64;
        }
    }
    println!("PASS phase_preservation_basis={cases}; three fixed measurement tapes zero/one/alternating and nonzero initial phase. This is not exhaustive enumeration of independently varying measurement outcomes; AND-uncompute phase cancellation also follows algebraically.");
}
