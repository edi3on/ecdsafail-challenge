//! TEST ONLY: lend S[0] as c0 when S[0] is exactly zero on the full input support.
//! No production dispatch. No assumption about an arbitrary dirty first source.
use super::*;

fn up(b: &mut B, ld: &Lad) -> Vec<G> {
    assert!(!ld.s.is_empty() && ld.c0 == ld.s[0]);
    assert_eq!(ld.t.len(), ld.s.len());
    // With initial carry=0 and original S[0]=0, the first majority
    // cell is exactly the identity. Keep complement/toggle bookkeeping.
    b.begin();
    if ld.cmpl { for &q in ld.t { b.x(q); } }
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec::new(&s.v, &s.pre)).collect();
    if ld.f0 { b.x(ld.sc.f); }
    for l in 0..ld.t.len() {
        let x=carry_wire(ld,l);
        toggles(b,ld,&mut decs,l,true);
        if l!=0 {
            if masked(ld,l) { masked_up_cell(b,ld,l,x); }
            else { b.cx(ld.s[l],ld.t[l]);b.cx(ld.s[l],x);b.ccx(x,ld.t[l],ld.s[l]); }
        }
        toggles(b,ld,&mut decs,l,false);
        clear_ended(b,ld,&mut decs,l,true);
    }
    if !ld.keep_f { f_end(b,ld); }
    b.end()
}
fn down(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    assert!(!ld.s.is_empty() && ld.c0 == ld.s[0]);
    assert!(g.is_none() || ld.srcs.iter().all(|s| !s.late));
    b.begin();
    let mut decs: Vec<Dec> = ld.srcs.iter().map(|s| Dec::new(&s.v, &s.pre)).collect();
    if !ld.keep_f { f_end(b,ld); }
    for l in (0..ld.t.len()).rev() {
        let x=carry_wire(ld,l);
        toggles(b,ld,&mut decs,l,false);
        // Return through the first cell is also identity: carry and S[0]
        // are both restored to zero; adding g*S[0] writes nothing there.
        if l!=0 {
            if masked(ld,l) { masked_down_cell(b,ld,l,x,g); }
            else {
                b.ccx(x,ld.t[l],ld.s[l]);b.cx(ld.s[l],x);b.cx(ld.s[l],ld.t[l]);
                if let Some(gq)=g { b.cx(ld.s[l],x);b.ccx(gq,x,ld.t[l]);b.cx(ld.s[l],x); }
            }
        }
        toggles(b,ld,&mut decs,l,true);
        clear_ended(b,ld,&mut decs,l,false);
    }
    if ld.f0 { b.x(ld.sc.f); }
    if ld.cmpl { for &q in ld.t { b.x(q); } }
    b.end()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::point_add::tests_double::run;
    use crate::circuit::OperationType;

    fn put(w: &mut [u64], qs: &[QubitId], k: usize, n: usize) {
        for (i,q) in qs.iter().enumerate() { if (n>>i)&1 !=0 {w[q.0 as usize]|=1<<k;} }
    }
    fn emit(n: usize, borrow: bool, mode: usize, roundtrip: bool, cmpl: bool, keep_f: bool) -> (B, Vec<QubitId>, Vec<QubitId>, Vec<QubitId>, QubitId, Vec<QubitId>) {
        let mut b=B::new();let t=b.alloc_n(n);let s=b.alloc_n(n);let meta=b.alloc_n(3);
        let flag=b.alloc();let g=b.alloc();let dirty=b.alloc_n(4);
        let c=if borrow{s[0]}else{b.alloc()};
        let f=b.alloc();let tmp=b.alloc();
        let chain=b.alloc_n(3);
        let sc=Mscr{f,t:tmp,gf:tmp,chain,dirty:dirty.clone()};
        let srcs=match mode {
            0=>vec![],
            1=>vec![Src{lo:0,hi:n,v:meta.clone(),a:0,d:1,pre:vec![],late:false}],
            2=>vec![Src{lo:0,hi:n,v:meta.clone(),a:n as isize-1,d:-1,pre:vec![],late:false}],
            3=>vec![Src{lo:0,hi:1,v:meta.clone(),a:0,d:1,pre:vec![],late:false}],
            _=>unreachable!()
        };
        let ld=Lad{t:&t,s:&s,c0:c,srcs:&srcs,f0:mode!=1,cmpl,sc:&sc,keep_f};
        let ru=if borrow{up(&mut b,&ld)}else{mup(&mut b,&ld)};
        let rd=if borrow{down(&mut b,&ld,Some(g))}else{mdown(&mut b,&ld,Some(g))};
        b.begin();
        b.play(&ru,false);b.cx(top_carry(&ld),flag);b.play(&rd,false);
        let all=b.end();
        b.play(&all,false);
        if roundtrip{b.play(&all,true);}
        // Reject malformed alias gates before ever handing them to the simulator.
        for op in &b.ops {
            if matches!(op.kind,OperationType::CX|OperationType::CCX|OperationType::CZ|OperationType::Swap){
                assert_ne!(op.q_target,op.q_control1,"first-zero primitive emitted target/control alias: {:?}",op);
                if op.kind==OperationType::CCX {assert_ne!(op.q_target,op.q_control2);assert_ne!(op.q_control1,op.q_control2);}
            }
        }
        let mut output=t.clone();output.extend(&s);output.extend(&meta);output.push(flag);output.push(g);output.extend(&dirty);
        (b,t,s,meta,g,output)
    }

    #[test]
    fn exhaustive_zero_first_source_native_differential_and_inverse() {
        let mut instances=0usize;
        for n in [1usize,2,3,4] {for mode in 0..4 {for rt in [false,true] {for cmpl in [false,true] {for keep_f in [false,true] {
            let (a,ta,sa,ma,ga,oa)=emit(n,false,mode,rt,cmpl,keep_f);
            let (b,tb,sb,mb,gb,ob)=emit(n,true,mode,rt,cmpl,keep_f);
            assert_eq!(a.width(),b.width()+1,"exact one-wire component saving");
            let bound=1usize<<n;let total=bound*(bound/2)*8*2;
            for start in (0..total).step_by(64) {
                let initial=|w:&mut Vec<u64>,t:&[QubitId],s:&[QubitId],m:&[QubitId],g:QubitId,o:&[QubitId]|{
                    for k in 0..64 {let i=start+k;if i>=total{continue;}
                        let gv=i&1;let mv=(i/2)%8;let sv=((i/16)%(bound/2))*2;let tv=i/(16*(bound/2));
                        put(w,t,k,tv);put(w,s,k,sv);put(w,m,k,mv);if gv!=0{w[g.0 as usize]|=1<<k;}
                    }
                    for (j,q) in o[o.len()-4..].iter().enumerate(){w[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left(j as u32*7);}
                };
                let ra=run(&a.ops,a.width() as usize,&|w|initial(w,&ta,&sa,&ma,ga,&oa));
                let rb=run(&b.ops,b.width() as usize,&|w|initial(w,&tb,&sb,&mb,gb,&ob));
                assert_eq!(ra.phase,0);assert_eq!(rb.phase,0);
                for(q1,q2)in oa.iter().zip(&ob){assert_eq!(ra.q[q1.0 as usize],rb.q[q2.0 as usize],"n{n} mode{mode} rt{rt} start{start}");}
                if rt {
                    let mut init=vec![0; b.width() as usize];initial(&mut init,&tb,&sb,&mb,gb,&ob);
                    assert_eq!(rb.q,init,"full native inverse/dirty/phase restoration");
                } else {
                    for (j,q) in ob[ob.len()-4..].iter().enumerate(){assert_eq!(rb.q[q.0 as usize],0x9e3779b97f4a7c15u64.rotate_left(j as u32*7));}
                    let live:std::collections::BTreeSet<_>=ob.iter().map(|q|q.0 as usize).collect();
                    for j in 0..rb.q.len(){if !live.contains(&j){assert_eq!(rb.q[j],0,"scratch restored");}}
                }
                instances+=(total-start).min(64);
            }
        }}}}}
        eprintln!("FIRST_ZERO_NATIVE basis_instances={instances}; forward differential, nested recording inverse, phase, dirty spectators; exactly one fewer component wire; full source-zero support only");
    }
}
