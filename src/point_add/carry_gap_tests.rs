//! Test-only H2 zero-image/lifetime survey. No production routing or borrowing.
use super::*;
use std::collections::BTreeSet;
use std::io::Write;

#[test]
fn gap_image_native_ledger() {
    let lay = lay_double();
    let mut b = B::new();
    let d = b.alloc_n(WD);
    let v = b.alloc_n(WD);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let input = f.v[1..257].to_vec();
    let mut rng = Rng::new(4242);
    let mut models: Vec<rmd::St> = (0..64).map(|_| {
        let x = rng.below(256) % rmd::p();
        rmd::St::new(if x == N::ZERO { N::from(1u64) } else { x })
    }).collect();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &input, k, &models[k].rv); }
        for (i,q) in dirty.iter().enumerate() {
            wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995;
        }
    }).q;
    let dirt: Vec<u64> = dirty.iter().map(|q| words[q.0 as usize]).collect();
    let mut file = std::env::var("LQ_GAP_LEDGER_PATH").ok().map(|p| {
        let mut w = std::io::BufWriter::new(std::fs::File::create(p).unwrap());
        writeln!(w,"slot\tstage\tentry_op\tend_op\toperand_wires\tcommon_sample_zero_packed\tcommon_sample_zero_disjoint_operands\tcommon_sample_zero_untouched\tslot_entry_selector_zero_shots_at_stage\tfirst_selector_touch\tlast_selector_touch\tfirst_source_zero_shots\tfirst_source_wire").unwrap(); w
    });
    let mut rows = 0;
    // H3 diagnostic only: real native stage-boundary metadata support census.
    // This is finite corpus evidence, never a universal zero/loan certificate.
    let mut meta_file = std::env::var("LQ_META_LEDGER_PATH").ok().map(|p| {
        let mut w = std::io::BufWriter::new(std::fs::File::create(p).unwrap());
        writeln!(w,"slot\tstage\tentry_op\tphase_tuple_mask\tp0_ones\tp1_ones\tp2_ones\tpi_min\tpi_max\tdep_min\tdep_max\tbq_min\tbq_max\tconstant_zero_meta\tconstant_one_meta").unwrap(); w
    });
    let mut no_dropin = 0;
    let mut selector_nonzero = 0;
    for sigma in 0..lay.s {
        // Exact slot-boundary reference image, not a mid-slot invariant.
        for (k,m) in models.iter().enumerate() {
            assert!(m.pi >= 0 && m.pi < 32 && m.stk.len() < 32);
            assert!(m.r * m.cd + m.rv * m.cv <= rmd::p(), "product invariant slot {sigma} shot{k}");
            let (ed,ev) = expect_lanes(m);
            for j in 0..WD {
                assert_eq!(getb(&words,f.d[j],k) as u8, ed[j], "slot{sigma} D{j} shot{k}");
                assert_eq!(getb(&words,f.v[j],k) as u8, ev[j], "slot{sigma} V{j} shot{k}");
            }
            let j = (m.b as usize + m.pi as usize) % WD;
            assert_eq!(ev[j],0,"reference gap slot{sigma} shot{k}");
            assert_eq!(getb(&words,f.v[j],k),0,"native gap slot{sigma} shot{k}");
        }
        let vmap = f.v.clone();
        let gaps: Vec<QubitId> = models.iter().map(|m| vmap[(m.b as usize+m.pi as usize)%WD]).collect();
        b.ops.clear(); f.marks.clear();
        f.slot(&mut b,&lay,sigma);
        let row = lay.rows[sigma];
        let lc = row[3];
        let p2hi = row[4];
        let cut = if p2hi>lc {(WD-p2hi).saturating_sub(super::super::froghop_double::P3DEPTH)} else {0}.max(1);
        if let Some(w) = meta_file.as_mut() {
            for &(stage,start) in &f.marks {
                let st = run(&b.ops[..start],nq,&|x|x.copy_from_slice(&words));
                assert_eq!(st.phase,0,"stage prefix phase slot{sigma}/{stage}");
                let mut tuple_mask=0u16;
                let mut pi=Vec::new();let mut dep=Vec::new();let mut bq=Vec::new();
                for k in 0..64 {
                    let code=getb(&st.q,f.p0,k)+2*getb(&st.q,f.p1,k)+4*getb(&st.q,f.p2,k);
                    tuple_mask |= 1<<code;
                    pi.push(get(&st.q,&f.pi,k).to::<u64>());
                    dep.push(get(&st.q,&f.dep,k).to::<u64>());
                    bq.push(get(&st.q,&f.bq,k).to::<u64>());
                }
                let mut metadata=vec![("p0".to_string(),f.p0),("p1".to_string(),f.p1),("p2".to_string(),f.p2)];
                for (name,qs) in [("pi",&f.pi),("dep",&f.dep),("bq",&f.bq)] {
                    metadata.extend(qs.iter().enumerate().map(|(i,&q)|(format!("{name}{i}"),q)));
                }
                let zero=metadata.iter().filter(|(_,q)|st.q[q.0 as usize]==0).map(|(n,_)|n.clone()).collect::<Vec<_>>().join(",");
                let one=metadata.iter().filter(|(_,q)|st.q[q.0 as usize]==u64::MAX).map(|(n,_)|n.clone()).collect::<Vec<_>>().join(",");
                writeln!(w,"{sigma}\t{stage}\t{start}\t{tuple_mask}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{zero}\t{one}",st.q[f.p0.0 as usize].count_ones(),st.q[f.p1.0 as usize].count_ones(),st.q[f.p2.0 as usize].count_ones(),pi.iter().min().unwrap(),pi.iter().max().unwrap(),dep.iter().min().unwrap(),dep.iter().max().unwrap(),bq.iter().min().unwrap(),bq.iter().max().unwrap()).unwrap();
            }
        }
        for (stage,end) in [("S2","S3"),("S6","S7"),("S8","S9")] {
            if stage=="S2" && row[0]==0 || stage!="S2" && lc>=WD {continue;}
            let start = f.marks.iter().find(|x|x.0==stage).unwrap().1;
            let stop = f.marks.iter().find(|x|x.0==end).unwrap().1;
            let initial = run(&b.ops[..start],nq,&|x|x.copy_from_slice(&words));
            let first_source=match stage {"S2"=>vmap[0],"S6"=>f.d[WD-1],"S8"=>f.d[WD-cut],_=>unreachable!()};
            let first_source_zero=64-initial.q[first_source.0 as usize].count_ones();
            let mut operands = BTreeSet::new();
            match stage {
                "S2" => {operands.extend(f.d[..row[0]].iter().map(|q|q.0));operands.extend(vmap[..row[0]].iter().map(|q|q.0));},
                "S6" => {operands.extend(f.d[lc..].iter().map(|q|q.0));operands.extend(vmap[lc..].iter().map(|q|q.0));},
                "S8" => {operands.extend(f.d[lc+1..WD-cut+1].iter().map(|q|q.0));operands.extend(vmap[lc..WD-cut].iter().map(|q|q.0));},
                _=>unreachable!()
            }
            let mut touched = BTreeSet::new();
            let mut first = None;
            let mut last = None;
            for (i,op) in b.ops[start..stop].iter().enumerate() {
                for q in [op.q_target,op.q_control1,op.q_control2] {
                    if q.0 < nq as u64 {
                        touched.insert(q.0);
                        if gaps.contains(&q) {if first.is_none(){first=Some(start+i);}last=Some(start+i);}
                    }
                }
            }
            let packed: Vec<QubitId> = f.d.iter().chain(vmap.iter()).copied().collect();
            let zero:Vec<QubitId> = packed.iter().copied().filter(|q|initial.q[q.0 as usize]==0).collect();
            let disjoint = zero.iter().filter(|q|!operands.contains(&q.0)).count();
            let untouched = zero.iter().filter(|q|!touched.contains(&q.0)).count();
            let gz = (0..64).filter(|&k|getb(&initial.q,gaps[k],k)==0).count();
            // The initial universal drop-in hypothesis was falsified at slot0 S2.
            // Preserve the negative fact while collecting EVERY remaining stage.
            if sigma == 0 && stage == "S2" {
                assert_eq!(operands.len(), 2 * WD);
                assert_eq!(disjoint, 0);
                assert_eq!(untouched, 0);
            }
            if untouched==0 {no_dropin+=1;}
            if gz!=64 {selector_nonzero+=1;}
            if let Some(w)=file.as_mut() {writeln!(w,"{sigma}\t{stage}\t{start}\t{stop}\t{}\t{}\t{disjoint}\t{untouched}\t{gz}\t{}\t{}\t{first_source_zero}\t{}",operands.len(),zero.len(),first.map_or_else(||"none".into(),|x|x.to_string()),last.map_or_else(||"none".into(),|x|x.to_string()),first_source.0).unwrap();}
            rows+=1;
        }
        let result=run(&b.ops,nq,&|x|x.copy_from_slice(&words));
        assert_eq!(result.phase,0,"slot{sigma} phase");
        for (i,q) in dirty.iter().enumerate(){assert_eq!(result.q[q.0 as usize],dirt[i],"slot{sigma} dirty{i}");}
        for q in &f.pool{assert_eq!(result.q[q.0 as usize],0,"slot{sigma} pool");}
        words=result.q;
        for m in &mut models{m.fwd(sigma);}
    }
    for (k,m) in models.iter().enumerate(){
        assert!(m.ph==Ph::Dn);let _=m.result();
        let (ed,ev)=expect_lanes(m);
        for j in 0..WD{assert_eq!(getb(&words,f.d[j],k) as u8,ed[j]);assert_eq!(getb(&words,f.v[j],k) as u8,ev[j]);}
    }
    if let Some(mut w)=file{w.flush().unwrap();}
    if let Some(mut w)=meta_file{w.flush().unwrap();}
    assert!(no_dropin>0); // At least slot0 S2 must remain blocked.
    eprintln!("H2_GAP_SUMMARY slots={} shots=64 boundary_states={} stage_rows={rows} no_untouched_sample_zero={no_dropin} slot_entry_selector_nonzero_at_later_stage={selector_nonzero} physical_width={nq}",lay.s,lay.s*64);
}

#[test]
fn sampled_metadata_zero_is_not_a_borrow_contract() {
    // Deliberately chosen nonuniform input: ordinary random 64-shot census
    // missed pi's high bit. This exact reference path reaches pi=16 without
    // overflowing the inherited five-bit width. Do not borrow/narrow pi[4].
    let x = (rmd::p() >> 16usize) + N::from(1u64);
    let mut m = rmd::St::new(x);
    let mut witness = None;
    for slot in 0..32 {
        if m.pi >= 16 { witness=Some((slot,m.pi,m.ph));break; }
        m.fwd(slot);
    }
    let w=witness.expect("structured quotient must expose the fifth rotation bit");
    assert!(w.1 < 32);
    let lay=lay_double();let mut b=B::new();
    let d=b.alloc_n(WD);let v=b.alloc_n(WD);let input=v[1..257].to_vec();let par=b.alloc();let dirty=b.alloc_n(256);
    let mut f=FhDouble::alloc(&mut b,d,v,&lay,par,dirty);
    f.init(&mut b,&lay);
    for slot in 0..w.0 { f.slot(&mut b,&lay,slot); }
    let result=run(&b.ops,b.width() as usize,&|words|{for k in 0..64{put(words,&input,k,&x);}});
    assert_eq!(result.phase,0);
    for k in 0..64 {assert_eq!(get(&result.q,&f.pi,k),N::from(w.1 as u64));}
    assert_eq!(result.q[f.pi[4].0 as usize],u64::MAX,"native prefix must refute sampled high-bit zero");
    eprintln!("H3_METADATA_COUNTEREXAMPLE input=(p>>16)+1 slot={} pi={} phase={:?}; native prefix confirms pi4=1 on64 identical witness copies; not a full native packet",w.0,w.1,w.2);
}

#[test]
fn dirty_carry_restores_but_is_not_clean_comparison() {
    let mut assignments=0usize;
    let mut wrong_clean_comparisons=0usize;
    for n in [3usize,4] {
        for masked in [false,true] {
            let mut b=B::new();
            let t=b.alloc_n(n);let s=b.alloc_n(n);let c0=b.alloc();
            let f=b.alloc();let temp=b.alloc();let flag=b.alloc();let value=b.alloc();
            let spectator=b.alloc_n(4);
            // An impossible toggle value makes every cell statically masked,
            // with its running mask constantly one. The selector stays zero.
            let srcs=if masked{vec![Src{lo:0,hi:n,v:vec![value],a:2,d:1,pre:vec![],late:false}]}else{vec![]};
            let sc=Mscr{f,t:temp,gf:temp,chain:vec![],dirty:spectator.clone()};
            let ld=Lad{t:&t,s:&s,c0,srcs:&srcs,f0:true,cmpl:true,sc:&sc,keep_f:true};
            let ru=mup(&mut b,&ld);
            b.play(&ru,false);b.cx(top_carry(&ld),flag);b.play(&ru,true);
            let bound=1usize<<n;
            let total=bound*bound*2;
            for offset in (0..total).step_by(64) {
                let r=run(&b.ops,b.width() as usize,&|w|{
                    for k in 0..64{
                        let i=offset+k;if i>=total{continue;}
                        let z=i&1;let sv=(i/2)%bound;let tv=i/(2*bound);
                        put(w,&t,k,&N::from(tv));put(w,&s,k,&N::from(sv));
                        if z==1{w[c0.0 as usize]|=1<<k;}
                    }
                    for (i,q) in spectator.iter().enumerate(){w[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left(i as u32*7);}
                });
                assert_eq!(r.phase,0);
                for k in 0..64{
                    let i=offset+k;if i>=total{continue;}
                    let z=i&1;let sv=(i/2)%bound;let tv=i/(2*bound);
                    assert_eq!(get(&r.q,&t,k),N::from(tv));assert_eq!(get(&r.q,&s,k),N::from(sv));
                    assert_eq!(getb(&r.q,c0,k),z as u64);
                    assert_eq!(getb(&r.q,flag,k),(sv+z>tv) as u64,"n{n} masked{masked} T{tv} S{sv} z{z}");
                    for q in [f,temp,value]{assert_eq!(getb(&r.q,q,k),0);}
                    if z==0{assert_eq!(getb(&r.q,flag,k),(sv>tv) as u64);}
                    else if getb(&r.q,flag,k)!=(sv>tv) as u64{wrong_clean_comparisons+=1;}
                    assignments+=1;
                }
                for(i,q)in spectator.iter().enumerate(){assert_eq!(r.q[q.0 as usize],0x9e3779b97f4a7c15u64.rotate_left(i as u32*7));}
            }
        }
    }
    assert_eq!(assignments,1280);
    assert_eq!(wrong_clean_comparisons,48);
    eprintln!("H2_DIRTY_CARRY assignments={assignments} clean_contract_counterexamples={wrong_clean_comparisons}; operands/carry/spectators restored, phase zero");
}
