//! TEST ONLY: first-source-known-one encoded carry loan; not production dispatch.
//! Original support requires S[0]=1, c0=0; all ordinary clean/alias contracts hold.
//! See H3 DERIVATION.md for exact return images and off-support counterexamples.
use super::*;
use crate::circuit::OperationType;
fn one_up(b: &mut B, ld: &Lad) -> Vec<G> {
    assert_eq!(ld.c0, ld.s[0]);
    b.begin();
    if ld.cmpl {
        for &q in ld.t {
            b.x(q)
        }
    }
    let mut ds: Vec<_> = ld.srcs.iter().map(|s| Dec::new(&s.v, &s.pre)).collect();
    if ld.f0 {
        b.x(ld.sc.f)
    }
    for l in 0..ld.t.len() {
        let (t, s, x) = (ld.t[l], ld.s[l], carry_wire(ld, l));
        toggles(b, ld, &mut ds, l, true);
        if l == 0 {
            if masked(ld, 0) {
                b.x(s);
                b.ccx(ld.sc.f, t, s)
            } else {
                b.x(t);
                b.cx(t, s)
            }
        } else if masked(ld, l) {
            masked_up_cell(b, ld, l, x)
        } else {
            b.cx(s, t);
            b.cx(s, x);
            b.ccx(x, t, s)
        }
        toggles(b, ld, &mut ds, l, false);
        clear_ended(b, ld, &mut ds, l, true);
    }
    if !ld.keep_f {
        f_end(b, ld)
    }
    b.end()
}
fn one_down(b: &mut B, ld: &Lad, g: Option<QubitId>) -> Vec<G> {
    assert_eq!(ld.c0, ld.s[0]);
    assert!(g.is_none() || ld.srcs.iter().all(|s| !s.late));
    b.begin();
    let mut ds: Vec<_> = ld.srcs.iter().map(|s| Dec::new(&s.v, &s.pre)).collect();
    if !ld.keep_f {
        f_end(b, ld)
    }
    for l in (0..ld.t.len()).rev() {
        let (t, s, x) = (ld.t[l], ld.s[l], carry_wire(ld, l));
        toggles(b, ld, &mut ds, l, false);
        if l == 0 {
            if masked(ld, 0) {
                b.ccx(ld.sc.f, t, s);
                b.x(s);
                if let Some(g) = g {
                    b.ccx(g, ld.sc.f, t)
                }
            } else {
                b.cx(t, s);
                b.x(t);
                if let Some(g) = g {
                    b.cx(g, t)
                }
            }
        } else if masked(ld, l) {
            masked_down_cell(b, ld, l, x, g)
        } else {
            b.ccx(x, t, s);
            b.cx(s, x);
            b.cx(s, t);
            if let Some(g) = g {
                b.cx(s, x);
                b.ccx(g, x, t);
                b.cx(s, x)
            }
        }
        toggles(b, ld, &mut ds, l, true);
        clear_ended(b, ld, &mut ds, l, false);
    }
    if ld.f0 {
        b.x(ld.sc.f)
    }
    if ld.cmpl {
        for &q in ld.t {
            b.x(q)
        }
    }
    b.end()
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha3::digest::{ExtendableOutput, Update};
    struct Circuit {
        b: B,
        prefix: Vec<crate::circuit::Op>,
        t: Vec<QubitId>,
        s: Vec<QubitId>,
        m: Vec<QubitId>,
        g: QubitId,
        flag: QubitId,
        dirty: Vec<QubitId>,
        c: QubitId,
        masked0: bool,
        live: Vec<QubitId>,
    }
    fn build(
        n: usize,
        mode: usize,
        f0: bool,
        cmpl: bool,
        keep: bool,
        temp: bool,
        prefix: bool,
        kind: usize,
        rt: bool,
        borrow: bool,
    ) -> Circuit {
        let mut b = B::new();
        let t = b.alloc_n(n);
        let s = b.alloc_n(n);
        let m = b.alloc_n(4);
        let g = b.alloc();
        let flag = b.alloc();
        let dirty = b.alloc_n(2);
        let f = b.alloc();
        let tmp = b.alloc();
        let chain = b.alloc_n(2);
        let pre = b.alloc_n(2);
        let c = if borrow { s[0] } else { b.alloc() };
        let sc = Mscr {
            f,
            t: if temp { tmp } else { NO_QUBIT },
            gf: tmp,
            chain,
            dirty: dirty.clone(),
        };
        let mk = |lo, hi, a, d, late, v: usize| Src {
            lo,
            hi,
            a,
            d,
            late,
            v: m[v * 2..v * 2 + 2].to_vec(),
            pre: if prefix { vec![pre[v]] } else { vec![] },
        };
        let srcs = match mode {
            0 => vec![],
            1 => vec![mk(0, n, 0, 1, false, 0)],
            2 => vec![mk(0, n, n as isize - 1, -1, false, 0)],
            3 => vec![mk(0, 1, 0, 1, false, 0)],
            4 => vec![mk(0, n, 0, 1, true, 0)],
            5 => vec![
                mk(0, n, 0, 1, false, 0),
                mk(0, n, n as isize - 1, -1, true, 1),
            ],
            6 => vec![mk(0, (n + 1) / 2, 0, 1, false, 0)],
            7 => {
                if n > 1 {
                    vec![mk(1, n, -1, 1, false, 0)]
                } else {
                    vec![]
                }
            }
            8 => vec![
                mk(0, n, 0, 1, false, 0),
                mk(0, n, n as isize - 1, -1, false, 1),
            ],
            9 => vec![mk(0, 1, 0, 1, true, 0)],
            _ => unreachable!(),
        };
        let ld = Lad {
            t: &t,
            s: &s,
            c0: c,
            srcs: &srcs,
            f0,
            cmpl,
            sc: &sc,
            keep_f: keep,
        };
        let masked0 = masked(&ld, 0);
        let u = if borrow {
            one_up(&mut b, &ld)
        } else {
            mup(&mut b, &ld)
        };
        let d = if kind == 0 || kind == 3 {
            if borrow {
                one_down(&mut b, &ld, None)
            } else {
                mdown(&mut b, &ld, None)
            }
        } else {
            if borrow {
                one_down(&mut b, &ld, Some(g))
            } else {
                mdown(&mut b, &ld, Some(g))
            }
        };
        b.play(if kind == 2 { &d } else { &u }, kind == 2);
        let prefix_ops = b.ops.clone();
        b.ops.clear();
        b.begin();
        b.play(if kind == 2 { &d } else { &u }, kind == 2);
        b.cx(top_carry(&ld), flag);
        if kind == 1 || kind == 2 {
            b.cx(top_carry(&ld), g)
        }
        b.play(
            if kind == 0 || kind == 2 { &u } else { &d },
            kind == 0 || kind == 2,
        );
        let all = b.end();
        b.play(&all, false);
        if rt {
            b.play(&all, true)
        }
        for o in b.ops.iter().chain(prefix_ops.iter()) {
            if matches!(
                o.kind,
                OperationType::CX | OperationType::CCX | OperationType::CZ | OperationType::Swap
            ) {
                assert_ne!(o.q_target, o.q_control1);
                if o.kind == OperationType::CCX {
                    assert_ne!(o.q_target, o.q_control2);
                    assert_ne!(o.q_control1, o.q_control2)
                }
            }
        }
        let mut live = t.clone();
        live.extend(&s);
        live.extend(&m);
        live.push(g);
        live.push(flag);
        live.extend(&dirty);
        Circuit {
            b,
            prefix: prefix_ops,
            t,
            s,
            m,
            g,
            flag,
            dirty,
            c,
            masked0,
            live,
        }
    }
    fn put(w: &mut [u64], qs: &[QubitId], k: usize, v: usize) {
        for (i, q) in qs.iter().enumerate() {
            if (v >> i) & 1 != 0 {
                w[q.0 as usize] |= 1 << k
            }
        }
    }
    fn initial(c: &Circuit, n: usize, start: usize) -> Vec<u64> {
        let mut w = vec![0; c.b.width() as usize];
        let total = (1usize << n) * (1usize << (n - 1)) * 16 * 2 * 2 * 4;
        for k in 0..64 {
            let z = start + k;
            if z >= total {
                break;
            }
            let mut i = z;
            let dirty = i % 4;
            i /= 4;
            let flag = i % 2;
            i /= 2;
            let g = i % 2;
            i /= 2;
            let m = i % 16;
            i /= 16;
            let s = (i % (1 << (n - 1))) * 2 + 1;
            i >>= n - 1;
            let t = i;
            put(&mut w, &c.t, k, t);
            put(&mut w, &c.s, k, s);
            put(&mut w, &c.m, k, m);
            put(&mut w, &[c.g], k, g);
            put(&mut w, &[c.flag], k, flag);
            put(&mut w, &c.dirty, k, dirty);
        }
        w
    }
    fn run(_c: &Circuit, ops: &[crate::circuit::Op], w: Vec<u64>) -> Vec<u64> {
        let (_, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"h3-known-one-exhaustive");
        let mut x = h.finalize_xof();
        let mut s = crate::sim::Simulator::new(w.len(), (nb as usize).max(1), &mut x);
        s.qubits = w;
        s.apply_iter(ops.iter());
        assert_eq!(s.phase, 0, "native simulator phase");
        s.qubits
    }
    #[test]
    fn exhaustive_known_one_native_differential_inverse_and_offsupport() {
        let mut cases = [0u64; 4];
        let mut circuits = 0;
        let mut checkpoints = 0u64;
        for n in 1..=4 {
            for mode in 0..10 {
                let late = [4, 5, 9].contains(&mode);
                for f0 in [false, true] {
                    for cmpl in [false, true] {
                        for keep in [false, true] {
                            for temp in [false, true] {
                                for pre in [false, true] {
                                    for kind in 0..4 {
                                        if late && (kind == 1 || kind == 2) {
                                            continue;
                                        }
                                        for rt in [false, true] {
                                            let a = build(
                                                n, mode, f0, cmpl, keep, temp, pre, kind, rt, false,
                                            );
                                            let b = build(
                                                n, mode, f0, cmpl, keep, temp, pre, kind, rt, true,
                                            );
                                            assert_eq!(a.b.width(), b.b.width() + 1);
                                            circuits += 1;
                                            let total = (1usize << n)
                                                * (1usize << (n - 1))
                                                * 16
                                                * 2
                                                * 2
                                                * 4;
                                            for start in (0..total).step_by(64) {
                                                let ia = initial(&a, n, start);
                                                let ib = initial(&b, n, start);
                                                let ra = run(&a, &a.b.ops, ia.clone());
                                                let rb = run(&b, &b.b.ops, ib.clone());
                                                for &q in &a.live {
                                                    assert_eq!(ra[q.0 as usize],rb[q.0 as usize],"n={n} mode={mode} kind={kind} rt={rt} q={q:?} start={start}");
                                                }
                                                for i in 0..ra.len() {
                                                    if !a.live.iter().any(|q| q.0 as usize == i) {
                                                        assert_eq!(ra[i], 0, "reference scratch");
                                                    }
                                                }
                                                for i in 0..rb.len() {
                                                    if !b.live.iter().any(|q| q.0 as usize == i) {
                                                        assert_eq!(rb[i], 0, "borrow scratch");
                                                    }
                                                }
                                                if rt {
                                                    assert_eq!(ra, ia);
                                                    assert_eq!(rb, ib)
                                                }
                                                // Prefix checkpoint: compare the exact encoded carrier, not a duplicated source operand.
                                                if !rt {
                                                    let pa =
                                                        run(&a, &a.prefix, initial(&a, n, start));
                                                    let pb =
                                                        run(&b, &b.prefix, initial(&b, n, start));
                                                    let valid = if total - start >= 64 {
                                                        u64::MAX
                                                    } else {
                                                        (1u64 << (total - start)) - 1
                                                    };
                                                    for i in 0..pb.len() {
                                                        if i == b.s[0].0 as usize && b.masked0 {
                                                            assert_eq!(
                                                                pb[i] & valid,
                                                                pa[a.c.0 as usize] & valid
                                                            );
                                                            assert_eq!(
                                                                pa[a.s[0].0 as usize] & valid,
                                                                valid
                                                            )
                                                        } else {
                                                            assert_eq!(pb[i]&valid,pa[i]&valid,"encoded prefix n{n} mode{mode} kind{kind}")
                                                        }
                                                    }
                                                    if !b.masked0 {
                                                        assert_eq!(
                                                            pa[a.c.0 as usize] & valid,
                                                            valid
                                                        )
                                                    }
                                                    checkpoints += (total - start).min(64) as u64;
                                                }
                                                cases[kind] += (total - start).min(64) as u64;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        println!("PASS circuits={circuits} recorded_inverse_compare_basis={} forward_conditional_sum_basis={} independent_inverse_first_basis={} explicit_down_none_compare_basis={} encoded_prefix_basis={checkpoints} total_basis={}",cases[0],cases[1],cases[2],cases[3],cases.iter().sum::<u64>());
        println!("Widths 1..4; all target/source(S0=1)/two independent 2-bit metadata/g/flag/two dirty assignments; both f0, complement, keep_f, temp, prefix modes; actual unchanged native simulator. Late sources compare-only. Each family includes exact whole-composite inverse roundtrips. No full-width coherent simulation or integrated Q claim.");
        // Deliberate source-zero violations: actual native compare-flag counterexamples.
        for mode in [0usize, 1] {
            let a = build(1, mode, true, false, true, true, false, 0, false, false);
            let b = build(1, mode, true, false, true, true, false, 0, false, true);
            let mut ia = vec![0; a.b.width() as usize];
            let mut ib = vec![0; b.b.width() as usize];
            if mode == 1 {
                ia[a.m[1].0 as usize] = u64::MAX;
                ib[b.m[1].0 as usize] = u64::MAX;
            }
            let ra = run(&a, &a.b.ops, ia);
            let rb = run(&b, &b.b.ops, ib);
            assert_eq!(ra[a.flag.0 as usize], 0);
            assert_eq!(rb[b.flag.0 as usize], u64::MAX);
            assert_eq!(ra[a.s[0].0 as usize], 0);
            assert_eq!(rb[b.s[0].0 as usize], 0);
            assert_eq!(ra[a.t[0].0 as usize], 0);
            assert_eq!(rb[b.t[0].0 as usize], 0);
            println!("PASS expected off-support failure: masked={} T=0 S0=0 c0=0 f=1 native_flag=0 borrowed_flag=1; data restored",mode==1);
        }
    }
}
