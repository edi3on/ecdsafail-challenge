//! TEST ONLY: stateless interval-mask experiment. Never selected by production.
use super::builder::B;
use super::mask::mcx_dirty;
use crate::circuit::{Op, OperationType, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

/// Literal conjunction using only reversible X/CX/CCX; negated = true.
fn literals_x(b: &mut B, lits: &[(QubitId, bool)], target: QubitId, dirty: &[QubitId]) {
    let mut seen = std::collections::BTreeSet::new();
    for &(q, _) in lits {
        assert_ne!(q, target, "target aliases a control");
        assert!(seen.insert(q.0), "duplicate control");
    }
    let need = lits.len().saturating_sub(2);
    assert!(dirty.len() >= need, "insufficient dirty wires");
    for &q in &dirty[..need] {
        assert_ne!(q, target);
        assert!(seen.insert(q.0), "dirty wire aliases a control/dirty wire");
    }
    for &(q, neg) in lits {
        if neg {
            b.x(q);
        }
    }
    mcx_dirty(
        b,
        &lits.iter().map(|l| l.0).collect::<Vec<_>>(),
        target,
        dirty,
    );
    for &(q, neg) in lits.iter().rev() {
        if neg {
            b.x(q);
        }
    }
}

/// [v >= k] = [v > k-1]. Each zero bit of k-1 contributes one
/// disjoint first-differing-MSB prefix. v is little-endian; bounds saturate.
pub(super) fn threshold_x(
    b: &mut B,
    v: &[QubitId],
    k: isize,
    extra: &[(QubitId, bool)],
    target: QubitId,
    dirty: &[QubitId],
) {
    assert!(v.len() < isize::BITS as usize - 1);
    if k <= 0 {
        literals_x(b, extra, target, dirty);
        return;
    }
    if k >= 1isize << v.len() {
        return;
    }
    let pivot = (k - 1) as usize;
    let mut prefix = Vec::new();
    for i in (0..v.len()).rev() {
        let one = (pivot >> i) & 1 != 0;
        if !one {
            let mut term = prefix.clone();
            term.push((v[i], false));
            term.extend_from_slice(extra);
            literals_x(b, &term, target, dirty);
        }
        prefix.push((v[i], !one));
    }
}

pub(super) fn interval_x(
    b: &mut B,
    v: &[QubitId],
    lo: isize,
    hi: isize,
    extra: &[(QubitId, bool)],
    target: QubitId,
    dirty: &[QubitId],
) {
    if lo > hi {
        return;
    }
    threshold_x(b, v, lo, extra, target, dirty);
    if let Some(k) = hi.checked_add(1) {
        threshold_x(b, v, k, extra, target, dirty);
    }
}

/// Source metadata is read-only throughout the ladder. Early includes this
/// lane; late excludes it. No stored mask, decoder prefix, or clean ancilla.
pub(super) fn mask_x(
    b: &mut B,
    srcs: &[super::mask::Src],
    f0: bool,
    lane: usize,
    extra: &[(QubitId, bool)],
    target: QubitId,
    dirty: &[QubitId],
) {
    if f0 {
        literals_x(b, extra, target, dirty);
    }
    for s in srcs {
        assert!(s.d == 1 || s.d == -1, "only exact source directions +/-1");
        let end = s.hi.min(if s.late { lane } else { lane.saturating_add(1) });
        if end <= s.lo {
            continue;
        }
        let a = s.a + s.d * s.lo as isize;
        let z = s.a + s.d * (end - 1) as isize;
        interval_x(b, &s.v, a.min(z), a.max(z), extra, target, dirty);
    }
}

/// Same carry routing and ordinary cells as mask.rs; only predicate writes
/// and late equalities are expanded. sc.f, sc.t and sc.chain are unused.
pub(super) fn stateless_up(b: &mut B, ld: &super::mask::Lad) -> Vec<super::builder::G> {
    b.begin();
    if ld.cmpl {
        for &q in ld.t {
            b.x(q);
        }
    }
    let mut carry = ld.c0;
    for lane in 0..ld.t.len() {
        late_flip(b, ld, lane);
        let (t, s) = (ld.t[lane], ld.s[lane]);
        if ld.srcs.iter().any(|src| src.lo <= lane && lane < src.hi) {
            b.cx(carry, t);
            b.cx(carry, s);
            mask_x(
                b,
                ld.srcs,
                ld.f0,
                lane,
                &[(t, false), (s, false)],
                carry,
                &ld.sc.dirty,
            );
        } else {
            b.cx(s, t);
            b.cx(s, carry);
            b.ccx(carry, t, s);
            carry = s;
        }
    }
    b.end()
}

pub(super) fn stateless_down(
    b: &mut B,
    ld: &super::mask::Lad,
    g: Option<QubitId>,
) -> Vec<super::builder::G> {
    assert!(g.is_none() || ld.srcs.iter().all(|src| !src.late));
    let mut carries = Vec::new();
    let mut carry = ld.c0;
    for lane in 0..ld.t.len() {
        carries.push(carry);
        if !ld.srcs.iter().any(|src| src.lo <= lane && lane < src.hi) {
            carry = ld.s[lane];
        }
    }
    b.begin();
    for lane in (0..ld.t.len()).rev() {
        let (x, t, s) = (carries[lane], ld.t[lane], ld.s[lane]);
        if ld.srcs.iter().any(|src| src.lo <= lane && lane < src.hi) {
            mask_x(
                b,
                ld.srcs,
                ld.f0,
                lane,
                &[(t, false), (s, false)],
                x,
                &ld.sc.dirty,
            );
            if let Some(gq) = g {
                mask_x(
                    b,
                    ld.srcs,
                    ld.f0,
                    lane,
                    &[(gq, false), (s, false)],
                    t,
                    &ld.sc.dirty,
                );
            }
            b.cx(x, t);
            b.cx(x, s);
        } else {
            b.ccx(x, t, s);
            b.cx(s, x);
            b.cx(s, t);
            if let Some(gq) = g {
                b.cx(s, x);
                b.ccx(gq, x, t);
                b.cx(s, x);
            }
        }
        late_flip(b, ld, lane);
    }
    if ld.cmpl {
        for &q in ld.t {
            b.x(q);
        }
    }
    b.end()
}

fn late_flip(b: &mut B, ld: &super::mask::Lad, lane: usize) {
    for src in ld.srcs {
        if !src.late || lane < src.lo || lane >= src.hi {
            continue;
        }
        let k = src.a + src.d * lane as isize;
        if k < 0 || k >= 1isize << src.v.len() {
            continue;
        }
        let lits: Vec<_> = src
            .v
            .iter()
            .enumerate()
            .map(|(i, &q)| (q, (k >> i) & 1 == 0))
            .collect();
        literals_x(b, &lits, ld.t[lane], &ld.sc.dirty);
    }
}

fn simulate(ops: &[Op], init: &[u64]) -> (Vec<u64>, u64, Vec<u64>) {
    let mut h = sha3::Shake256::default();
    h.update(b"stateless-mask-experiment");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(init.len(), 4, &mut xof);
    s.qubits.copy_from_slice(init);
    s.phase = 0x369c_5aa5_1234_fedc;
    s.bits
        .copy_from_slice(&[0, !0, 0x5555_aaaa_ffff_0000, 0x1234_5678_9abc_def0]);
    let phase = s.phase;
    let bits = s.bits.clone();
    s.apply_iter(ops.iter());
    assert_eq!(s.phase, phase, "unexpected phase change");
    assert_eq!(s.bits, bits, "classical spectator changed");
    (s.qubits, s.phase, s.bits)
}

fn word_value(v: &[QubitId], value: usize) -> Vec<u64> {
    v.iter()
        .enumerate()
        .map(|(i, _)| if value >> i & 1 != 0 { !0 } else { 0 })
        .collect()
}

fn random_words(n: usize, seed: u64) -> Vec<u64> {
    let mut x = seed | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        })
        .collect()
}

fn reversible_only(b: &B) {
    for op in &b.ops {
        assert!(
            matches!(
                op.kind,
                OperationType::X | OperationType::CX | OperationType::CCX
            ),
            "replacement must not measure"
        );
        op.validate();
    }
}

/// Every v value appears in a packed simulator shot (repeated for n<6).
fn check_predicate(b: &B, n: usize, mut expected: impl FnMut(usize) -> bool) {
    reversible_only(b);
    let mut init = random_words(b.width() as usize, 0x1234_5678);
    for i in 0..n {
        init[i] = (0..64).fold(0, |w, shot| w | (((shot >> i & 1) as u64) << shot));
    }
    for controls in 0..4 {
        init[n] = if controls & 1 != 0 { !0 } else { 0 };
        init[n + 1] = if controls & 2 != 0 { !0 } else { 0 };
        let mut want = init.clone();
        let pred = (0..64).fold(0, |w, shot| {
            w | ((expected(shot & ((1 << n) - 1)) as u64) << shot)
        });
        want[n + 2] ^= pred & init[n] & !init[n + 1];
        assert_eq!(simulate(&b.ops, &init).0, want);
    }
}

#[test]
fn maskless_exhaustive_thresholds_intervals() {
    let mut thresholds = 0;
    let mut intervals = 0;
    let mut values = 0;
    for n in 1..=6 {
        let end = 1isize << n;
        for lo in -2..=end + 2 {
            let mut b = B::new();
            let v = b.alloc_n(n);
            let c = b.alloc_n(2);
            let t = b.alloc();
            let dirty = b.alloc_n(n);
            b.alloc();
            threshold_x(&mut b, &v, lo, &[(c[0], false), (c[1], true)], t, &dirty);
            check_predicate(&b, n, |x| x as isize >= lo);
            thresholds += 1;
            values += 1usize << n;
            for hi in -2..=end + 2 {
                b.ops.clear();
                b.tof = 0;
                interval_x(
                    &mut b,
                    &v,
                    lo,
                    hi,
                    &[(c[0], false), (c[1], true)],
                    t,
                    &dirty,
                );
                check_predicate(&b, n, |x| lo <= x as isize && x as isize <= hi);
                intervals += 1;
                values += 1usize << n;
            }
        }
    }
    println!("predicate coverage: {thresholds} thresholds, {intervals} ordered endpoint intervals, {values} distinct value/case checks; all n=1..6; endpoints -2..=2^n+2");
}

fn reference_mask(
    srcs: &[super::mask::Src],
    f0: bool,
    lane: usize,
    words: &[u64],
    shot: usize,
) -> bool {
    let mut f = f0;
    for s in srcs {
        let value = s.v.iter().enumerate().fold(0isize, |v, (i, q)| {
            v | ((((words[q.0 as usize] >> shot) & 1) as isize) << i)
        });
        for l in s.lo..s.hi {
            if (l < lane || (l == lane && !s.late)) && value == s.a + s.d * l as isize {
                f = !f;
            }
        }
    }
    f
}

#[test]
fn maskless_all_small_window_lane_predicates() {
    use super::mask::Src;
    let mut cases = 0;
    for n in 1..=3 {
        for lo in 0..=4 {
            for hi in lo..=5 {
                for d in [-1, 1] {
                    for a in -5..=10 {
                        for late in [false, true] {
                            for lane in 0..=6 {
                                for f0 in [false, true] {
                                    let mut b = B::new();
                                    let v = b.alloc_n(n);
                                    let c = b.alloc_n(2);
                                    let t = b.alloc();
                                    let dirty = b.alloc_n(n);
                                    let src = Src {
                                        lo,
                                        hi,
                                        v,
                                        a,
                                        d,
                                        pre: vec![],
                                        late,
                                    };
                                    mask_x(
                                        &mut b,
                                        &[src.clone()],
                                        f0,
                                        lane,
                                        &[(c[0], false), (c[1], true)],
                                        t,
                                        &dirty,
                                    );
                                    let mut words = vec![0; b.width() as usize];
                                    check_predicate(&b, n, |value| {
                                        words[..n].copy_from_slice(&word_value(&src.v, value));
                                        reference_mask(&[src.clone()], f0, lane, &words, 0)
                                    });
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    println!("literal-toggle reference: {cases} single-source lane cases, all values n=1..3; both f0, +/-1, early/late, empty windows and out-of-range matches");
}

#[test]
fn maskless_all_dirty_controls_inverse_nested() {
    for n in 1..=6 {
        let mut b = B::new();
        let v = b.alloc_n(n);
        let c = b.alloc_n(2);
        let target = b.alloc();
        let dirty = b.alloc_n(n);
        let spectator = b.alloc();
        b.begin();
        b.begin();
        interval_x(
            &mut b,
            &v,
            1,
            (1isize << n) - 2,
            &[(c[0], false), (c[1], true)],
            target,
            &dirty,
        );
        let inner = b.end();
        b.play(&inner, false);
        let outer = b.end();
        let mut inverse = B::new();
        inverse.play(&outer, true);
        b.play(&outer, false);
        reversible_only(&b);
        reversible_only(&inverse);
        let mut count = 0;
        // Exhaustive values, controls, target, dirty, spectator assignments.
        for base in (0..1usize << b.width()).step_by(64) {
            let init: Vec<u64> = (0..b.width() as usize)
                .map(|q| (0..64).fold(0, |w, s| w | ((((base + s) >> q & 1) as u64) << s)))
                .collect();
            let mut want = init.clone();
            let pred = (0..64).fold(0, |w, s| {
                let x = (base + s) & ((1 << n) - 1);
                w | (((x >= 1 && x <= (1 << n) - 2) as u64) << s)
            });
            want[target.0 as usize] ^= pred & init[c[0].0 as usize] & !init[c[1].0 as usize];
            assert_eq!(simulate(&b.ops, &init).0, want);
            assert_eq!(simulate(&inverse.ops, &init).0, want);
            assert_eq!(simulate(&inverse.ops, &want).0, init);
            assert_eq!(want[spectator.0 as usize], init[spectator.0 as usize]);
            count += 64;
        }
        println!("n={n}: exhaustive arbitrary-dirty/control/target/spectator assignments {count}; forward, inverse, roundtrip, nested recordings");
    }
}

fn emitted(rec: &[super::builder::G], inverse: bool) -> Vec<Op> {
    let mut b = B::new();
    b.play(rec, inverse);
    reversible_only(&b);
    b.ops
}

#[test]
fn maskless_small_full_ladders_differential() {
    use super::mask::{mdown, mup, Lad, Mscr, Src};
    use crate::circuit::NO_QUBIT;
    let mut total = 0usize;
    let mut circuits = 0;
    for lanes in [3, 4] {
        for style in 0..3 {
            for f0 in [false, true] {
                for cmpl in [false, true] {
                    let mut b = B::new();
                    let t = b.alloc_n(lanes);
                    let s = b.alloc_n(lanes);
                    let c0 = b.alloc();
                    let g = b.alloc();
                    let va = b.alloc_n(2);
                    let vb = b.alloc_n(2);
                    let dirty = b.alloc_n(2);
                    let spectator = b.alloc();
                    let active = b.width() as usize;
                    let f = b.alloc();
                    let srcs = match style {
                        0 => vec![
                            Src {
                                lo: 0,
                                hi: 2,
                                v: va.clone(),
                                a: 0,
                                d: 1,
                                pre: vec![],
                                late: false,
                            },
                            Src {
                                lo: 1,
                                hi: lanes,
                                v: vb.clone(),
                                a: -1,
                                d: 1,
                                pre: vec![],
                                late: false,
                            },
                        ],
                        1 => vec![Src {
                            lo: 1,
                            hi: lanes,
                            v: va.clone(),
                            a: lanes as isize,
                            d: -1,
                            pre: vec![],
                            late: false,
                        }],
                        _ => vec![Src {
                            lo: 1,
                            hi: lanes,
                            v: vb.clone(),
                            a: lanes as isize - 1,
                            d: -1,
                            pre: vec![],
                            late: true,
                        }],
                    };
                    let sc = Mscr {
                        f,
                        t: NO_QUBIT,
                        gf: NO_QUBIT,
                        chain: vec![],
                        dirty: dirty.clone(),
                    };
                    let ld = Lad {
                        t: &t,
                        s: &s,
                        c0,
                        srcs: &srcs,
                        f0,
                        cmpl,
                        sc: &sc,
                        keep_f: true,
                    };
                    let oldup = mup(&mut b, &ld);
                    let newup = stateless_up(&mut b, &ld);
                    let old_up = emitted(&oldup, false);
                    let new_up = emitted(&newup, false);
                    let old_up_inv = emitted(&oldup, true);
                    let new_up_inv = emitted(&newup, true);
                    for sum in [false, true] {
                        if style == 2 && sum {
                            continue;
                        }
                        let olddown = mdown(&mut b, &ld, if sum { Some(g) } else { None });
                        let newdown = stateless_down(&mut b, &ld, if sum { Some(g) } else { None });
                        // Exercise nested recordings with full up/return permutations.
                        b.begin();
                        b.play(&oldup, false);
                        b.play(&olddown, false);
                        let oldrec = b.end();
                        b.begin();
                        b.begin();
                        b.play(&newup, false);
                        b.play(&newdown, false);
                        let inner = b.end();
                        b.play(&inner, false);
                        let newrec = b.end();
                        let oldall = emitted(&oldrec, false);
                        let newall = emitted(&newrec, false);
                        let oldinv = emitted(&oldrec, true);
                        let newinv = emitted(&newrec, true);
                        for base in (0..1usize << active).step_by(64) {
                            let mut init = vec![0; b.width() as usize];
                            for q in 0..active {
                                init[q] = (0..64)
                                    .fold(0, |w, k| w | ((((base + k) >> q & 1) as u64) << k));
                            }
                            let ou = simulate(&old_up, &init).0;
                            let nu = simulate(&new_up, &init).0;
                            assert_eq!(
                                &ou[..active],
                                &nu[..active],
                                "up lanes={lanes} style={style}"
                            );
                            assert_eq!(nu[f.0 as usize], 0, "replacement touched unused mask wire");
                            assert_eq!(simulate(&old_up_inv, &ou).0, init);
                            assert_eq!(simulate(&new_up_inv, &nu).0, init);
                            let old = simulate(&oldall, &init).0;
                            let new = simulate(&newall, &init).0;
                            assert_eq!(
                                old, new,
                                "full forward lanes={lanes} style={style} sum={sum}"
                            );
                            assert_eq!(
                                simulate(&oldinv, &init).0,
                                simulate(&newinv, &init).0,
                                "inverse differential"
                            );
                            assert_eq!(simulate(&newinv, &new).0, init, "full roundtrip");
                            for q in va
                                .iter()
                                .chain(&vb)
                                .chain(&dirty)
                                .chain(std::iter::once(&spectator))
                            {
                                assert_eq!(new[q.0 as usize], init[q.0 as usize]);
                            }
                            total += 64;
                        }
                        circuits += 1;
                    }
                }
            }
        }
    }
    println!("small full-ladder differential: {circuits} configurations, {total} exhaustive basis assignments; 3/4 lanes, overlapping early +1, reverse -1, late -1, both f0/cmpl, optional sum; up, inverse-up, whole forward/inverse, nested, roundtrip; all dirty+spectator and all input carry/data/metadata values");
}

#[test]
fn maskless_exact_source_all_slot_geometry_edges() {
    use super::froghop_double::{BB, P3DEPTH, PIB, WD};
    use super::mask::Src;
    let lay = super::layout_double();
    let mut geometries = 0;
    let mut lane_cases = 0;
    let mut assignments = 0;
    for sigma in 0..lay.s {
        let row = lay.rows[sigma];
        let base = lay.base[sigma] as isize;
        let (lv, jw, p1lo, lc, p2hi) = (row[0], row[1], row[2], row[3], row[4]);
        let mut b = B::new();
        let pi = b.alloc_n(PIB);
        let bq = b.alloc_n(BB);
        let c = b.alloc_n(2);
        let target = b.alloc();
        let dirty = b.alloc_n(BB);
        b.alloc();
        let mut bands = Vec::new();
        let mut p1 = vec![Src {
            lo: 0,
            hi: jw.min(lv),
            v: pi.clone(),
            a: 0,
            d: 1,
            pre: vec![],
            late: false,
        }];
        if p1lo < lv {
            p1.push(Src {
                lo: p1lo,
                hi: lv,
                v: bq.clone(),
                a: -2 - base,
                d: 1,
                pre: vec![],
                late: false,
            });
        }
        bands.push((lv, false, p1));
        if lc < WD {
            let p2 = if p2hi > lc {
                vec![Src {
                    lo: WD - p2hi,
                    hi: WD - lc,
                    v: bq.clone(),
                    a: WD as isize - 1 - base,
                    d: -1,
                    pre: vec![],
                    late: false,
                }]
            } else {
                vec![]
            };
            bands.push((WD - lc, true, p2));
            let cut = if p2hi > lc {
                (WD - p2hi).saturating_sub(P3DEPTH)
            } else {
                0
            }
            .max(1);
            let p3 = if p2hi > lc {
                vec![Src {
                    lo: (WD - p2hi).saturating_sub(cut),
                    hi: WD - lc - cut,
                    v: bq.clone(),
                    a: WD as isize - 1 - base - cut as isize,
                    d: -1,
                    pre: vec![],
                    late: true,
                }]
            } else {
                vec![]
            };
            bands.push((WD - lc - cut, true, p3));
        }
        for (length, f0, srcs) in bands {
            if length == 0 {
                continue;
            }
            let mut lanes = std::collections::BTreeSet::from([0, length / 2, length - 1]);
            for src in &srcs {
                for edge in [src.lo, src.hi] {
                    for l in [edge.saturating_sub(1), edge, edge.saturating_add(1)] {
                        if l < length {
                            lanes.insert(l);
                        }
                    }
                }
            }
            for lane in lanes {
                b.ops.clear();
                b.tof = 0;
                mask_x(
                    &mut b,
                    &srcs,
                    f0,
                    lane,
                    &[(c[0], false), (c[1], false)],
                    target,
                    &dirty,
                );
                reversible_only(&b);
                for batch in (0..1usize << (PIB + BB)).step_by(64) {
                    let mut init = random_words(b.width() as usize, (sigma + batch + 1) as u64);
                    for q in 0..PIB + BB {
                        init[q] =
                            (0..64).fold(0, |w, k| w | ((((batch + k) >> q & 1) as u64) << k));
                    }
                    init[c[0].0 as usize] = !0;
                    init[c[1].0 as usize] = !0;
                    let mut want = init.clone();
                    let f = (0..64).fold(0, |w, k| {
                        w | ((reference_mask(&srcs, f0, lane, &init, k) as u64) << k)
                    });
                    want[target.0 as usize] ^= f;
                    assert_eq!(
                        simulate(&b.ops, &init).0,
                        want,
                        "exact geometry sigma={sigma} lane={lane}"
                    );
                    assignments += 64;
                }
                lane_cases += 1;
            }
            geometries += 1;
        }
    }
    println!("exact schedule all-slot edges: {geometries} P1/P2/P3 geometries from {} slots, {lane_cases} endpoint/midpoint lane cases, {assignments} exhaustive combined pi(5)/boundary(6) basis assignments; unchanged source formulas/windows, P3DEPTH={P3DEPTH}", lay.s);
}

#[test]
fn maskless_gate_costs() {
    for (n, lo, hi) in [
        (5, 0, 31),
        (5, 3, 20),
        (5, 16, 16),
        (6, 0, 63),
        (6, 7, 52),
        (6, 31, 31),
    ] {
        let mut b = B::new();
        let v = b.alloc_n(n);
        let c = b.alloc_n(2);
        let t = b.alloc();
        let dirty = b.alloc_n(n);
        interval_x(
            &mut b,
            &v,
            lo,
            hi,
            &[(c[0], false), (c[1], false)],
            t,
            &dirty,
        );
        reversible_only(&b);
        println!("cost n={n} interval=[{lo},{hi}] extra=2: CCX={} ops={} declared_wires={} clean_scratch=0",b.tof,b.ops.len(),b.width());
    }
}

#[test]
fn maskless_red_threshold_constant() {
    let mut b = B::new();
    let v = b.alloc_n(1);
    let t = b.alloc();
    threshold_x(&mut b, &v, 0, &[], t, &[]);
    let (q, _, _) = simulate(&b.ops, &[0, 0]);
    assert_eq!(q[t.0 as usize], !0, "[v >= 0] must toggle every shot");
}
