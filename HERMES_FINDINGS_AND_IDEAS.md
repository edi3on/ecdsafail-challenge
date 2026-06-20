# Hermes ECDSA.fail Findings and Ideas

Last updated: 2026-06-20

## Current repository state at time of this note

- Working repo: `/tmp/ecdsafail-challenge`
- Local branch: `main`
- Local HEAD before this notes commit: `ac7beec Add cout layout tie-break option`
- Upstream latest fetched winner: `origin/main @ d11bdbb Accept submission 88ed0f53-3464-4eda-98fa-977bd4331ee1`
- Local branch is **2 commits ahead and 5 commits behind** upstream.
- Important: before continuing optimization, update/rebase onto `origin/main` or create a clean branch from latest winner.

## Formal submission rules

A candidate is submit-safe only if all of these are true:

1. Full validation/evaluation passes: `9024/9024` shots OK.
2. Candidate score is lower than the live best at submission time.
3. Source edits relevant to submission are only under `src/point_add/`.
4. No direct edits to generated score/result files are used as evidence.
5. No harness/Cargo/toolchain changes are part of a challenge submission.

## Formal hot-fail definition

A candidate is **hot** if any full eval reports any nonzero correctness failure, including:

- `CLASSICAL MISMATCH`
- `PHASE GARBAGE`
- `ANCILLA GARBAGE`
- nonzero failed shots/batches of any kind

Hot candidates are not submit-safe, even if their Toffoli/qubit metrics beat the live best.

## Continue / stop criteria

Continue investigating a candidate if:

- score is strictly better than live best,
- failure profile is new or meaningfully lower than previous nearby attempts,
- failure count is small enough to plausibly repair structurally,
- the change is localized and reversible.

Stop or deprioritize a candidate if:

- score is not better,
- failure signature is a duplicate,
- failures persist across nonce rerolls,
- extra qubits erase the Toffoli gain,
- the required repair looks broader than the score upside justifies.

## Safe helper commits created locally

Two default-no-op experimental knobs were added under `src/point_add/`:

- `87bf8d9 Add selective cout layout call override`
- `ac7beec Add cout layout tie-break option`

These are useful for controlled experiments, but neither is a winner by itself.

## Key discovery: cout layout force values

The `TLM_COUT_LAYOUT_FORCE_M1_KS` knob uses effective post-delta `k` values.

Observed behavior:

- `126`, `130`, `132` pass because they are no-ops in this schedule.
- `127`, `128`, `131` each occur exactly twice and actually change the circuit.

Actual call positions found:

- `k=131`: calls `2` and `513`
- `k=128`: calls `3` and `512`
- `k=127`: calls `4` and `511`

This explains why some passing settings were fake leads.

## Sweep results completed

### Multi-force / cout layout sweep

No valid winner.

Best invalid families:

- `force128` family:
  - avgT around `1,389,022.510`
  - q = `1162`
  - FAIL around `7 classical / 4 phase`
- `force131` family:
  - avgT around `1,389,019.324`
  - q = `1162`
  - FAIL around `17 classical / 8 phase`
- `force127` family:
  - avgT around `1,389,024.395`
  - q = `1162`
  - FAIL around `12 classical / 7 phase`

### Call-index sweep

Tested:

- `call2`
- `call513`
- `call3`
- `call512`
- `call4`
- `call511`
- `call2_513`
- `call3_512`
- `call4_511`
- `call2_3_4`
- `call511_512_513`

No valid winner.

Best score lead:

- `call3`
  - avgT = `1,389,017.480`
  - q = `1162`
  - FAIL `12 classical / 7 phase`

Best lower-failure combo:

- `call3_512`
  - avgT = `1,389,022.510`
  - q = `1162`
  - FAIL `7 classical / 4 phase`

This matches the `force128` family behavior.

### Tie-breaker sweep

Added/tested:

- `TLM_COUT_LAYOUT_TIE=last`

Variants tested:

- `tie_last`
- `tie_last_force128`
- `tie_last_force131`
- `tie_last_call3`
- `tie_last_call4`
- `tie_last_hyb1`

No valid winner.

Best-ish result:

- `tie_last_force128`
  - avgT = `1,389,020.722`
  - q = `1162`
  - FAIL `12 classical / 7 phase`

Large-upside but too dirty:

- `tie_last_hyb1`
  - avgT = `1,387,492.966`
  - q = `1163`
  - FAIL `18 classical / 14 phase`

### Force128 nonce sweep

Bounded nonce sweep tested:

- `100002962141` through `100002962156`

No valid winner.

Best score lead:

- `force128_n100002962147`
  - avgT = `1,389,012.583`
  - q = `1162`
  - FAIL `CLASSICAL MISMATCH`

Examples from tail:

- `force128_n100002962145`: avgT `1,389,044.694`, FAIL classical mismatch
- `force128_n100002962146`: avgT `1,389,038.375`, FAIL classical mismatch
- `force128_n100002962147`: avgT `1,389,012.583`, FAIL classical mismatch
- `force128_n100002962149`: avgT `1,389,047.462`, FAIL phase garbage
- `force128_n100002962151`: avgT `1,389,031.164`, FAIL phase garbage
- `force128_n100002962156`: avgT `1,389,024.201`, FAIL classical mismatch

Conclusion: nonce rerolling did not clean the family; likely structural hotness.

## Latest-winner update finding

After `git fetch`, upstream moved from our local base to:

- `d11bdbb Accept submission 88ed0f53-3464-4eda-98fa-977bd4331ee1`

Local branch state:

- ahead by 2 local helper commits,
- behind by 5 accepted upstream submissions.

Latest accepted upstream chain:

- `d11bdbb Accept submission 88ed0f53-3464-4eda-98fa-977bd4331ee1`
- `42b56c6 Accept submission 977a9e1a-c4af-4f7d-997b-23d284d3c16a`
- `3df690f Accept submission fe4999b2-cba6-4025-afaf-6e9293e238d4`
- `fed64cf Accept submission 6c1a65d4-677c-4bc6-8924-5aaad1ef8e4e`
- `94d44be Accept submission e385edf3-e040-4867-bf3c-d84bd2b7ea96`

Diff from prior public base to `origin/main` touches 11 files under `src/point_add/`, mostly `trailmix_ludicrous`, with roughly:

- `2017` insertions
- `412` deletions

Changed files:

- `src/point_add/mod.rs`
- `src/point_add/trailmix_ludicrous/arith.rs`
- `src/point_add/trailmix_ludicrous/codec.rs`
- `src/point_add/trailmix_ludicrous/comparator.rs`
- `src/point_add/trailmix_ludicrous/constprop.rs`
- `src/point_add/trailmix_ludicrous/ec_add.rs`
- `src/point_add/trailmix_ludicrous/fused.rs`
- `src/point_add/trailmix_ludicrous/gcd.rs`
- `src/point_add/trailmix_ludicrous/gidney.rs`
- `src/point_add/trailmix_ludicrous/mcx.rs`
- `src/point_add/trailmix_ludicrous/mod.rs`

## Strategic conclusion

The frontier is extremely tight. The best local experiments produced lower theoretical Toffoli/qubit products, but every lower-score candidate was hot.

`force128 / call3_512` remains the most informative invalid family because it has the lowest observed failure profile, but more blind nonce rerolling is unlikely to be enough.

## Highest-priority next ideas

1. **Sync to latest winner first**
   - Preserve local helper commits on a backup branch.
   - Start a new experiment branch from `origin/main`.
   - Re-evaluate the current accepted winner locally before changing anything.

2. **Mine the latest accepted diffs**
   - The latest winner made large `trailmix_ludicrous` changes.
   - Identify the exact new scoring lever: qubit reduction, fused arithmetic rewrite, layout improvement, GCD change, or constprop improvement.
   - Do not continue optimizing stale `7b7bd12` without understanding `d11bdbb`.

3. **Structural repair for force128/call3_512**
   - Compare first failing shots against baseline.
   - Classify whether mismatches are localized to y-coordinate limbs, high bits, carry/cout propagation, phase-only artifacts, or full arithmetic corruption.
   - If localized, add a compensating layout/carry correction around the changed call rather than rerolling nonce.

4. **Controlled call-pair experiments on latest winner**
   - Recreate call-index override knobs on top of `origin/main` only if still applicable.
   - Start with call pairs around the latest winner's analogous layout sites.
   - Require a full pass after every promising change.

5. **Formal result cards for each candidate**
   - For each attempt, record:
     - branch/commit,
     - env vars/knobs,
     - avg Toffoli,
     - qubits,
     - score,
     - OK/FAIL,
     - first failure type and shot,
     - whether failure signature is duplicate,
     - next action: continue/repair/stop.

6. **Avoid generated-file noise**
   - Do not commit `results.tsv` or `score.json` as challenge evidence unless explicitly needed as logs.
   - Prefer separate notes/result-card files for handoff.

## Suggested branch workflow

```bash
git fetch origin
git branch hermes-pre-latest-winner ac7beec
git checkout -b hermes/latest-winner origin/main
cargo run --release --bin build_circuit
cargo run --release --bin eval_circuit -- --note "latest winner baseline"
```

Then port only useful helper instrumentation/knobs, one commit at a time.

## Reminder

Do not submit anything hot. A lower score with any correctness failure is not a solution.
