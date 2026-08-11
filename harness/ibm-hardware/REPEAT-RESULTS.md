# Second-snapshot replication — paper question E4 (RESULTS)

**Status: COMPLETE — all 8 pre-registered pairs replicated.** (`ibm_fez` finally cleared its queue
after ~23 h. The earlier PARTIAL wording is superseded.) We fixed the analysis rule in advance, in
`REPEAT-PREREG.md`, written after submission and before we read any result.

## What ran

| device | pairs | job | QPU-s | outcome |
|---|---|---|---|---|
| `ibm_marrakesh` (Heron r2) | 5 | `d9k5uljjf64c739hn19g` | 106.9 | **DONE** |
| `ibm_fez` (Heron r2) | 3 | `d9k5um0ii2cc73efn7l0` | ~61 | **DONE** — after ~23 h queued (peaked at ~5000 pending) |

Free-tier budget was **not** the binding constraint. The rolling 600 s/28-day window had 227 s
remaining, and the fez job needs about 47 s. Queue depth was the binding constraint.

## Why this is a genuinely different calibration snapshot

We do not assert this from timestamps. It is checkable in the artifact. **All 24 pre-registered
qubits report a different readout error** than the value pinned in `sweep_prereg.json`. Examples
(marrakesh):
q98 `0.0017 → 0.0083` (≈5× worse), q6 `0.0020 → 0.0044`, q141 `0.0029 → 0.0037`.

Backend `last_update_date` at submission: marrakesh **2026-07-28 02:44 EDT**, fez **03:37 EDT**.
Both dates are later than the snapshot-1 run. `repeat_results.json` stores the full live snapshot
(per-qubit readout error + T2) under its `calibration` key. The first sweep did not record that
provenance.

## Result — `ibm_marrakesh`, same 5 pairs, second snapshot

| pair | victim | snapshot 1 · d=1 | snapshot 2 · d=1 | snapshot 2 · d=2 | verdict |
|---|---|---|---|---|---|
| 0 | q98  | ΔP=0.3663, z=77.0 | **ΔP=0.4066, z=82.3** | ΔP=0.0027, z=0.5 | HOLDS |
| 1 | q6   | ΔP=0.2408, z=46.9 | **ΔP=0.2696, z=56.0** | ΔP=0.0007, z=0.2 | HOLDS |
| 2 | q141 | ΔP=0.0508, z=9.5  | **ΔP=0.1249, z=23.8** | ΔP=0.0024, z=0.4 | HOLDS |
| 3 | q146 | ΔP=0.2995, z=59.5 | **ΔP=0.1245, z=22.7** | ΔP=0.0040, z=0.7 | HOLDS |
| 4 | —    | ΔP=0.2653, z=57.1 | **ΔP=0.3430, z=66.5** | ΔP=0.0085, z=1.8 | HOLDS |

**Snapshot 2: leak at d=1 on 5/5 · leak at d≥2 on 0/5 · no pair flipped leak status.**
Combined across both snapshots: **13 pair-observations, 12 leak at d=1, 0 leak at d≥2.**

## The finding worth reporting beyond "it replicated"

Leak **magnitude is calibration-dependent and unstable**. Pair 2 more than doubled (z 9.5 → 23.8).
Pair 3 more than halved (z 59.5 → 22.7), for the same qubits and protocol, hours apart. The
**structural boundary did not move at all**: every d=1 pair leaked, and no d≥2 pair did, in both
snapshots.

The paper previously justified this design decision only on principle. This result gives it direct
empirical support. The certificate must guarantee **placement** (no shared coupling edge), not
bound crosstalk **magnitude**. A magnitude-based guarantee calibrated on snapshot 1 is wrong by 2×
in both directions within hours. The structural guarantee was invariant.

## Third snapshot (`mrk_t3`) — same pairs, ~18 h after snapshot 1

We ran two `ibm_marrakesh` pairs (0, 1) a third time (job `d9khifrhdfks73cjm760`, 43 QPU-s,
calibration `2026-07-28 15:47 EDT`, that is, a *third* distinct calibration).

| pair | victim | snap 1 (~05:00Z) | snap 2 (~08:00Z) | snap 3 (~23:21Z) | d≥2, snap 3 |
|---|---|---|---|---|---|
| 0 | q98 | ΔP=0.3663, z=77.0 | ΔP=0.4066, z=82.3 | **ΔP=0.2728, z=55.2** | ΔP=0.0026, z=0.6 |
| 1 | q6  | ΔP=0.2408, z=46.9 | ΔP=0.2696, z=56.0 | **ΔP=0.3555, z=72.6** | ΔP=0.0046, z=0.9 |

**leak@d1 2/2 · leak@d≥2 0/2.**

**The two pairs drifted in opposite directions** (pair 0, 0.366 → 0.407 → 0.273 — pair 1,
0.241 → 0.270 → 0.356). This rules out a *global* device-level drift — a temperature or
chip-wide calibration shift moves both the same way. It instead points to **per-coupler ZZ
variation between recalibrations**. It is the sharpest form of the magnitude-instability result.
Leak strength is not merely noisy. It is independently noisy per qubit pair, so no single
device-level crosstalk bound covers both pairs across these three snapshots.

The structural d=1 / d≥2 boundary did not move in any of the three.

## Cumulative across all snapshots

**15 pair-observations · 14 leak at d=1 · 0 leak at d≥2 · validator sound on 15/15.**

- Snapshot 1: 8 pairs, 7 leak.
- Snapshot 2: 5 marrakesh pairs, 5 leak.
- Snapshot 3: 2 pairs, 2 leak.

## COMPLETE snapshot-2 result (all 8 pairs)

| device | pair | snap 1 · d=1 | snap 2 · d=1 | snap 2 · d≥2 | verdict |
|---|---|---|---|---|---|
| marrakesh | 0 | ΔP=0.3663, z=77.0 | ΔP=0.4066, z=82.3 | z=0.5 | HOLDS |
| marrakesh | 1 | ΔP=0.2408, z=46.9 | ΔP=0.2696, z=56.0 | z=0.2 | HOLDS |
| marrakesh | 2 | ΔP=0.0508, z=9.5  | ΔP=0.1249, z=23.8 | z=0.4 | HOLDS |
| marrakesh | 3 | ΔP=0.2995, z=59.5 | ΔP=0.1245, z=22.7 | z=0.7 | HOLDS |
| marrakesh | 4 | ΔP=0.2653, z=57.1 | ΔP=0.3430, z=66.5 | z=1.8 | HOLDS |
| **fez** | **0** | **ΔP=0.0002, z=0.0 (NO LEAK)** | **ΔP=0.1184, z=22.4 (LEAK)** | z=0.3 | **FLIPPED** |
| fez | 1 | ΔP=0.1727, z=33.2 | ΔP=0.1830, z=37.8 | z=0.1 | HOLDS |
| fez | 2 | ΔP=0.1970, z=41.7 | ΔP=0.2720, z=51.2 | z=0.2 | HOLDS |

**Snapshot 2: leak@d1 8/8 · leak@d≥2 0/8 · validator sound 8/8.**

## The flip is the most important result of the replication

The paper described `ibm_fez` pair 0, the **single null** of snapshot 1, as a case with no leak.
It called the rejected placement "a harmless conservative over-block." **On the second
calibration it leaks at z=22.4.**

That reverses the interpretation, in the direction that favors the design:

- The validator correctly rejected that placement. It was **not** an over-block: snapshot 1 did
  not detect the channel at that calibration.

- Across snapshots, **every one of the 8 pre-registered pairs leaked at d=1 at some point.** The
  "7/8" of snapshot 1 was a property of *that calibration*, not of the pairs.

- Most consequentially: **a policy that measures leak magnitude and whitelists the quiet pair is
  wrong within hours.** The structural certificate rejected that placement in both snapshots,
  before and after the channel became measurable. This is the empirical case for guaranteeing
  *placement* rather than *measured magnitude*. It is much stronger than the drift argument alone:
  a whitelist derived from snapshot 1 actively introduces a vulnerability.

## Cumulative across all snapshots

| snapshot | pairs | leak@d1 | leak@d≥2 |
|---|---|---|---|
| 1 (~05:00Z) | 8 | 7 | 0 |
| 2 (~08:00Z / fez ~07:00Z+1d) | 8 | 8 | 0 |
| 3 (~23:21Z, marrakesh subset) | 2 | 2 | 0 |
| **total** | **18** | **17** | **0** |

**Validator soundness (never accepted a leaking placement): 18/18.**
**k=1 sufficiency (no leak at d≥2): 18/18.**

## New-pairs run (`mrk_new`) — 5 previously-unmeasured pairs

We submitted this run after we abandoned `ibm_kingston` (`PROVENANCE.md` records that cancelled
arm). We selected pairs by the same calibration-only rule and excluded **every already-measured
qubit** (`--exclude-measured`, which bars 15 qubits). These are independent couplers, not a
re-run. Job `d9kuj2ibr2fc73e7toog`, 103 QPU-s, calibration `2026-07-29 07:22 EDT`.

| pair | victim | d=1 | d≥2 | verdict |
|---|---|---|---|---|
| 0 | q5  | ΔP=0.1296, z=23.7 | ΔP=0.0048, z=1.1 | HOLDS |
| 1 | q14 | ΔP=0.0551, z=14.0 | ΔP=0.0068, z=1.3 | HOLDS |
| 2 | q75 | ΔP=0.1551, z=30.3 | ΔP=0.0034, z=0.6 | HOLDS |
| 3 | q34 | ΔP=0.3022, z=68.1 | ΔP=0.0085, z=1.6 | HOLDS |
| 4 | q21 | ΔP=0.2474, z=52.8 | ΔP=0.0013, z=0.2 | HOLDS |

**leak@d1 5/5 · leak@d≥2 0/5.**

These pairs are systematically *weaker* than the originals (ΔP 0.055–0.30 vs up to 0.41). This is
expected: the original selection took the best-readout qubits, so these are the next tier. Every
pair leaked at d=1 as well. Across all 13 distinct pairs, the d=1 effect spans **ΔP 0.055 → 0.41,
roughly 8×**. That is one more reason a magnitude-calibrated policy is the wrong instrument.

## FINAL TOTALS across every run

| run | pairs | leak@d1 | leak@d≥2 |
|---|---|---|---|
| snapshot 1 | 8 | 7 | 0 |
| snapshot 2 (replication) | 8 | 8 | 0 |
| snapshot 3 (`mrk_t3`) | 2 | 2 | 0 |
| new pairs (`mrk_new`) | 5 | 5 | 0 |
| **total observations** | **23** | **22** | **0** |

- **13 distinct qubit pairs** measured, across **2 devices** and **4 calibrations**.
- **Validator soundness: 23/23** — it never accepted a placement that leaked.
- **k=1 sufficiency: 23/23** — no pair leaked at graph distance ≥ 2, on any pair, device, or
  calibration. This is the strongest form of the paper's load-bearing structural assumption, and it
  survived 13 independent chances to fail.

## Honest limits

- ~~3 of 8 pairs were not replicated~~ — **superseded**: all 8 pairs are now replicated.
- Both snapshots fall on the **same calendar day** (~1–3 h apart, spanning at least one
  recalibration per device). This removes the *single-calibration-snapshot* objection. It does
  **not** establish multi-day, cross-generation, or cross-device-family stability.
- `ibm_fez` was the device carrying the one null pair in snapshot 1. So the pair most informative
  about instability is precisely the one not re-measured. We state this plainly. We do not gloss
  over it.

## Reproduce

```
python3 submit_repeat.py      # reuses sweep_prereg.json pairs VERBATIM; no re-selection
python3 collect_repeat.py --wait
```
