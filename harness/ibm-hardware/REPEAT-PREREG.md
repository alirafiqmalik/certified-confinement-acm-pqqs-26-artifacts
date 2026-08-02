# E1-R — pre-registration of the second-snapshot replication

**Written 2026-07-28 before the jobs returned.** We submitted job IDs `d9k5uljjf64c739hn19g`
(ibm_marrakesh, 40 circuits) and `d9k5um0ii2cc73efn7l0` (ibm_fez, 24 circuits) before we wrote this
file. The analysis rule below is therefore fixed independently of the outcome.

## What is being replicated, and what is deliberately *not* re-done
- The **same 8 victim/probe pairs** from `sweep_prereg.json`, used **verbatim**. `pick_pairs()` is
  **not** re-run. Selecting pairs again from the new calibration picks whichever qubits look best
  today. That is precisely the cherry-picking that the pre-registration exists to exclude.
- Same protocol: Y-basis Ramsey, τ = 40 µs, 8192 shots × 2 reps, `asap` scheduling,
  `initial_layout=[victim, probe]`.
- Same statistic: an unpooled two-proportion Wald z over N = 16384. A **leak** is z ≥ 5.

## Why this counts as a second calibration snapshot
Both devices recalibrated between the two runs, and this is checkable in-artifact rather than by
file timestamps: **all 24 pre-registered qubits report a different readout error** than the value
pinned in `sweep_prereg.json` (for example, q98 on marrakesh: 0.0017 → 0.0083, about 5× worse).
Backend `last_update_date` at submission: marrakesh **2026-07-28 02:44 EDT**, fez **03:37 EDT**.
`repeat_jobs.json` stores the full live snapshot (readout error + T2 per qubit), which the first
sweep did **not** record — this run fixes that provenance weakness for itself.

## Outcome rules, fixed in advance
| Outcome | What we will write |
|---|---|
| **Leak at d=1 reproduces on most pairs, no leak at d≥2 on any pair** | §9 ¶4 hedge narrows from "single calibration snapshot" to "two independent calibration snapshots". k=1 sufficiency now rests on 16 pair-observations rather than 8. |
| **Some pairs flip d=1 leak status** | Reported per-pair, in a flip table, not averaged away. A pair that leaks in one snapshot and not the other *strengthens* the case for a structural certificate, which is placement-based, over a magnitude-based one. We will say so. We will also report it as instability. |
| **Any pair leaks at d ≥ 2** | This **breaks** the k=1 sufficiency claim. We will report it prominently, raise the recommended default to k=2, and rewrite §7.7's "k=1 is the principled minimum". `bufferK` already supports this with no new soundness proof — that is the design property being tested. |
| **Jobs fail / quota exhausted** | Reported as not-run. No number from snapshot 1 will be re-labelled as a replication. |

## Honest limit of what a positive result buys
Both snapshots fall on the **same calendar day**, about 1 to 3 hours apart, and they span at
least one recalibration on each device. A positive result therefore removes the
*single-calibration-snapshot* hedge. It does **not** establish multi-day or cross-generation
stability. §9 will say "two
independent calibration snapshots on one day", not "reproducible over time".

## Budget
Rolling 28-day free-tier window: 270 s consumed of 600 s, with **330 s remaining** at
submission. Snapshot 1 cost 153.8 s, being 106.9 s on marrakesh and 46.9 s on fez. This run is
the same size.
