# Hardware reproducibility sweep — paper question E4 (RESULTS, 2026-07-28)

This upgrades the E4 hardware evidence from a single pair (n=1) to eight pairs (n=8). Each triple is a victim, a d=1
probe, and a d=2 control, across **two IBM Heron r2 devices**. It tests one *prediction*: that the
leak is strictly nearest-neighbor, present at d=1 and null at d≥2. We fixed k=1 on 2026-07-23,
before any sweep data existed. That prediction is exactly the condition the `bufferF` certificate
enforces at k=1.

- **Devices:** `ibm_marrakesh` (5 pairs) + `ibm_fez` (3 pairs). **Both `processor_type =
  {family: Heron, revision: 2}`** — same generation, which we confirmed from backend properties.

- **Protocol, identical to IBM-RESULTS.md.** The victim is `|0⟩` or `|1⟩`. The probe runs
  `H·delay(40µs)·S†·H·measure`, in the Y basis. ΔP is |P1(|1⟩)−P1(|0⟩)|. The statistic is a
  two-proportion z over 2×8192 shots.

- **Pre-registration.** We chose the pairs from calibration. We took the best readout and kept
  them disjoint, and we wrote them to `sweep_prereg.json` before any result arrived. **Cost: 164
  QPU-s** (103 marrakesh + 61 fez). Cycle total 106+164 = **270 s ≈ 4.5 min ≤ 10 min/month**. Jobs
  `d9k297jjf64c739hhu70`, `d9k2983jf64c739hhu80`.

## Result — the prediction holds on 7 of 8 pairs, and the NN assumption holds on 8 of 8

| device | pair | d=1 ΔP (z) | d=2 ΔP (z) | prediction |
|---|---|---|---|---|
| marrakesh | 0 | **0.366 (77.0)** | 0.001 (0.3) | HOLDS |
| marrakesh | 1 | **0.241 (46.9)** | 0.003 (0.6) | HOLDS |
| marrakesh | 2 | **0.051 (9.5)** | 0.004 (0.8) | HOLDS |
| marrakesh | 3 | **0.300 (59.5)** | 0.001 (0.2) | HOLDS |
| marrakesh | 4 | **0.265 (57.1)** | 0.005 (1.0) | HOLDS |
| fez | 0 | 0.000 (0.0) | 0.007 (1.8) | — (no d1 leak) |
| fez | 1 | **0.173 (33.2)** | 0.002 (0.4) | HOLDS |
| fez | 2 | **0.197 (41.7)** | 0.002 (0.4) | HOLDS |

- **The d=1 leak reproduces on 7 of 8 pairs**, with z from 9.5 to 77. The magnitude varies with
  the physical ZZ of the pair. That gives ΔP from 0.05 to 0.37. This is a *class* of leaks. It is
  not a single anecdote.

- **No pair leaked at d=2** (all z<2). The nearest-neighbor assumption — and therefore the
  sufficiency of a **k=1** buffer — holds on **8/8** pairs. This is the key sweep finding.

- **fez pair 0 showed no detectable d=1 leak** (ΔP=0.0002, z=0.0). We report it plainly. We do not
  drop it. The validator still **REJECTS** this placement, structurally, on the coupling edge. The
  result is *conservatively safe*, because the validator never *accepts* a leaking placement.

## Validator–hardware agreement (the honest framing)
The verdict of the validator is **structural**: it rejects exactly when the victim shares a
coupling edge with the co-tenant. Under `bufferF` it therefore **REJECTS all 8** d=1 placements
and **ACCEPTS all 8** d=2 placements. Against the physics:

- **Soundness (the safety-critical direction): 8/8** — the validator never accepted a placement
  that leaked. No false-accepts.

- **Necessity (did the guarded-against leak actually occur): 7/8** at d=1 — on 1 pair the rejected
  placement happened not to leak (conservative over-block, harmless).

- **NN / k=1 validity: 8/8** — no d≥2 leak anywhere, so k=1 is never insufficient on this sample.

**Wording used in the paper:** "across 8 qubit pairs on 2 Heron r2 device instances,
**single calibration snapshot**." Do **not** claim generalization across time (no second-day run —
out of budget). Phrase the agreement as the counts above. Reserve "coincides" for the sound
direction alone, at 8 of 8. Do not make it a blanket claim.

Raw: `sweep_results.json` and `sweep_prereg.json`. `submit_sweep.py` also writes a
`sweep_jobs.json` label map, which is a by-product of a submission, so we do not ship it.
`provenance.json` carries the raw per-circuit counts instead, and
`reconcile_provenance.py` recomputes every cell above from them without an account.
