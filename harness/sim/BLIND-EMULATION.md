# Blind hardware emulation — can we predict leaks *without* knowing the results?

## The question

The forward model (`qpu_sim.py`, `RESULTS-SIM.md`) is circular: measured ΔP → fit ζ → inject ζ →
reproduce ΔP. Can we instead predict leaks from device data alone, with no knowledge of the outcome?

## The answer, in two halves

| | predictable blind? | why |
|---|---|---|
| **WHICH placements leak** (structure) | **YES — exactly** | the coupling map is published in full (352 edges for `ibm_marrakesh`) |
| **HOW MUCH they leak** (magnitude ζ) | **NO — not even in principle from public data** | ζ = f(J, Δ, α), and IBM publishes none of J, qubit frequency, or anharmonicity. A tunable coupler adds an unpublished bias point |

### What IBM actually publishes for Heron r2
Verified against the live API, not assumed:

- **Available:** coupling map, T1, T2, readout error, CZ duration, CZ error.
- **Not available:** `qubit_properties[q].frequency` returns **`None`**. Anharmonicity is not exposed
  (`BackendPropertyError`). Coupling strength *J* is not published. Tunable-coupler bias is not
  published. CZ duration takes only **two** distinct values device-wide (68 ns / 80 ns), so it
  carries no usable per-edge information either.

The static-ZZ rate for coupled transmons depends on exactly the withheld quantities. On a
tunable-coupler device the *residual* ZZ also depends on how precisely the coupler was biased to
null it. This calibration detail is not merely unpublished but device- and session-specific.
**Magnitude is therefore not determined by public data.** This is a property of the platform. No
amount of effort changes it.

## What we built and how blindness is enforced

`blind_predict.py` reads **only** public metadata (`public_meta_ibm_marrakesh.json`, captured with
zero QPU time and containing no measurements). The script enforces blindness *mechanically*, not
just by promise. It replaces `builtins.open` with a guard that raises `PermissionError` on any path
matching `results_*`, `sweep_results`, `repeat_results`, `ibm_results`, `RESULTS-*`, and more. It
cannot read our outcomes even by accident.

**The prediction rule:** a probe leaks iff it sits at **graph distance 1** from the victim. This
follows from the documented mechanism (always-on residual ZZ acts across a coupling edge). We
committed it in `QpuCompiler/Buffer.lean` on **2026-07-23** — five days *before* the first hardware
run on 2026-07-28 began. The derivation order is checkable from the repository, which is what makes
"blind" a claim about provenance rather than about one script's file handles.

Scoring lives in a **separate** file (`blind_score.py`), which can read both. Nothing feeds back, so
running the scorer cannot alter a prediction.

## Result — 46 held-out observations

| | count | meaning |
|---|---|---|
| true positive | **22** | predicted leak, leaked |
| true negative | **23** | predicted no leak, none detected |
| false positive | **1** | predicted leak, none detected — *conservative over-block* |
| **FALSE NEGATIVE** | **0** | predicted safe but leaked — **the unsafe direction** |

- **Overall agreement: 45/46 = 97.8%**
- **d=1 recall: 22/23** · **d≥2 null accuracy: 23/23**
- **SAFETY-CRITICAL DIRECTION: PASS — zero missed leaks across all 46 observations.**

### The single false positive is not a prediction error

It is `ibm_fez` 50→51 in snapshot 1 (z=0.0). The *same pair, same qubits* leaked at **z=22.4** in
snapshot 2, so the blind structural prediction was correct. The snapshot-1 *measurement* was
below detection at that calibration. Counted as a false positive because that is what the data said
at the time. The follow-up shows the predictor was right, and the observation was blind.

This best illustrates the paper's design choice: a policy built on *measured magnitude* whitelists
that placement — and is wrong within a day. A policy built on *published structure* flagged it
correctly both times, before and after the channel became visible.

## What this does and does not license

**Does:** a tenant can identify every at-risk placement on an IBM device **before running anything**,
from public metadata alone. The rule that does it is the same rule the Lean certificate enforces.
That is the practically important claim — it means the certifier's input requires no privileged data.

**Does not:** predict leak strength, guarantee the NN rule holds on other hardware families, or
substitute for the hardware measurements. Non-graph-mediated channels (shared readout resonators,
control-line crosstalk) are not caught by *any* coupling-map-derived rule at any radius — as
§9 already discloses.

## Reproduce

```
python blind_predict.py     # public metadata only; guard active; writes blind_predictions.json
python blind_score.py       # scores vs held-out hardware; exits non-zero on any missed leak
```

| file | role |
|---|---|
| `public_meta_ibm_marrakesh.json` | captured public metadata (no measurements, no QPU time) |
| `blind_predict.py` | blind structural predictor, `open()` guard enforcing blindness |
| `blind_score.py` | held-out scorer, separate by design |
| `blind_predictions.json`, `blind_score.json` | outputs |
