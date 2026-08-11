# QPU simulation — forward model of the measured ZZ leak (RESULTS)

## What this is, and what it is not

**It is not validation.** Aer and IBM's fake backends contain **no crosstalk term at all**. So a
leak cannot appear here unless we put it there. This harness takes the leak as a *hypothesis* —
always-on residual ZZ between coupled qubits — and encodes the hypothesis explicitly as an `RZZ`
rotation. It asks whether that hypothesis reproduces what we measured. Every empirical claim in
the paper still rests on the hardware runs.

**It is useful for three things**, all offline and all costing zero QPU time:
1. **Regression-testing the whole pipeline** before spending metered quota.
2. **Checking the measured ΔP are consistent with a physically plausible coupling** rather than one
   that requires implausible hardware.
3. **Catching protocol bugs pre-flight** — this is how we originally found the Y-basis requirement.

## Physics encoded

A static ZZ of strength ζ gives `H = π ζ (Z⊗Z)`. Over an idle window τ, the probe accumulates a
phase whose **sign depends on the victim's state** — exactly `RZZ(θ)` with `θ = 2π ζ τ`. Read out in
the Y basis (`sdg; h`):

```
P(1 | victim=b) = (1 ∓ sin θ)/2      ⇒      ΔP = |sin θ|      (linear near θ=0)
```

A plain H…H Ramsey instead gives `sin²(θ/2)`, which is **even** in θ. Both secret values give the
same answer, so the channel is invisible. Decoherence and readout error come from the **real
stored calibration snapshot** (`2026-07-29 07:22 EDT`), not from guesses.

## End-to-end test suite — 9/9 passing

| test | purpose | result |
|---|---|---|
| **T1** | positive control: injected leak detected | ΔP=0.3858, z=75.7 |
| **T2** | negative control: no coupling ⇒ no detection | ΔP=0.0123, z=2.2 (< 5) |
| **T3** | closure: measured ΔP → fitted ζ → simulated ΔP | worst error **0.0101** over 13 pairs |
| **T4** | Y-basis necessity | Y: z=75.7 · plain: **z=0.9 (blind)** |
| **T5** | response curve tracks \|sin(2πζτ)\| | 5/5 points within 0.03 |
| **T6** | alias honesty | ζ ∈ {1.6, 26.6, 51.6} kHz all give ΔP=0.397 |
| **T7** | plausibility of fitted ζ | **219–1666 Hz** across 13 pairs |
| **T8** | kernel-checked certifier verdicts on the real patch | support-only ACCEPTS d=1. `bufferF` REJECTS it. Distant region still accepted |
| **T9** | **blind** structural prediction vs held-out hardware | **0 missed leaks in 46 observations** (see `BLIND-EMULATION.md`) |

Reproduce: `python test_e2e.py` (exits non-zero on any failure, so it works as a pre-flight gate).

### T3 per-pair closure
Every one of the 13 distinct hardware pairs, inverted to a ζ and re-simulated, returns its own
measured ΔP to within **0.0101** overall. This includes the weakest pair (ΔP=0.055) and the
strongest (0.407).
A single-parameter static-ZZ model therefore accounts for the full ≈8× spread of measured effects
with no per-pair fudging beyond that one coupling constant. **This is self-consistency of a forward
model, not independent evidence.**

### T7 — the substantive consistency result
Fitted couplings on the n=0 branch span **0.22–1.67 kHz**. That is squarely the regime expected
for *residual* ZZ on a tunable-coupler device. Heron's couplers are designed to suppress ZZ, and
sub-kHz to low-kHz residuals are what survives. The measured ΔP therefore do **not** require an
implausible coupling. This is a real, if modest, argument that the static-ZZ mechanism is the
right one. It is independent of the mechanism-control run that ruled out drive-activity leakage.

## NEW LIMITATION this work uncovered

**We cannot state the coupling strength from the existing data.** `ΔP = |sin(2πζτ)|` is periodic. So,
at the single τ=40 µs used throughout, ζ = 1.62 kHz, 26.62 kHz and 51.62 kHz are *all* exact fits.
The ambiguity is not pedantic. ~1.6 kHz is the plausible tunable-coupler residual. ~26.6 kHz is
typical of *fixed*-coupler devices instead, and the two imply different physics. The paper reports
ΔP (an observable) and never quotes a ζ, so nothing published is wrong. But any future claim about
coupling *magnitude* is unsupported without the extra measurement below.

This does not touch the security argument at all. The certificate is structural (no shared coupling
edge) and never references the ζ value. In fact, it reinforces why a magnitude-based policy is the
wrong instrument: we cannot even pin the magnitude with the data we have.

## Designed follow-up: one extra idle window resolves it

`tau_discriminator.py` scans for the τ that maximally separates the alias branches:

**τ = 29 µs**, where the branches predict wildly different observables:

| ζ | predicted ΔP | simulated ΔP |
|---|---|---|
| 1.62 kHz | 0.2917 | 0.2852 (z=53.9) |
| 26.62 kHz | 0.9904 | 0.9910 (z=1342) |
| 51.62 kHz | 0.0182 | 0.0223 (z=4.0) |

**Cost: ~22 QPU-s for one pair.** We pre-register the prediction here, before the run: the measured
ΔP at τ=29 µs selects the branch outright. If it lands *between* the predictions, the static-ZZ model
is itself incomplete. That is the more interesting outcome. We state the prediction in advance, so
that no one can explain it away after the fact.

## Files

| file | role |
|---|---|
| `qpu_sim.py` | forward model: real calibration snapshot + explicitly injected `RZZ` ZZ term |
| `test_e2e.py` | the 8-test end-to-end suite (offline pre-flight gate) |
| `tau_discriminator.py` | designs the alias-resolving follow-up |
| `blind_predict.py` / `blind_score.py` | the **non-circular** counterpart — see `BLIND-EMULATION.md` |
| `public_meta_ibm_marrakesh.json` | captured public device metadata (no measurements) |
| `test_results.json`, `tau_discriminator.json` | machine-readable outputs |

Environment: qiskit 2.5.1, qiskit-aer 0.17.2, python 3.11 in an isolated venv (qiskit is **not**
installed system-wide on this machine).
