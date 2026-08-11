# Live IBM QPU results — tenant-isolation leak on real Heron r2 (2026-07-28)

**This is the headline empirical result of the paper (§7.6).** On a real IBM Heron r2 device, a
co-tenant placed on a qubit *adjacent* to a victim reads the secret qubit state of that victim. The
swing in its own measurement is 38 percentage points. The channel disappears completely at graph
distance 2 or more. Our confinement certificate, under the neighbor-buffered policy `bufferF`,
rejects exactly the adjacent placements that leak.

- **Device:** `ibm_marrakesh` (IBM Heron r2, 156 qubits), open/free plan.
- **Date:** 2026-07-28. `submit_ibm.py` writes the run record to `ibm_job.json`. That file is a
  by-product of a submission, so this repository does not ship it. `provenance.json` holds the
  job records that we recovered from the IBM job history instead, and `PROVENANCE.md` explains
  the recovery.
- **Victim:** physical qubit **q98** (T2≈84 µs, readout err 0.0017).
- **Probes (co-tenant):** q91 (d=1), q112 (d=2), q109 (d=3), q6 (d=18, "far"), all selected by
  best readout error at their graph distance.
- **Protocol.** The probe runs a **Y-basis Ramsey**, that is,
  `H · delay(40µs) · S† · H · measure`. The Y-basis choice is necessary. A plain Ramsey is blind,
  because `sin²(θ/2)` is even in the ZZ phase. The victim encodes a secret bit in its qubit state.
  The analysis takes ΔP(probe=1) between the two victim states, with a two-proportion z-test over
  2×8192 shots.
- **Cost:** primary job 43 s + control job 63 s = **106 s QPU** total (≪ the 10-min/month cap).
- **Jobs:** primary `d9k1gu3jf64c739hh0p0`, control `d9k1i90ii2cc73efhco0`.

## Result 1 — the leak is sharply adjacency-gated
Victim driven-to-|1⟩ vs idle-|0⟩, probe reads its own qubit:

| distance | probe | P1(secret=0) | P1(secret=1) | **ΔP** | **z** | verdict |
|---|---|---|---|---|---|---|
| **d=1** | q91 | 0.892 | 0.495 | **0.397** | **86.4** | **LEAK** |
| d=2 | q112 | 0.237 | 0.235 | 0.002 | 0.44 | no signal |
| d=3 | q109 | 0.317 | 0.315 | 0.002 | 0.29 | no signal |
| far | q6 | 0.837 | 0.840 | 0.003 | 0.77 | no signal |

A co-tenant one hop away recovers the secret bit of the victim almost perfectly. Two hops away,
the co-tenant detects nothing above the noise floor.

## Result 2 — mechanism control: it is static ZZ (state leakage), not drive activity
We ruled out that the signal came only from the victim's *drive activity*. We separated the
victim's **final state** from its **activity** (a driven-but-returns-to-|0⟩ arm has the same final
state as idle):

| distance | idle |0⟩ | static |1⟩ | driven→|0⟩ | **static-ZZ ΔP (z)** | **pure-drive ΔP (z)** |
|---|---|---|---|---|---|---|
| **d=1** | 0.886 | 0.506 | 0.880 | **0.380 (82.1)** | 0.006 (1.6) |
| d=2 | 0.254 | 0.260 | 0.256 | 0.006 (1.3) | 0.002 (0.4) |
| d=3 | 0.310 | 0.306 | 0.307 | 0.004 (0.7) | 0.003 (0.5) |
| far | 0.855 | 0.852 | 0.857 | 0.003 (0.7) | 0.002 (0.6) |

- **The channel is always-on ZZ coupling, and the STATE of the victim leaks.** For |1⟩ against |0⟩,
  ΔP=0.38 and z=82.
- **Activity alone does not leak.** A drive that returns to |0⟩ gives ΔP=0.006 and z=1.6, so there
  is no signal.
- Both mechanisms are **strictly nearest-neighbor** (nothing at d≥2).
- **The tunable couplers of Heron r2 do NOT null this ZZ channel** for this pair. That directly
  refutes the pre-registered concern that the demo can see nothing on a tunable-coupler device.

## Correspondence with the certifier (the bridge)
ZZ coupling is a property of a **coupling edge**. Our confinement predicate under `bufferF`
(`QpuCompiler/Buffer.lean`, kernel-checked) forbids the victim from sharing an edge with the
forbidden co-tenant region. It therefore rejects exactly the `d=1` placement that leaks, and it
accepts `d≥2`:
- `certifySecurity heronPatch patchF vAdj` → accepted **true** ← support-only misses adjacency (the gap)
- `certifySecurity heronPatch (bufferF …) vAdj` → accepted **false** ← rejects the leaking placement
- `certifySecurity heronPatch (bufferF …) vFar` → accepted **true** ← no over-blocking

**The certifier's accept/reject boundary coincides with the measured physical leak boundary.**
A device-specific Lean patch encodes the real `ibm_marrakesh` neighborhood of q98 and makes this
exact. Read `HeronMarrakesh.lean`.

## Honest scope
- **What we show:** a real, strong, nearest-neighbor ZZ **state-confidentiality** leak on a
  current IBM device, and that the buffered certificate's structural verdict matches it.
- **What we do NOT claim:**
  1. That this generalizes to every qubit pair and every device. This is a single victim and a
     single calibration snapshot, so reproducibility across pairs and days is future work.
  2. That the certificate *bounds crosstalk magnitude*. It certifies the structural precondition,
     namely no shared edge, and the hardware shows that removing that edge removes the measurable
     channel.
  3. Drive-only activity leakage. That sits below our sensitivity here, and we do not exclude it in
     general.
- **Emulated co-tenancy:** IBM is single-tenant, so victim+probe share one job on disjoint qubits,
  per the NDSS'25 / SWAP'25 methodology. The certificate's guarantee is layout-structural and
  independent of whether co-tenancy is real or emulated.

## Reproduce
`submit_ibm.py` builds and submits the primary job, and `submit_control.py` does the same for the
control. `wait_ibm.py` and `wait_ctrl.py` poll and analyze. The raw verdicts are in
`ibm_results.json` and `ibm_ctrl_results.json`. You need an IBM token in `apikey.json`, which we do
not commit.

`bash run_artifact.sh --submit-qpu` runs this sequence for you. It costs metered QPU time.

To audit these numbers **without** a QPU and **without** an account, run
`python3 harness/ibm-hardware/reconcile_provenance.py`. It recomputes every published cell from
the raw bitstring counts in `provenance.json`.
