"""
qpu_sim.py — FORWARD MODEL of the measured nearest-neighbor ZZ leak.

================================ READ THIS FIRST ================================
This simulation does **not prove that the leak exists**. IBM's fake and noise
backends contain **no crosstalk term at all**. A leak can appear here only
because we add it ourselves.

This file does the opposite of validation. It treats the leak as a *hypothesis*:
an always-on residual ZZ coupling between coupled qubits. It encodes this
hypothesis explicitly. Then it checks whether the hypothesis reproduces the
numbers that we measured on hardware.

Legitimate uses (all offline, none costs QPU time):
  1. Run a regression test on the whole analysis pipeline, end to end, without
     spending quota.
  2. Check that the measured ΔP values match a *physically plausible*
     residual-ZZ strength for Heron r2, and do not need an implausible one.
  3. Catch protocol bugs before they reach hardware. This is how we first
     found the Y-basis readout requirement. A plain H…H Ramsey measures
     sin²(θ/2), which is even in θ. So it cannot detect a sign-flip secret.

Illegitimate use, explicitly out of scope: do not present simulated ΔP as
independent confirmation of the hardware result. All empirical claims in the
paper rest on the hardware runs.
=================================================================================

## Physics encoded

A static, always-on ZZ coupling of strength ζ (Hz), between victim v and probe p,
generates H_ZZ = π ζ (Z_v ⊗ Z_p). Over an idle window τ, the probe accumulates a
phase. The SIGN of this phase depends on the victim's state. This is exactly an
RZZ rotation:

    θ = 2π ζ τ            and the circuit gets   RZZ(θ) on (v, p)

Read out in the Y basis (`sdg` then `h`), the probe's excited-state probability is
    P(1 | victim=b) = (1 ∓ sin θ)/2
So the observable separation between victim=0 and victim=1 is

    ΔP = |sin θ|          (LINEAR in the phase near θ=0)

A plain H…H Ramsey instead gives sin²(θ/2), which is EVEN in θ. Both victim
states give the same answer. So the channel stays invisible. `--basis plain`
reproduces this failure mode on purpose, as a regression test.

Decoherence, gate error, and readout error come from the **real stored
calibration snapshot** of the device: per-qubit T1/T2 and measurement error.
These values do not come from guesses.

## Inverting a measurement (and its honest ambiguity)

Given a measured ΔP: θ = arcsin(ΔP), and ζ = θ / (2π τ).
**This is degenerate.** θ and θ + 2πn give the same |sin θ|. So a single τ cannot
fix ζ uniquely. All values ζ_n = (arcsin(ΔP) + 2πn)/(2πτ) fit equally well.

Resolving this ambiguity needs a sweep over τ. `fit_zz()` returns the n=0 branch
and the first few aliases. This keeps the ambiguity visible, and does not hide it.
"""
import json, math, argparse, os

BASE = os.path.dirname(os.path.abspath(__file__)) + "/"
HW = os.path.abspath(BASE + "../ibm-hardware") + "/"

from qiskit import QuantumCircuit, transpile
from qiskit_aer import AerSimulator
from qiskit_aer.noise import NoiseModel, thermal_relaxation_error, ReadoutError

TAU = 40e-6          # Idle window used on hardware.
SHOTS = 8192
REPS = 2


# ----------------------------------------------------------------- calibration
def load_snapshot(tag):
    """This is the per-qubit {rerr, t2} data. We recorded it at submission time, on real hardware."""
    for fn, key in ((f"results_{tag}.json", "calibration_snapshot"),
                    (f"jobs_{tag}.json", "calibration_snapshot")):
        path = HW + fn
        if not os.path.exists(path):
            continue
        d = json.load(open(path))
        if key and key in d:
            return d[key], d.get("last_calibration")
    path = HW + "repeat_results.json"             # The second-snapshot replication run.
    if os.path.exists(path):
        d = json.load(open(path))
        for dev in d.get("calibration", {}).values():
            if dev.get("snapshot"):
                return dev["snapshot"], dev.get("last_calibration")
    raise SystemExit(f"no calibration snapshot found for tag={tag}")


def build_noise(snapshot, victim, probe, t1_over_t2=1.0):
    """This builds the Aer noise model from the REAL snapshot. It adds thermal
    relaxation on the idle delay, and measurement error. It does NOT add
    crosstalk or a ZZ term, because Aer has none. This is why the script
    injects the ZZ term into the circuit instead."""
    nm = NoiseModel()
    qmap = {victim: 0, probe: 1}                 # Maps a physical qubit index to a simulated qubit index.
    for phys, sim_i in qmap.items():
        info = snapshot.get(str(phys))
        if not info:
            continue
        t2 = info.get("t2") or 200e-6
        t1 = max(t2 * t1_over_t2, t2 / 2 + 1e-9)  # T2 <= 2*T1 must hold
        nm.add_quantum_error(
            thermal_relaxation_error(t1, t2, TAU), "delay", [sim_i])
        re = info.get("rerr")
        if re:
            nm.add_readout_error(ReadoutError([[1 - re, re], [re, 1 - re]]), [sim_i])
    return nm


# ----------------------------------------------------------------- the circuit
def make_circuit(secret_bit, zeta, tau=TAU, basis="y"):
    """The victim holds the secret in its STATE. The probe performs a Ramsey.

    Qubit 0 is the victim. Qubit 1 is the probe. RZZ(2*pi*zeta*tau) is the
    injected always-on ZZ. `basis='plain'` swaps the Y-basis readout for a
    plain H. This reproduces the sin^2(theta/2) blindness on purpose.
    """
    theta = 2 * math.pi * zeta * tau
    qc = QuantumCircuit(2, 1)
    if secret_bit:
        qc.x(0)
    qc.h(1)
    qc.barrier()
    qc.delay(tau, 0, unit="s")
    qc.delay(tau, 1, unit="s")
    if zeta != 0.0:
        qc.rzz(theta, 0, 1)          # The leak, injected explicitly.
    qc.barrier()
    if basis == "y":
        qc.sdg(1)
    qc.h(1)
    qc.measure(1, 0)
    return qc


# ----------------------------------------------------------------- run + stats
def p1_of(counts):
    tot = sum(counts.values())
    return counts.get("1", 0) / tot if tot else 0.0


def two_proportion_z(a, b, n):
    """This is the unpooled two-proportion (Wald) z, identical to the hardware collectors."""
    se = math.sqrt(a * (1 - a) / n + b * (1 - b) / n)
    d = abs(b - a)
    return d, (d / se if se > 0 else 0.0)


def run_pair(zeta, snapshot=None, victim=None, probe=None, tau=TAU,
             basis="y", shots=SHOTS, reps=REPS, seed=1234):
    """Returns (dP, z). This mirrors the hardware protocol exactly: two secret
    conditions times reps, Y-basis readout, and an unpooled two-proportion z."""
    nm = build_noise(snapshot, victim, probe) if snapshot else None
    sim = AerSimulator(noise_model=nm, seed_simulator=seed)
    got = {}
    for bit in (0, 1):
        acc = []
        for r in range(reps):
            qc = make_circuit(bit, zeta, tau=tau, basis=basis)
            tqc = transpile(qc, sim, optimization_level=0)
            res = sim.run(tqc, shots=shots, seed_simulator=seed + 17 * r + bit).result()
            acc.append(p1_of(res.get_counts()))
        got[bit] = sum(acc) / len(acc)
    return two_proportion_z(got[0], got[1], shots * reps)


# ----------------------------------------------------------------- inversion
def fit_zz(dP, tau=TAU, n_aliases=3):
    """Inverts ΔP = |sin θ| for ζ. Returns the n=0 branch plus aliases, because a
    single τ cannot distinguish between them."""
    dP = min(max(dP, 0.0), 0.999999)
    theta0 = math.asin(dP)
    return [(theta0 + 2 * math.pi * n) / (2 * math.pi * tau) for n in range(n_aliases)]


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeta", type=float, default=1626.0, help="ZZ strength in Hz")
    ap.add_argument("--tau", type=float, default=TAU)
    ap.add_argument("--basis", choices=["y", "plain"], default="y")
    ap.add_argument("--victim", type=int, default=98)
    ap.add_argument("--probe", type=int, default=91)
    a = ap.parse_args()
    snap, cal = load_snapshot("mrk_new")
    dP, z = run_pair(a.zeta, snap, a.victim, a.probe, tau=a.tau, basis=a.basis)
    print(f"calibration snapshot: {cal}")
    print(f"zeta={a.zeta:.1f} Hz  tau={a.tau*1e6:.0f} us  basis={a.basis}")
    print(f"  theta = {2*math.pi*a.zeta*a.tau:.4f} rad   predicted |sin| = {abs(math.sin(2*math.pi*a.zeta*a.tau)):.4f}")
    print(f"  simulated dP = {dP:.4f}   z = {z:.1f}")
