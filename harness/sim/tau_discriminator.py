"""
tau_discriminator.py — designs a cheap follow-up experiment. This experiment
resolves the zeta alias that the current data cannot fix.

The problem: ΔP = |sin(2π ζ τ)| is periodic. So at the single τ=40 µs that we
used, ζ = 1.62 kHz, ζ = 26.6 kHz, and ζ = 51.6 kHz all predict the SAME ΔP =
0.397. The first two are both physically credible. Sub-kHz to few-kHz is the
expected residual ZZ for a tunable-coupler device like Heron. Tens of kHz is
typical of fixed couplers. So the ambiguity is real, not pedantic. It means
that we cannot currently state the coupling strength, only the observable.

The fix is cheap: it adds ONE extra idle window. This script finds the τ that
best separates the alias branches. It reports the predicted ΔP for each one.
So the follow-up run has a pre-registered discriminating prediction.
"""
import math, json, os, sys

BASE = os.path.dirname(os.path.abspath(__file__)) + "/"
sys.path.insert(0, BASE)
from qpu_sim import run_pair, fit_zz, load_snapshot, TAU  # noqa

MEASURED_DP = 0.397          # ibm_marrakesh pair 0, snapshot 1
aliases = fit_zz(MEASURED_DP, n_aliases=3)

print(f"measured dP={MEASURED_DP} at tau={TAU*1e6:.0f} us is consistent with:")
for n, z in enumerate(aliases):
    print(f"   n={n}:  zeta = {z:9.1f} Hz  ({z/1e3:6.2f} kHz)")

# Scan candidate tau values for maximum spread between alias predictions.
best = None
for tau_us in [t / 2 for t in range(2, 81)]:          # 1 .. 40 us in 0.5 us steps
    tau = tau_us * 1e-6
    preds = [abs(math.sin(2 * math.pi * z * tau)) for z in aliases]
    spread = max(preds) - min(preds)
    if best is None or spread > best[1]:
        best = (tau_us, spread, preds)

tau_us, spread, preds = best
print(f"\nbest discriminating window: tau = {tau_us:.1f} us  (spread {spread:.3f})")
for n, (z, p) in enumerate(zip(aliases, preds)):
    print(f"   if zeta = {z/1e3:6.2f} kHz  ->  predicted dP = {p:.4f}")

print(f"\nsimulated check at tau={tau_us:.1f} us (forward model, each alias injected):")
snap, cal = load_snapshot("mrk_new")
sims = []
for n, z in enumerate(aliases):
    dP, zs = run_pair(z, snap, 98, 91, tau=tau_us * 1e-6, seed=99 + n)
    sims.append(dP)
    print(f"   n={n}  zeta={z/1e3:6.2f} kHz  ->  sim dP={dP:.4f}  z={zs:.1f}")

cost = 8 * 2.70          # 8 circuits (2 secret x 2 reps x 2 distances) at ~2.7 s each
print(f"\nEstimated cost of the follow-up: ~{cost:.0f} QPU-s for one pair at one extra tau.")
print("PRE-REGISTERED DISCRIMINATION: the measured dP at this tau selects the branch;")
print("if it lands between predictions, the static-ZZ model itself is incomplete.")

json.dump(dict(measured_dP=MEASURED_DP, tau_used_s=TAU, aliases_hz=aliases,
               recommended_tau_us=tau_us, predicted_dP_per_alias=preds,
               simulated_dP_per_alias=sims, est_qpu_seconds=cost,
               calibration_snapshot=cal),
          open(BASE + "tau_discriminator.json", "w"), indent=1)
print(f"\nwrote tau_discriminator.json")
