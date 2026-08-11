"""
test_e2e.py — end-to-end test suite for the leak-measurement harness.

This suite runs entirely offline. If any test fails, the suite exits non-zero.
You can use it as a pre-flight gate before spending QPU time.

WHAT EACH TEST IS FOR (and what it is NOT)
  T1 positive control   the pipeline detects an injected leak
  T2 negative control   the pipeline reports NO leak when there is none
  T3 closure            a measured ΔP produces a fitted ζ, which produces a
                        simulated ΔP that reproduces the measured ΔP
                        *** This is self-consistency of a forward model, NOT independent
                            confirmation of the hardware result. ***
  T4 Y-basis necessity  a plain H…H Ramsey is blind (the real bug this harness once had)
  T5 response curve     ΔP tracks |sin(2πζτ)| across a ζ sweep
  T6 alias honesty      a single τ cannot pin ζ. This script reports aliases,
                        and does not hide them
  T7 plausibility       the fitted ζ values sit in a physically sane residual-ZZ
                        band for Heron r2
  T8 validator          Lean verdicts on the REAL device patch: the buffered policy
                        rejects the adjacent placement, and accepts the distant one
  T9 blind prediction   the NON-circular test. It predicts which placements leak,
                        from PUBLIC metadata only (the coupling map). It scores the
                        prediction against held-out hardware. It fails if any
                        placement predicted safe actually leaked.
"""
import json, math, os, subprocess, sys, tempfile

BASE = os.path.dirname(os.path.abspath(__file__)) + "/"
HW = os.path.abspath(BASE + "../ibm-hardware") + "/"
ROOT = os.path.abspath(BASE + "../..") + "/"      # Artifact/ (holds lakefile.toml)

sys.path.insert(0, BASE)
from qpu_sim import run_pair, fit_zz, load_snapshot, TAU, two_proportion_z  # noqa

LEAK_Z = 5.0
results = []


def check(name, ok, detail):
    results.append((name, ok, detail))
    print(("  PASS  " if ok else "  FAIL  ") + name + " :: " + detail, flush=True)
    return ok


def measured_pairs():
    """These are the 13 DISTINCT hardware pairs: 8 from the snapshot-2 replication, and 5 new."""
    out = []
    rr = json.load(open(HW + "repeat_results.json"))
    for p in rr["pairs"]:
        out.append(dict(src="snap2", device=p["device"], pair=p["pair"],
                        dP=p["d1"]["dP"], z=p["d1"]["z"],
                        dP2=p["d2"]["dP"], z2=p["d2"]["z"]))
    mn = json.load(open(HW + "results_mrk_new.json"))
    for p in mn["pairs"]:
        out.append(dict(src="new", device=mn["backend"], pair=p["pair"],
                        victim=p["victim"], dP=p["d1"]["dP"], z=p["d1"]["z"],
                        dP2=p["d2"]["dP"], z2=p["d2"]["z"]))
    return out


snap, cal = load_snapshot("mrk_new")
print(f"calibration snapshot in use: {cal}\n")

# ---------------------------------------------------------------- T1 / T2
print("T1 positive control — injected leak must be detected")
dP, z = run_pair(1626.0, snap, 98, 91)
check("T1 injected leak detected", z >= LEAK_Z, f"dP={dP:.4f} z={z:.1f} (need z>={LEAK_Z})")

print("\nT2 negative control — no coupling must give no detection")
dP0, z0 = run_pair(0.0, snap, 98, 112)
check("T2 zero coupling -> null", z0 < LEAK_Z, f"dP={dP0:.4f} z={z0:.1f} (need z<{LEAK_Z})")

# ---------------------------------------------------------------- T3 closure
print("\nT3 closure — measured dP -> fitted zeta -> simulated dP  (forward-model self-consistency)")
rows = measured_pairs()
worst = 0.0
for m in rows:
    zeta = fit_zz(m["dP"])[0]
    sdP, sz = run_pair(zeta, snap, 98, 91, seed=4242 + m["pair"])
    err = abs(sdP - m["dP"])
    worst = max(worst, err)
    tag = f"{m['src']}/{m['device'][4:]}/p{m['pair']}"
    print(f"    {tag:<22} measured dP={m['dP']:.4f}  fitted zeta={zeta:8.1f} Hz  "
          f"sim dP={sdP:.4f}  |err|={err:.4f}")
check("T3 closure within 0.02 for every pair", worst <= 0.02,
      f"worst |sim-measured| = {worst:.4f} across {len(rows)} pairs")

# ---------------------------------------------------------------- T4 Y-basis
print("\nT4 Y-basis necessity — plain Ramsey must be BLIND at the same coupling")
dPy, zy = run_pair(1626.0, snap, 98, 91, basis="y")
dPp, zp = run_pair(1626.0, snap, 98, 91, basis="plain")
check("T4 plain basis blind, Y basis sees it", zy >= LEAK_Z and zp < LEAK_Z,
      f"Y: dP={dPy:.4f} z={zy:.1f}  |  plain: dP={dPp:.4f} z={zp:.1f}")

# ---------------------------------------------------------------- T5 response
print("\nT5 response curve — dP must track |sin(2*pi*zeta*tau)|")
bad = []
for zeta in (200.0, 800.0, 1626.0, 3000.0, 6250.0):
    pred = abs(math.sin(2 * math.pi * zeta * TAU))
    got, _ = run_pair(zeta, snap, 98, 91, seed=777)
    print(f"    zeta={zeta:7.1f} Hz  predicted={pred:.4f}  simulated={got:.4f}")
    if abs(got - pred) > 0.03:
        bad.append((zeta, pred, got))
check("T5 dP follows |sin| across sweep", not bad,
      "all 5 points within 0.03" if not bad else f"deviations: {bad}")

# ---------------------------------------------------------------- T6 aliasing
print("\nT6 alias honesty — one tau cannot pin zeta")
al = fit_zz(0.397)
same = all(abs(abs(math.sin(2 * math.pi * a * TAU)) - 0.397) < 1e-6 for a in al)
check("T6 aliases all reproduce the same dP", same,
      "zeta in {" + ", ".join(f"{a:.0f}" for a in al) + "} Hz all give dP=0.397 "
      "-> tau-sweep required to disambiguate (documented limitation)")

# ---------------------------------------------------------------- T7 plausibility
print("\nT7 plausibility — fitted zeta (n=0 branch) should be a sane residual ZZ")
z0s = [fit_zz(m["dP"])[0] for m in rows]
lo, hi = min(z0s), max(z0s)
check("T7 fitted zeta within 0.1-100 kHz", 100.0 <= lo and hi <= 100_000.0,
      f"range {lo:.0f}-{hi:.0f} Hz ({lo/1e3:.2f}-{hi/1e3:.2f} kHz) over {len(z0s)} pairs")

# ---------------------------------------------------------------- T8 validator
print("\nT8 validator — Lean verdicts on the real ibm_marrakesh patch")
lean = r"""
import QpuCompiler.HeronMarrakesh
import QpuCompiler.Buffer
open QpuCompiler
-- support-only confinement ACCEPTS the adjacent placement (the gap):
example : (certifySecurity heronMarrakesh Fd1 victimCirc).accepted = true := by decide
-- the neighbour-buffered policy REJECTS it (the fix):
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) victimCirc).accepted
        = false := by decide
-- and does NOT over-block a genuinely distant co-tenant region:
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Ffar) victimCirc).accepted
        = true := by decide
def main : IO Unit := IO.println "LEAN_VERDICTS_OK"
"""
tmp = os.path.join(tempfile.gettempdir(), "sim_cert.lean")
open(tmp, "w").write(lean)
env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
try:
    r = subprocess.run(["lake", "env", "lean", "--run", tmp], cwd=ROOT, env=env,
                       capture_output=True, text=True, timeout=900)
    ok = "LEAN_VERDICTS_OK" in r.stdout
    check("T8 kernel-checked validator verdicts", ok,
          "d=1 accepted by support-only, REJECTED by bufferF, distant region still accepted"
          if ok else f"rc={r.returncode} out={r.stdout[-300:]} err={r.stderr[-300:]}")
except Exception as e:
    check("T8 kernel-checked validator verdicts", False, f"could not run lean: {e}")

# ---------------------------------------------------------------- T9 blind
print("\nT9 blind structural prediction — scored against held-out hardware")
try:
    r9 = subprocess.run([sys.executable, BASE + "blind_score.py"],
                        capture_output=True, text=True, timeout=300)
    sc = json.load(open(BASE + "blind_score.json"))
    check("T9 blind prediction: zero missed leaks", sc["fn"] == 0 and r9.returncode == 0,
          f"n={sc['n']} tp={sc['tp']} tn={sc['tn']} fp={sc['fp']} fn={sc['fn']} "
          f"({sc['accuracy']*100:.1f}% agreement, safety-critical "
          f"{'PASS' if sc['safety_critical_pass'] else 'FAIL'})")
except Exception as e:
    check("T9 blind prediction: zero missed leaks", False, f"could not score: {e}")

# ---------------------------------------------------------------- summary
npass = sum(1 for _, ok, _ in results if ok)
print(f"\n{'='*70}\n{npass}/{len(results)} tests passed")
for name, ok, detail in results:
    print(("  [x] " if ok else "  [ ] ") + name)
print("\nREMINDER: T3 is forward-model self-consistency, not independent validation.")
print("Aer contains no crosstalk; the ZZ term is injected by construction.")
json.dump([dict(name=n, passed=o, detail=d) for n, o, d in results],
          open(BASE + "test_results.json", "w"), indent=1)
sys.exit(0 if npass == len(results) else 1)
