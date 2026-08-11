"""
blind_score.py — score the blind structural predictions against HELD-OUT hardware.

This file is deliberately separate from `blind_predict.py`. A guard mechanically
blocks the predictor from reading any results file. This scorer reads both
files. It never feeds anything back to the predictor. Running the scorer
cannot change a prediction.

Scored quantity: the STRUCTURAL prediction that "a probe leaks if and only if
it sits at graph distance 1 from the victim". We derived this prediction from
the published coupling map and the documented nearest-neighbor residual-ZZ
mechanism. We committed it in QpuCompiler/Buffer.lean on 2026-07-23, five days
before the first measurement.

We score two directions separately, because they are not equally important:

  SAFETY-CRITICAL  never predict "no leak" for a placement that does leak.
                   A miss here means that the certifier accepts a leaking
                   placement. The paper's soundness claim depends on this
                   direction.
  CONSERVATISM     predicting "leak" where none was detected is a harmless
                   over-block. The certifier refuses a placement that happened to
                   be quiet. This over-block costs usable area, not security.
"""
import json, os

BASE = os.path.dirname(os.path.abspath(__file__)) + "/"
HW = os.path.abspath(BASE + "../ibm-hardware") + "/"
LEAK_Z = 5.0

pred = json.load(open(BASE + "blind_predictions.json"))


def observations():
    """This is every held-out hardware observation, as a tuple: (device, victim, probe, distance, z)."""
    obs = []

    def add(dev, victim, probe, dist, z, src):
        obs.append(dict(device=dev, victim=victim, probe=probe, dist=dist,
                        z=z, leaked=(z >= LEAK_Z), src=src))

    prereg = json.load(open(HW + "sweep_prereg.json"))
    pairmap = {}
    for dev, info in prereg["devices"].items():
        for i, p in enumerate(info["pairs"]):
            pairmap[(dev, i)] = p

    for fn, src in (("sweep_results.json", "snap1"), ("repeat_results.json", "snap2")):
        d = json.load(open(HW + fn))
        for p in d["pairs"]:
            key = (p["device"], p["pair"])
            if key not in pairmap:
                continue
            pr = pairmap[key]
            add(p["device"], pr["victim"], pr["d1"], 1, p["d1"]["z"], src)
            add(p["device"], pr["victim"], pr["d2"], 2, p["d2"]["z"], src)

    for fn, src in (("results_mrk_t3.json", "snap3"), ("results_mrk_new.json", "new")):
        d = json.load(open(HW + fn))
        for p in d["pairs"]:
            add(d["backend"], p["victim"], p["d1_qubit"], 1, p["d1"]["z"], src)
            add(d["backend"], p["victim"], p["d2_qubit"], 2, p["d2"]["z"], src)
    return obs


obs = observations()
print(f"held-out observations: {len(obs)}\n")

# This is the structural rule, repeated here only to score it. It matches the predictor's rule exactly.
def predicted_leak(dist):
    return dist == 1


tp = fp = tn = fn = 0
rows = []
for o in obs:
    pl = predicted_leak(o["dist"])
    if pl and o["leaked"]:
        tp += 1; verdict = "hit"
    elif pl and not o["leaked"]:
        fp += 1; verdict = "over-block (harmless)"
    elif not pl and not o["leaked"]:
        tn += 1; verdict = "correct null"
    else:
        fn += 1; verdict = "*** MISSED LEAK (unsafe) ***"
    rows.append((o, pl, verdict))

print(f"{'src':<7}{'device':<15}{'v->p':<12}{'d':<3}{'z':>8}  {'predicted':<10}{'outcome'}")
for o, pl, v in rows:
    vp = "%d->%d" % (o["victim"], o["probe"])
    print("%-7s%-15s%-12s%-3d%8.1f  %-10s%s" % (
        o["src"], o["device"][4:], vp, o["dist"], o["z"],
        "LEAK" if pl else "no leak", v))

n = len(obs)
print(f"\n{'='*72}")
print(f"confusion matrix over {n} held-out observations")
print(f"  true positive  (predicted leak, leaked)         : {tp}")
print(f"  true negative  (predicted no leak, no leak)     : {tn}")
print(f"  false positive (predicted leak, none detected)  : {fp}   <- conservative over-block")
print(f"  FALSE NEGATIVE (predicted no leak, but LEAKED)  : {fn}   <- unsafe; must be 0")
acc = (tp + tn) / n
print(f"\n  overall agreement           : {tp+tn}/{n} = {acc*100:.1f}%")
d1 = [o for o in obs if o['dist'] == 1]
d2 = [o for o in obs if o['dist'] >= 2]
print(f"  d=1 predicted-leak recall   : {sum(1 for o in d1 if o['leaked'])}/{len(d1)}")
print(f"  d>=2 predicted-null accuracy: {sum(1 for o in d2 if not o['leaked'])}/{len(d2)}")
print(f"\n  SAFETY-CRITICAL DIRECTION (no missed leaks): "
      f"{'PASS' if fn == 0 else 'FAIL'} ({n-fn}/{n})")

json.dump(dict(n=n, tp=tp, tn=tn, fp=fp, fn=fn, accuracy=acc,
               safety_critical_pass=(fn == 0),
               rule=pred["rule"], observations=obs),
          open(BASE + "blind_score.json", "w"), indent=1)
print("\nwrote blind_score.json")
raise SystemExit(0 if fn == 0 else 1)
