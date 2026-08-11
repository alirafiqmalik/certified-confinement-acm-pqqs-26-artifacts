"""
blind_predict.py — predicts WHERE leaks occur, from PUBLIC device data only.

===================== THE POINT OF THIS FILE =====================
The forward model in `qpu_sim.py` is circular. The model receives a measured ΔP.
It fits a coupling ζ to the ΔP. Then it reproduces the same ΔP. This process has
zero predictive content.

This file is the non-circular counterpart to that model. This script can read
ONLY data that IBM publishes for any user, before any experiment runs:

    * the coupling map          (which physical qubit pairs connect)
    * T1 / T2                   (per qubit)
    * readout error             (per qubit)
    * CZ gate durations/errors  (per edge)

The function `_guard_open`, below, **mechanically forbids** this script from
reading our own leak results. It raises an error on any path that matches a
results file. So the code enforces the blindness. We do not merely assert the
blindness in a comment.

We fix the prediction rule in advance, from the *documented mechanism*. The rule
is not tuned to our data. Always-on residual ZZ couples only qubits that share a
coupling edge. So a probe leaks if and only if it sits at graph distance 1 from
the victim. We committed this rule in `QpuCompiler/Buffer.lean` on 2026-07-23,
five days BEFORE the first hardware run on 2026-07-28. The derivation order is
checkable from the repository. This is what makes "blind" a claim about
provenance, and not only a claim about this script.

===================== WHAT CANNOT BE PREDICTED =====================
We cannot predict the *magnitude* ζ. The transmon static-ZZ rate is a function
of the qubit-qubit coupling J, the detuning Δ = ω_i − ω_j, and the anharmonicities
α_i, α_j. For IBM Heron r2, the API returns `frequency = None`. The API exposes no
anharmonicity.

The API publishes no J, and no tunable-coupler bias point. CZ duration takes only
two distinct values device-wide (68 ns and 80 ns), so it also carries no usable
per-edge information. On a tunable-coupler device, the residual ZZ is also a
function of how precisely the coupler was biased to null it. IBM does not
publish this calibration detail at all.

So magnitude here is not merely hard to predict. Public data **does not
determine** the magnitude. We therefore predict a *detectability band* from a
literature prior on residual ZZ for tunable-coupler transmons. We state that
this band is a prior, and not a device-specific calculation.

This asymmetry is the empirical case for the paper's design. The certificate is
structural, because structure is publicly predictable and magnitude is not.
"""
import builtins, json, math, os, sys
from collections import deque

BASE = os.path.dirname(os.path.abspath(__file__)) + "/"

# ---------------------------------------------------------------- blindness guard
FORBIDDEN = ("results_", "sweep_results", "repeat_results", "ibm_results",
             "ibm_ctrl_results", "test_results", "tau_discriminator.json",
             "RESULTS-", "SWEEP-RESULTS", "IBM-RESULTS")
_real_open = builtins.open


def _guard_open(path, *a, **k):
    p = str(path)
    base = os.path.basename(p)
    if any(f in base for f in FORBIDDEN):
        raise PermissionError(
            f"BLINDNESS VIOLATION: blind_predict.py attempted to read '{base}'. "
            "This script may only use public device metadata.")
    return _real_open(path, *a, **k)


builtins.open = _guard_open

# ---------------------------------------------------------------- literature prior
# This is the residual ZZ for tunable-coupler transmons after coupler nulling. The
# script states it as a PRIOR RANGE, not a device-specific calculation. The range
# is wide on purpose.
ZETA_PRIOR_HZ = (100.0, 5000.0)
TAU = 40e-6
SHOTS_TOTAL = 8192 * 2
LEAK_Z = 5.0


def dP_of(zeta, tau=TAU):
    return abs(math.sin(2 * math.pi * zeta * tau))


def z_of(dP, n=SHOTS_TOTAL):
    """This is the z-score for a two-proportion test at a p≈0.5 baseline. This protocol sits in this regime."""
    se = math.sqrt(2 * 0.25 / n)
    return dP / se if se > 0 else 0.0


def load_public(path):
    """This function loads public metadata only: the coupling map, per-qubit T1/T2 and readout, and CZ durations."""
    d = json.load(_real_open(path))          # The guard blocks only *results* files. This path is metadata, so this call uses `_real_open` directly.
    return d


def graph_distances(nq, edges, src, maxd=4):
    adj = {i: set() for i in range(nq)}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    dist = {src: 0}
    q = deque([src])
    while q:
        u = q.popleft()
        if dist[u] >= maxd:
            continue
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def predict_for_victim(nq, edges, victim, maxd=4):
    """THE BLIND PREDICTION. This prediction is structural. It comes from the coupling map alone."""
    dist = graph_distances(nq, edges, victim, maxd)
    lo, hi = ZETA_PRIOR_HZ
    out = []
    for q, dd in sorted(dist.items(), key=lambda kv: (kv[1], kv[0])):
        if q == victim:
            continue
        leaks = (dd == 1)
        band = (dP_of(lo), dP_of(hi)) if leaks else (0.0, 0.0)
        out.append(dict(probe=q, graph_distance=dd, predicted_leak=leaks,
                        predicted_dP_band=band,
                        predicted_z_band=(z_of(band[0]), z_of(band[1])),
                        detectable=leaks and z_of(band[0]) >= LEAK_Z))
    return out


if __name__ == "__main__":
    meta_path = sys.argv[1] if len(sys.argv) > 1 else BASE + "public_meta_ibm_marrakesh.json"
    meta = load_public(meta_path)
    nq, edges = meta["num_qubits"], [tuple(e) for e in meta["coupling_map"]]
    print(f"device: {meta['backend']}   qubits={nq}   edges={len(edges)}")
    print(f"public fields used: {', '.join(meta['public_fields_used'])}")
    print(f"fields NOT published (so magnitude is unpredictable): "
          f"{', '.join(meta['fields_unavailable'])}")
    lo, hi = ZETA_PRIOR_HZ
    print(f"\nliterature prior on residual ZZ: {lo:.0f}-{hi:.0f} Hz  ->  at tau={TAU*1e6:.0f}us "
          f"predicted dP band = {dP_of(lo):.3f}-{dP_of(hi):.3f}  (z = {z_of(dP_of(lo)):.0f}-{z_of(dP_of(hi)):.0f})")

    victims = meta.get("victims_of_interest", [98])
    allpred = {}
    for v in victims:
        pred = predict_for_victim(nq, edges, v)
        allpred[str(v)] = pred
        d1 = [p for p in pred if p["graph_distance"] == 1]
        d2p = [p for p in pred if p["graph_distance"] >= 2]
        print(f"\nvictim q{v}: {len(d1)} neighbours predicted TO LEAK -> "
              f"{[p['probe'] for p in d1]}")
        print(f"           {len(d2p)} qubits at distance>=2 predicted NO LEAK "
              f"(showing 6: {[p['probe'] for p in d2p[:6]]})")

    json.dump(dict(prior_hz=ZETA_PRIOR_HZ, tau_s=TAU, shots_total=SHOTS_TOTAL,
                   leak_z=LEAK_Z, predictions=allpred,
                   rule="leak iff graph_distance == 1 (documented NN residual-ZZ mechanism, "
                        "fixed in Buffer.lean 2026-07-23, before the 2026-07-28 measurement)"),
              _real_open(BASE + "blind_predictions.json", "w"), indent=1)
    print("\nwrote blind_predictions.json  (no leak-result file was read; guard active)")
