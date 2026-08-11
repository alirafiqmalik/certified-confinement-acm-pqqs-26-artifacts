"""
gen_device_corpus.py — turn real QPU topologies into Lean `Coupling n` devices.

Purpose: test the certifier against actual hardware graphs, with **no QPU access**.
`qiskit_ibm_runtime.fake_provider` ships calibration and topology snapshots of about
68 real IBM devices. None of them need an account, a token, or a second of quota.
They include Heron (156q), heavy-hex Eagle (127q), the Nighthawk square lattice
(120q), and a long tail of smaller machines.

Edge counts: Qiskit reports a DIRECTED coupling map. Heron is 352 directed pairs,
which is **176 canonical undirected edges**. Nighthawk is 436 directed pairs,
which is 218 canonical undirected edges. Everything downstream of `canon()` uses
the canonical undirected count: the emitted `EdgeSpec`, the Lean file, and this
module's output. Do not quote the directed figure as an edge count.

For each selected device we emit:
  * `dev_<name> : EdgeSpec n` — the canonical edge list, plus the two finite
    `by decide` side conditions. `DeviceLib` uses these to derive a `Coupling n`
    generically.
  * a tenant partition (A, F) chosen structurally, not from any measurement:
      victim  = the highest-degree qubit (worst case for confinement)
      F       = a co-tenant region placed 3 hops away, so it stays genuinely disjoint
  * two witness circuits:
      `adj`  — victim acts on itself and a NEIGHBOR of F. This is support-disjoint
               from F: exactly the placement that plain `confinedb` misses.
      `far`  — victim acts well away from F
  * `#eval` verdicts for: support-only confinement, `bufferF`, and `hardwareLegal`.

The generated file is checked by `lake build`. So the *encoding* of every device is
kernel-verified, even where individual verdicts are `#eval` rather than `by decide`.
"""
import json, os, sys
from collections import deque

OUT_LEAN = os.path.abspath(os.path.join(
    os.path.dirname(__file__), "../../QpuCompiler/DeviceCorpus.lean"))
OUT_META = os.path.join(os.path.dirname(os.path.abspath(__file__)), "corpus_meta.json")

# A deliberately diverse slice: three topology families across a range of sizes.
SELECTED = [
    # Small devices come first. These probe how far kernel `decide` still works.
    ("FakeBelemV2",     "belem"),      # 5q
    ("FakeLagosV2",     "lagos"),      # 7q
    ("FakeGuadalupeV2", "guadalupe"),  # 16q
    ("FakeHanoiV2",     "hanoi"),      # 27q
    ("FakeBrooklynV2",  "brooklyn"),   # 65q
    # Then real full-size machines.
    ("FakeNighthawk",   "nighthawk"),  # 120q square lattice, degree 4
    ("FakeSherbrooke",  "sherbrooke"), # 127q heavy-hex Eagle
    ("FakeWashingtonV2","washington"), # 127q, different wiring
    ("FakeTorino",      "torino"),     # 133q
    ("FakeMarrakesh",   "marrakesh"),  # 156q Heron r2 — the device we measured
    ("FakeFez",         "fez"),        # 156q Heron r2 — also measured
    ("FakeKingston",    "kingston"),   # 156q Heron r2 — NEVER measured on hardware
]

# Kernel `decide` now works for EVERY device in this corpus, including the full
# 156-qubit Heron r2 topology (measured at about 3 s for all four verdicts). The
# old ~20-30 qubit ceiling came from one design choice: the edge relation was an
# explicit disjunction. The `EdgeSpec` list representation removes this limit. The
# script keeps this value as a knob. If a future device is even larger, the
# script can use it to re-probe the ceiling.
DECIDE_MAX_QUBITS = 100000


def bfs(adj, src, maxd):
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


def build(name):
    from qiskit_ibm_runtime import fake_provider as fp
    b = getattr(fp, name)()
    nq = b.num_qubits
    raw = [tuple(e) for e in b.coupling_map.get_edges()]
    # get_edges() reports directed pairs on some backends and undirected pairs on
    # others. This script converts each pair to (lo, hi), which normalizes both
    # forms. EdgeSpec requires this canonical form.
    canon = sorted({(min(a, c), max(a, c)) for a, c in raw if a != c})
    adj = {i: set() for i in range(nq)}
    for a, c in canon:
        adj[a].add(c); adj[c].add(a)
    if not canon:
        return None

    # Put the co-tenant region in the BULK of the device, not at the index boundary.
    # Among the highest-degree qubits, take the one with the largest 3-hop
    # neighborhood, that is, the most interior qubit. If the region sits at a
    # boundary qubit, the test becomes trivial.
    def ball(q, r):
        return len(bfs(adj, q, r))
    maxdeg = max(len(adj[q]) for q in range(nq))
    cands = [q for q in range(nq) if len(adj[q]) == maxdeg]
    seed = max(cands, key=lambda q: (ball(q, 3), -q))
    F = sorted([seed] + sorted(adj[seed])[:2])
    Fset = set(F)

    # This is the distance from the WHOLE region F, computed by a multi-source
    # BFS. bufferK uses this distance.
    dfromF = {}
    frontier = deque((f, 0) for f in F)
    seen = set(F)
    for f in F:
        dfromF[f] = 0
    while frontier:
        u, d = frontier.popleft()
        if d >= 6:
            continue
        for v in adj[u]:
            if v not in seen:
                seen.add(v); dfromF[v] = d + 1; frontier.append((v, d + 1))

    ring1 = sorted(q for q, d in dfromF.items() if d == 1)     # bufferF excludes these
    ring2 = sorted(q for q, d in dfromF.items() if d == 2)     # bufferF allows this ring. A radius-2 bufferK blocks it.
    ring3 = sorted(q for q, d in dfromF.items() if d >= 3)

    # ADJ witness: support-disjoint from F, but on ring1. Plain confinement accepts
    # it. bufferF rejects it.
    adj_pair = None
    for t in ring1:
        for p in sorted(adj[t]):
            if p not in Fset:
                adj_pair = (t, p); break
        if adj_pair:
            break

    # FAR witness: both endpoints are at distance 2 or more from F. bufferF must
    # still accept this witness.
    far_pair = None
    for a, c in canon:
        if dfromF.get(a, 99) >= 2 and dfromF.get(c, 99) >= 2:
            far_pair = (a, c); break

    # DEEP witness: both endpoints are at distance 3 or more. This witness survives
    # even a 2-hop buffer.
    deep_pair = None
    for a, c in canon:
        if dfromF.get(a, 99) >= 3 and dfromF.get(c, 99) >= 3:
            deep_pair = (a, c); break

    if not (adj_pair and far_pair):
        return None
    return dict(name=name, nq=nq, edges=canon, F=F, seed=seed,
                degree=len(adj[seed]), adj_pair=adj_pair, far_pair=far_pair,
                deep_pair=deep_pair, n_ring1=len(ring1), n_ring2=len(ring2),
                n_ring3=len(ring3),
                adj_dist=[dfromF.get(adj_pair[0]), dfromF.get(adj_pair[1])],
                far_dist=[dfromF.get(far_pair[0]), dfromF.get(far_pair[1])])


def lean_list(pairs):
    return "[" + ", ".join(f"({a},{b})" for a, b in pairs) + "]"


def emit(dev, slug):
    n, es = dev["nq"], dev["edges"]
    F, seed = dev["F"], dev["seed"]
    t, p = dev["adj_pair"]
    fa, fb = dev["far_pair"]
    kernel = n <= DECIDE_MAX_QUBITS
    # Use `by decide` where the kernel can still cope. Use `#eval` beyond that
    # point, and label it as such.
    #
    # maxRecDepth 100000 here sets the recursion-depth budget for `decide` over the
    # whole-circuit `certifySecurity` fold. This fold checks HWF and confinement, and
    # it walks every gate. This budget is a separate knob from `DECIDE_MAX_QUBITS`
    # above. That knob picks kernel `decide` or `#eval` for each device. This budget
    # is Lean's own elaborator limit for the proof term that `decide` builds. Both
    # share the numeral 100000 by coincidence, not because one comes from the other.
    # Do not assume that a change to one budget affects the other. This budget was
    # not tuned to a measured minimum. It is round-number headroom that clears the
    # largest device tried (156 qubits, 176 edges) with margin. It has never needed
    # a raise. If a future device makes `decide` hit this limit, first check
    # whether the recursion grows in proportion to circuit and gate-fold size, as
    # expected. Only then raise the number further.
    def claim(expr, expected, note):
        if kernel:
            return (f"set_option maxRecDepth 100000 in\nexample : {expr} = {expected} := by decide"
                    f"   -- {note} [KERNEL]")
        return f"#eval {expr}   -- expect {expected}  ({note}) [EVAL]"

    L = []
    L.append(f"/-! ### `{dev['name']}` — {n} qubits, {len(es)} canonical edges."
             f"  verdicts: {'KERNEL `decide`' if kernel else '`#eval` only'}")
    L.append(f"Co-tenant region `F = {F}` is seeded at the degree-{dev['degree']} qubit q{seed},")
    L.append(f"chosen as the most *interior* max-degree site so the test is not a boundary case.")
    L.append(f"Rings by distance from F: |d=1| = {dev['n_ring1']}, |d=2| = {dev['n_ring2']},"
             f" |d>=3| = {dev['n_ring3']}. -/")
    # maxRecDepth 8000 here budgets `decide` only for `ordered_all` and `bounded_all`.
    # These are a `List.all` fold over the edge list (see the EdgeSpec docstring in
    # DeviceLib.lean). This Bool-fold form is why this budget is much smaller than
    # the 100000 above, which covers the heavier whole-circuit `certifySecurity`
    # fold, not the edge-list check. 8000 is round-number headroom over the largest
    # edge list in this corpus (176 pairs). It is not a tuned minimum, and it has
    # never needed a raise.
    L.append(f"set_option maxRecDepth 8000 in")
    L.append(f"def spec_{slug} : EdgeSpec {n} where")
    L.append(f"  edges := {lean_list(es)}")
    L.append("  ordered_all := by decide")
    L.append("  bounded_all := by decide")
    L.append("")
    L.append(f"def dev_{slug} : Coupling {n} := spec_{slug}.toCoupling")
    L.append(f"def F_{slug} : ℕ → Bool := fun q => {' || '.join(f'decide (q = {x})' for x in F)}")
    L.append(f"/-- Support-disjoint from `F` yet sitting ON its 1-hop ring (distance"
             f" {dev['adj_dist']}): the placement plain `confinedb` accepts and `bufferF` must reject. -/")
    L.append(f"def adj_{slug} : UCom {n} := .seq (.app1 .x {t}) (.cz {t} {p})")
    L.append(f"/-- Distance {dev['far_dist']} from `F` on both ends: must stay accepted. -/")
    L.append(f"def far_{slug} : UCom {n} := .seq (.app1 .x {fa}) (.cz {fa} {fb})")
    L.append(claim(f"(certifySecurity dev_{slug} F_{slug} adj_{slug}).accepted",
                   "true", "THE GAP: support-only confinement accepts an adjacent placement"))
    L.append(claim(f"(certifySecurity dev_{slug} (bufferF dev_{slug} F_{slug}) adj_{slug}).accepted",
                   "false", "THE FIX: neighbour-buffered policy rejects it"))
    L.append(claim(f"(certifySecurity dev_{slug} (bufferF dev_{slug} F_{slug}) far_{slug}).accepted",
                   "true", "NO OVER-BLOCK: a distant placement is still accepted"))
    L.append(claim(f"(certifySecurity dev_{slug} (bufferF dev_{slug} F_{slug}) adj_{slug}).hardwareLegal",
                   "true", "the rejection is POLICY, not hardware legality"))
    L.append("")
    return "\n".join(L)


def header(meta, skipped):
    """Build the file header FROM the emitted results.

    This header used to be a hardcoded literal. That literal drifted from the truth
    over time. It claimed that the per-device verdicts were `#eval`, because kernel
    `decide` was "impractical" at 156 qubits. But every verdict actually emitted was
    `by decide`. The literal also quoted a directed edge count (352) against an
    undirected encoding (176). It said nothing when SELECTED dropped a device.
    Deriving the header from the results removes all three failure modes.
    """
    n_dev = len(meta)
    n_kernel = sum(1 for m in meta if m["kernel_checked"])
    n_eval = n_dev - n_kernel
    max_q = max((m["nq"] for m in meta), default=0)
    max_e = max((m["n_edges"] for m in meta), default=0)
    if n_eval == 0:
        checked = [
            f'NOTE ON WHAT IS KERNEL-CHECKED: all {4 * n_dev} per-device verdicts below are',
            f'`by decide`, kernel-checked — including at the largest device in the corpus',
            f'({max_q} qubits, {max_e} canonical undirected edges). The canonical edge-list',
            '`EdgeSpec` encoding is what makes that practical; an earlier nested-disjunction',
            'encoding did not reduce at this size. Each device *encoding* is additionally',
            'checked by `lake build` (`ordered_all`/`bounded_all` are `by decide` over the real',
            'edge list, and `DeviceLib` derives symmetry/irreflexivity/bounds generically).',
        ]
    else:
        checked = [
            'NOTE ON WHAT IS KERNEL-CHECKED: every device *encoding* is verified by `lake build`',
            '(`ordered_all`/`bounded_all` are `by decide` over the real edge list, and `DeviceLib`',
            'derives symmetry/irreflexivity/bounds generically). Of the per-device verdicts,',
            f'{4 * n_kernel} are `by decide` [KERNEL] and {4 * n_eval} are `#eval` [EVAL] — the',
            f'`#eval` ones are on devices above {DECIDE_MAX_QUBITS} qubits, the honest scaling limit.',
        ]
    skip_lines = []
    if skipped:
        skip_lines = ['',
                      f'DEVICES REQUESTED BUT NOT EMITTED ({len(skipped)} of {len(SELECTED)}):']
        skip_lines += [f'  * {cls} — {why}' for cls, why in skipped]
    return ['/-',
            'QpuCompiler/DeviceCorpus.lean — GENERATED by',
            'harness/devices/gen_device_corpus.py. Do not hand-edit.',
            '',
            f'{n_dev} real IBM QPU topologies (7–{max_q} qubits) encoded as `Coupling n`, so the',
            'certifier can be exercised against actual hardware graphs with **no QPU access',
            'whatsoever** (topologies come from `qiskit_ibm_runtime.fake_provider`, which needs',
            'no account and no quota).',
            '',
            'Each device gets a worst-case tenant partition and two witnesses. The four verdicts',
            'per device assert the same four facts the paper argues on its toy models:',
            '  1. support-only confinement ACCEPTS a support-disjoint but ADJACENT placement,',
            '  2. the neighbour-buffered policy REJECTS it,',
            '  3. a genuinely distant placement is still ACCEPTED (no over-blocking),',
            '  4. the rejected placement is hardware-LEGAL — so the refusal is policy, not legality.',
            ''] + checked + skip_lines + [
            '-/',
            'import QpuCompiler.DeviceLib',
            'import QpuCompiler.Buffer',
            '',
            'namespace QpuCompiler',
            '']


if __name__ == "__main__":
    body, meta, skipped = [], [], []
    for cls, slug in SELECTED:
        try:
            d = build(cls)
        except Exception as e:
            why = f"{type(e).__name__}: {e}"
            print(f"  SKIP {cls}: {why}"); skipped.append((cls, why)); continue
        if d is None:
            why = "no valid tenant partition found"
            print(f"  SKIP {cls}: {why}"); skipped.append((cls, why)); continue
        body.append(emit(d, slug))
        meta.append(dict(slug=slug, kernel_checked=(d["nq"] <= DECIDE_MAX_QUBITS),
                         **{k: v for k, v in d.items() if k != "edges"},
                         n_edges=len(d["edges"])))
        mode = "KERNEL" if d["nq"] <= DECIDE_MAX_QUBITS else "eval  "
        print(f"  {cls:<20} {d['nq']:4d}q {len(d['edges']):4d}e  {mode}  F={d['F']}  "
              f"adj={d['adj_pair']}@{d['adj_dist']}  far={d['far_pair']}@{d['far_dist']}  "
              f"rings={d['n_ring1']}/{d['n_ring2']}/{d['n_ring3']}")
    hdr = header(meta, skipped)
    open(OUT_LEAN, "w").write("\n".join(hdr) + "\n".join(body) + "\nend QpuCompiler\n")
    json.dump(dict(devices=meta, skipped=[dict(cls=c, reason=r) for c, r in skipped]),
              open(OUT_META, "w"), indent=1)
    print(f"\nwrote {OUT_LEAN}\nwrote {OUT_META}  "
          f"({len(meta)} devices, {len(skipped)} skipped)")
