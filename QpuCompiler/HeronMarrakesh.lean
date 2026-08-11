/-
QpuCompiler/HeronMarrakesh.lean — the validator bridge to the LIVE IBM result.

On `ibm_marrakesh` (IBM Heron r2, 156q, free/open plan), on 2026-07-28, we measured a
real multi-tenant side channel. A co-tenant one hop from a victim qubit reads the
victim's secret STATE through always-on ZZ coupling. ΔP = 0.38 (z = 82) at graph
distance 1, and there is **no signal** (z < 1.5) at distance 2 or more. A
mechanism-control run showed that pure drive activity that returns to |0⟩ leaks a
negligible amount (z = 1.6). So the channel is static-ZZ *state* readout, strictly
nearest-neighbor. (Full data:
`harness/ibm-hardware/IBM-RESULTS.md`.)

This file encodes the REAL device neighborhood of the victim (physical qubit 98 and
the qubits within 3 hops, relabeled 0..11 — see `marrakesh_patch.json`) as a
`Coupling 12`. It shows that the validator's verdict matches the physical leak:

  * The victim runs on qubit **6** (phys q98). Its gate support is `{6}`. It never
    gates a co-tenant qubit. It only *sits next to* one.
  * The d=1 probe (the co-tenant that leaked) is qubit **3** (phys q91). It neighbors
    qubit 6 through the real coupling edge (3,6) — the same edge that carried the ZZ leak.
  * The far probe (no signal) is qubit **0** (phys q6), isolated within this patch.

Correspondence (kernel-checked below):
  - support-only `confinedb` ACCEPTS the victim next to the leaking co-tenant  ← the GAP
  - the neighbor-buffered policy `bufferF` REJECTS exactly that d=1 placement  ← the FIX
  - and ACCEPTS the far placement that showed no signal                        ← no over-block

SCOPE (honest): this is a STRUCTURAL guarantee. The certificate proves that the victim
shares no coupling edge with the co-tenant region. The hardware shows that removing
that edge removes the measurable channel. It is NOT a bound on crosstalk magnitude, and
it rests on a single victim/pair/calibration snapshot. `certifySecurity_sound` is reused
verbatim (`bufferF` is just another decidable region argument): the trusted base stays
the same.

DATA NOTE: on this induced patch the victim (node 6) has degree 2, between the two
genuine degree-3 heavy-hex sites 3 and 9. The d=1 co-tenant (node 3) has degree 3 itself.
-/
import QpuCompiler.Buffer

namespace QpuCompiler

/-! ## The real `ibm_marrakesh` victim neighborhood as a `Coupling 12`

Undirected edges of the induced subgraph on physical qubits
`{6,89,90,91,92,93,98,109,110,111,112,113}` (relabeled 0..11):
`(1,2) (2,3) (3,4) (3,6) (4,5) (6,9) (7,8) (8,9) (9,10) (10,11)`. Node 0 (far probe,
phys q6) is isolated within the patch. -/
/-- Undirected edge list of the induced patch (relabeled 0..11). -/
def mEdges : List (ℕ × ℕ) :=
  [(1,2), (2,3), (3,4), (3,6), (4,5), (6,9), (7,8), (8,9), (9,10), (10,11)]

/-- Edge test through *unordered* membership: `{a,b}` is an edge if and only if
`(min a b, max a b)` is in `mEdges`. The test is symmetric by construction. The term
stays small (a 10-element list scan) instead of a 20-way nested `decide`. Both
properties now come from the generic `EdgeSpec` construction in `DeviceLib.lean`,
not from three hand-written proofs. -/
def specHeronMarrakesh : EdgeSpec 12 where
  edges := mEdges
  ordered_all := by decide
  bounded_all := by decide

def heronMarrakesh : Coupling 12 := specHeronMarrakesh.toCoupling

/-- Degree of a qubit in the patch (for the record). -/
def patchDegree (x : ℕ) : ℕ := (List.range 12).countP (fun y => heronMarrakesh.edge x y)

-- The victim (node 6) is adjacent to the d=1 co-tenant (node 3) through a real edge…
example : heronMarrakesh.edge 6 3 = true := by decide
-- …and node 3 (the leaking co-tenant) is a genuine degree-3 heavy-hex site:
#eval patchDegree 3          -- 3
#eval patchDegree 9          -- 3   (the other degree-3 site)
#eval patchDegree 6          -- 2   (victim: degree-2, between the two degree-3 sites)
example : heronMarrakesh.edge 3 2 = true ∧ heronMarrakesh.edge 3 4 = true
    ∧ heronMarrakesh.edge 3 6 = true := by decide
-- node 0 (far probe, phys q6) is isolated within this patch:
example : (List.range 12).all (fun y => !heronMarrakesh.edge 0 y) = true := by decide

/-! ## The experiment's placements -/

/-- Victim circuit: runs on qubit **6** (phys q98) only. Its support `{6}` is disjoint
from every probe/co-tenant qubit — the victim never gates a co-tenant qubit. -/
def victimCirc : UCom 12 := .seq (.app1 .x 6) (.app1 .x 6)

/-- Forbidden co-tenant region = the **d=1 probe** (qubit 3, phys q91) that leaked. -/
def Fd1 : ℕ → Bool := fun q => decide (q = 3)

/-- Forbidden co-tenant region = the **far probe** (qubit 0, phys q6) that showed no signal. -/
def Ffar : ℕ → Bool := fun q => decide (q = 0)

/-! ## The gap and the device-specific fix — kernel-checked

Each `example` is `by decide` (kernel-checked). The `#eval`s print the same verdict. -/

-- The 1-hop buffer of the d=1 co-tenant is {3} ∪ neighbors(3) = {2,3,4,6}. It CONTAINS
-- the victim qubit 6. This is why the validator rejects the adjacent placement:
#eval (List.range 12).filter (bufferF heronMarrakesh Fd1)     -- [2, 3, 4, 6]
example : (List.range 12).filter (bufferF heronMarrakesh Fd1) = [2, 3, 4, 6] := by decide

-- (1) THE GAP — support-only confinement ACCEPTS the victim next to the leaking co-tenant:
#eval (certifySecurity heronMarrakesh Fd1 victimCirc).accepted        -- true
example : (certifySecurity heronMarrakesh Fd1 victimCirc).accepted = true := by decide

-- (2) THE FIX — the neighbor-buffered policy REJECTS exactly the d=1 placement that leaked
--     (same one-call driver, same `certifySecurity_sound`, just a buffered region):
#eval (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) victimCirc).accepted  -- false
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) victimCirc).accepted
    = false := by decide

-- …and the rejection is on POLICY, not hardware legality — the victim placement is legal:
#eval (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) victimCirc).hardwareLegal -- true
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) victimCirc).hardwareLegal
    = true := by decide

-- (3) NO OVER-BLOCKING — the far co-tenant (node 0, isolated, no signal) is ACCEPTED. Its
--     buffer is just {0}. It does not contain the victim qubit 6:
#eval (List.range 12).filter (bufferF heronMarrakesh Ffar)    -- [0]
example : (List.range 12).filter (bufferF heronMarrakesh Ffar) = [0] := by decide
#eval (certifySecurity heronMarrakesh (bufferF heronMarrakesh Ffar) victimCirc).accepted  -- true
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Ffar) victimCirc).accepted
    = true := by decide

end QpuCompiler
