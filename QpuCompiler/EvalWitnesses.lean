/-
QpuCompiler/EvalWitnesses.lean — Axis-1 caught-violation witnesses (Fork B/C [NEED] #1).

This file gives three per-instance `#eval` witnesses for the evaluation. Each
witness also appears as a kernel-checked `example ... := by decide`. This shows
that the verdict is not only an `#eval` print. It is a proof.

  (a) SWAP-drags-secret-across-boundary  → REJECTED  (hardware-legal yet unsafe)
  (b) externally-"optimized" circuit crosses the tenant boundary → REJECTED
  (c) 12-ring circuit fully within the allowed region → ACCEPTED

All witnesses use existing definitions (`certifySecurity`, `heavyHexFrag`/`fragF`,
`heavyHex`, `tenantF`, `swapEdge`, `optimize`, `ofList`). The file adds no new
axioms and no new trusted code.
-/
import QpuCompiler.Confine

namespace QpuCompiler

/-! ## (a) A routing SWAP that drags a secret across the tenant boundary is REJECTED.

`swapEdge 4 0 3` is the routing primitive (a SWAP macro) on the degree-3 fragment
edge `0–3`. The edge is HARDWARE-LEGAL, because `0–3` is a real edge. But the SWAP
moves qubit-`0` state onto the forbidden co-tenant qubit `3`. This is exactly the
SWAP-attack co-location channel. The certifier accepts the legality. But it REJECTS
the circuit under the confinement policy. -/
def wA : UCom 4 := swapEdge 4 0 3

#eval (certifySecurity heavyHexFrag fragF wA).hardwareLegal   -- true  (0–3 is a real edge)
#eval (certifySecurity heavyHexFrag fragF wA).accepted        -- false (touches forbidden qubit 3)

example : (certifySecurity heavyHexFrag fragF wA).hardwareLegal = true := by decide
example : (certifySecurity heavyHexFrag fragF wA).accepted = false := by decide

/-! ## (b) An externally-"optimized" circuit that crosses the boundary is REJECTED.

The external producer sends an ingested circuit `wBsrc`. The verified `optimize`
function runs on this circuit. The two `x 0` gates fuse, but the boundary-crossing
`cz 0 3` gate stays. The checker finds this gate in the OPTIMIZER'S OUTPUT `wB`.
So the checker catches a confinement violation after optimization, not only in the
raw input.

Proof note: the proof of the rejection of the ingested circuit `wBsrc` is
KERNEL-CHECKED (`by decide`, structural). The rejection of the optimizer output
`wB` is a runtime `#eval` witness. The reason is that `optimize`/`optFix` uses
well-founded recursion, and the kernel `decide` tactic does not reduce this
recursion. This proof deliberately avoids `native_decide`, to keep the trust base
free of axioms. (The proof of the *positive* direction — that `optimize` preserves
confinement — is a general proof, `optimize_conf`.) -/
def wBsrc : UCom 4 := ofList [.g1 .x 0, .g1 .x 0, .g2 0 3]
def wB : UCom 4 := optimize wBsrc

#eval (certifySecurity heavyHexFrag fragF wBsrc).accepted     -- false (ingested circuit rejected)
#eval (certifySecurity heavyHexFrag fragF wB).accepted        -- false (optimizer OUTPUT still rejected)

example : (certifySecurity heavyHexFrag fragF wBsrc).accepted = false := by decide

/-! ## (c) A 12-ring circuit confined to the allowed region is ACCEPTED.

This is a chain of ring `cz` gates, entirely inside the tenant slot `A = {0..5}`
(forbidden region `tenantF = {6..11}`). Every edge `i–(i+1)`, for `i ∈ {0..4}`, is
a real ring edge and stays inside the slot. So the certificate is ACCEPTED. -/
def wC : UCom 12 :=
  .seq (.cz 0 1) (.seq (.cz 1 2) (.seq (.cz 2 3) (.seq (.cz 3 4) (.cz 4 5))))

#eval (certifySecurity heavyHex tenantF wC).accepted          -- true (all gates within {0..5})

example : (certifySecurity heavyHex tenantF wC).accepted = true := by decide

/-! ## Summary line (prints all three verdicts at once). -/
#eval s!"(a) drag-secret={(certifySecurity heavyHexFrag fragF wA).accepted}  " ++
      s!"(b) opt-crosses={(certifySecurity heavyHexFrag fragF wB).accepted}  " ++
      s!"(c) ring-confined={(certifySecurity heavyHex tenantF wC).accepted}"
-- expected: (a) drag-secret=false  (b) opt-crosses=false  (c) ring-confined=true

end QpuCompiler
