/-
QpuCompiler/AdvWitnesses.lean — §E7 crafted hostile-transpiler witnesses.

The *incidental* direct-contact example (`.cz 0 3`) is different. We DELIBERATELY designed
these circuits to sneak a tenant-isolation violation past the validator. The validator
catches both. The neighbour-buffered policy catches W1. The sound lexer
`parseQASMSafe` catches W2.

VERIFICATION STATUS (honest, per witness — do NOT paraphrase as "every verdict is
`by decide`"):
  * **W1** — every verdict is `by decide` (kernel-checked) on the real `ibm_marrakesh`
    patch. The proof is fully verified end to end.
  * **W2** — the *circuit-level* verdicts are `by decide`. The old lexer yields the
    circuit `w2skipped`, with the guarded gate silently dropped, and the validator
    ACCEPTS it. The circuit `w2full` contains the hidden gate, and the validator
    REJECTS it. One step stays as an `#eval` witness only: `parseQASM w2src` equals
    `w2skipped`'s gate list, and `parseQASMSafe w2src = none`. This step CANNOT
    become `by decide`. `String.splitOn` uses well-founded recursion
    (`String.splitOnAux`, `Init/Data/String/Legacy.lean`), and string literals are
    opaque to the kernel except through `String.decEq`. So `decide`, `rfl`, and
    `simp` all get stuck on *any* `parseQASM`/`parseQASMSafe` application (verified:
    even `"abc".length = 3` fails `by decide`). The lexer sits on the UNTRUSTED
    producer side by design, so this `#eval` step stays outside the trusted base.
    But the paper must state this fact.
-/
import QpuCompiler.HeronMarrakesh
import QpuCompiler.Frontend

namespace QpuCompiler

/-! ## W1 — legal-but-adjacent (defeats support-only confinement)

Support `{6, 9}` is disjoint from the co-tenant `F = {3}`, and every gate is
hardware-legal. So a support-only check ACCEPTS it. Yet qubit 6 sits on the real
coupling edge `(3,6)` to the co-tenant — the exact adjacency that leaked. The
buffered policy CATCHES it. -/
def w1 : UCom 12 := .seq (.app1 .x 6) (.seq (.cz 6 9) (.app1 (.rz 0) 6))

#eval (certifySecurity heronMarrakesh Fd1 w1).accepted                               -- true (MISS)
example : (certifySecurity heronMarrakesh Fd1 w1).accepted = true := by decide
#eval (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) w1).accepted      -- false (CAUGHT)
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) w1).accepted = false := by
  decide
-- rejection is on policy, not legality — W1 is perfectly hardware-legal:
#eval (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) w1).hardwareLegal -- true
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) w1).hardwareLegal = true := by
  decide

/-! ## W2 — lexer-evasion (defeats the *old* front-end)

A conditioned CZ hides a gate onto the co-tenant qubit 3. The shipped `parseQASM`
silently skips the `if(...)` line. The validator then ACCEPTS the confined-looking
remainder (UNSOUND). `parseQASMSafe` rejects the unrecognized support-bearing token. -/
def w2src : String := "x q[6]; if(c==1) cz q[6],q[3];"

-- OLD lexer skips the guarded gate → validator ACCEPTS (the unsound hole).
-- `#eval` ONLY: the kernel cannot reduce `String.splitOn` (WF recursion, plus opaque
-- string literals). So this step cannot use `by decide`. See the header.
#eval (parseQASM w2src).length                                                       -- 1 (`x q[6]`)
#eval (certifySecurity heronMarrakesh Fd1 (ofList (parseQASM w2src))).accepted       -- true (UNSOUND)
-- SAFE lexer: unrecognized support-bearing token → parse fails → REJECT (`#eval` only):
#eval (parseQASMSafe w2src).isNone                                                    -- true (SAFE)

/-- The circuit that the OLD lexer yields on `w2src`. The lexer silently drops the
`if(...)` statement, leaving a confined-looking remainder. -/
def w2skipped : UCom 12 := ofList [.g1 .x 6]
/-- The circuit that `w2src` really denotes, with the hidden guarded gate visible. -/
def w2full : UCom 12 := .seq (.app1 .x 6) (.cz 6 3)

-- Kernel-checked circuit level: the skipped remainder is ACCEPTED (the hole) …
example : (certifySecurity heronMarrakesh Fd1 w2skipped).accepted = true := by decide
-- … whereas the circuit with the hidden gate visible hits F → REJECTED:
example : (certifySecurity heronMarrakesh Fd1 w2full).accepted = false := by decide
-- (and the buffered policy rejects it too — qubit 6 is adjacent to F = {3} anyway):
example : (certifySecurity heronMarrakesh (bufferF heronMarrakesh Fd1) w2full).accepted
    = false := by decide

/-! ## Buffer-radius k ablation, paper question E5 (isolation vs usable area)

Derivation order (honest): we fixed k = 1 on 2026-07-23, based on the documented
nearest-neighbour ZZ threat model. This choice came BEFORE the 2026-07-28 hardware
run. The measured leak (nonzero at d=1, null at d≥2) is *consistent with and
motivates* k=1, but it does not "predict" k=1. These counts show the
isolation/utilization tradeoff on the real patch. -/
#eval ((List.range 12).filter (bufferK heronMarrakesh Fd1 1)).length   -- k=1 sterilized count
#eval ((List.range 12).filter (bufferK heronMarrakesh Fd1 2)).length   -- k=2
#eval ((List.range 12).filter (bufferK heronMarrakesh Fd1 3)).length   -- k=3
#eval ((List.range 12).filter (bufferK heronMarrakesh Fd1 4)).length   -- k=4

end QpuCompiler
