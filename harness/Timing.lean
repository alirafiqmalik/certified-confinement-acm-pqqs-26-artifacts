/-
Timing.lean — wall-clock timing harness (paper question E2).

This harness gives empirical support for the Θ(#gates) claim. It times `certifySecurity`
on `genLine g` (a g-gate CZ chain on the degree-3 fragment) for growing values of g.
It prints the exact `checkerSteps` count with the wall-clock time in nanoseconds. The
step count is the honest proxy, because the validator visits each gate once. The
wall-clock time confirms that the validator never touches the 2ⁿ state space. Cost tracks
the gate count, not the qubit count.

Run:  lake env lean --run harness/Timing.lean
(from the qpu-compiler/ project root, after `lake build`).
-/
import QpuCompiler
open QpuCompiler

/-- Time one certification. Returns (steps, nanoseconds). This forces the Bool verdict. -/
def timeOne (g : Nat) : IO (Nat × Nat) := do
  let c := genLine g
  let steps := checkerSteps c
  let t0 ← IO.monoNanosNow
  let verdict := (certifySecurity heavyHexFrag fragF c).accepted
  -- This forces the verdict, so the timer measures the real check, not thunk creation.
  if verdict != true then IO.eprintln s!"unexpected reject at g={g}"
  let t1 ← IO.monoNanosNow
  pure (steps, t1 - t0)

def main : IO Unit := do
  IO.println "gates_g,checker_steps,wall_ns"
  for g in [10, 100, 1000, 10000] do
    let (steps, ns) ← timeOne g
    IO.println s!"{g},{steps},{ns}"
