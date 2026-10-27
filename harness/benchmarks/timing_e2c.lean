import QpuCompiler
open QpuCompiler
def main (args : List String) : IO Unit := do
  for a in args do
    let n := a.toNat!
    let t0 ← IO.monoNanosNow
    let steps := checkerSteps (genLine n)           -- This forces a full O(n) traversal.
    let t1 ← IO.monoNanosNow
    IO.println s!"gates={n} steps={steps} us={(t1-t0)/1000}"
