/-
TimingBuffered.lean — cost of the BUFFERED policy on a full-size device.

`Timing.lean` benchmarks `certifySecurity` on `heavyHexFrag` (4 qubits, 3 edges) with
the bare region `fragF`. That configuration cannot show the thing the cost discussion
in Buffer.lean is actually about, because the buffered region's cost is driven by the
device size `n`, and n = 4 there.

This harness runs the real comparison on `dev_marrakesh` (n = 156, 176 edges):

  plain     : region = F_marrakesh                                   (Φ = O(1))
  bufferK   : region = bufferK dev_marrakesh F_marrakesh k           (Φ = Θ(n^k))
  bufferArrK: region = bufferMemo F (bufferArrK … k)                 (Φ = O(1) after build)

`bufferArrK_ext` proves the last two are the SAME FUNCTION, so any wall-clock gap
between them is pure representation cost, not a change of policy.

Run:  lake env lean --run harness/TimingBuffered.lean
(from the Artifact/ root, after `lake build`).
-/
import QpuCompiler
open QpuCompiler

/-- A `g`-gate chain of single-qubit X gates on qubit `q` of a 156-qubit device.
Each gate forces exactly one region query, which is what we are timing. -/
def genChain156 (q : Nat) : Nat → UCom 156
  | 0     => .app1 .id q
  | g + 1 => .seq (.app1 .x q) (genChain156 q g)

/-- Time one certification against a given region.

The `if verdict != true` is load-bearing, not a sanity check: `let verdict := …` only
builds a thunk, so without forcing it *between* the two clock reads the timer measures
thunk allocation and every configuration comes out at a few hundred nanoseconds
regardless of gate count. -/
def timeRegion (label : String) (region : Nat → Bool) (c : UCom 156) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let verdict := (certifySecurity dev_marrakesh region c).accepted
  if verdict != true then IO.eprintln s!"unexpected reject at {label}"
  let t1 ← IO.monoNanosNow
  IO.println s!"{label},{checkerSteps c},{t1 - t0},{verdict}"

def main : IO Unit := do
  -- Qubit 100 is well outside F_marrakesh = {16,22,23} and its small-k halo, so every
  -- configuration below ACCEPTS. We are timing the accept path, which is the one that
  -- must scan every gate (a reject can short-circuit).
  IO.println "# device: dev_marrakesh (n=156, 176 edges), F = {16,22,23}"
  IO.println s!"# blocked |bufferK 1| = {((List.range 156).filter (bufferK dev_marrakesh F_marrakesh 1)).length}"
  IO.println s!"# blocked |bufferK 2| = {((List.range 156).filter (bufferK dev_marrakesh F_marrakesh 2)).length}"
  IO.println "config,checker_steps,wall_ns,accepted"
  for g in [100, 1000, 10000] do
    let c := genChain156 100 g
    timeRegion s!"plain/g={g}" F_marrakesh c
    timeRegion s!"bufferK1/g={g}" (bufferK dev_marrakesh F_marrakesh 1) c
    timeRegion s!"bufferArrK1/g={g}"
      (bufferMemo F_marrakesh (bufferArrK dev_marrakesh F_marrakesh 1)) c
    timeRegion s!"bufferK2/g={g}" (bufferK dev_marrakesh F_marrakesh 2) c
    timeRegion s!"bufferArrK2/g={g}"
      (bufferMemo F_marrakesh (bufferArrK dev_marrakesh F_marrakesh 2)) c
  -- Memoisation makes larger k tractable at all; the unmemoised form is Θ(n^k).
  IO.println "# deeper k, memoised only (unmemoised bufferK 4 does not finish)"
  for k in [3, 4, 8] do
    let c := genChain156 100 1000
    timeRegion s!"bufferArrK{k}/g=1000"
      (bufferMemo F_marrakesh (bufferArrK dev_marrakesh F_marrakesh k)) c
