/-
CertifyQASM.lean — real-circuit ingestion entry point (paper question E1).

This is the end-to-end path: OpenQASM-subset file(s) → untrusted `parseQASM` lexer →
`ofList` → trusted `certifySecurity` → per-file verdict. Device: the 12-node heavy-hex
ring (`heavyHex`). Tenant slot `A = {0..5}`. Forbidden co-tenant region `tenantF = {6..11}`.

The lexer is UNTRUSTED (basis subset {x, sx, id, rz, cz/cx}).

WARNING: this driver uses `parseQASM`, which is UNSOUND. It silently DROPS any
statement it does not recognize. As a result, a gate can disappear from the circuit.
For example, this happens when a classical guard hides the gate. The validator can then
accept the remainder as valid. The fuzz pass turned 269 of 1120 crafted inputs into
false accepts this way. For real evaluation, use `CertifyQASMSafe.lean`. This driver
stays in the repository only to reproduce the §E7/W2 before-and-after comparison.

Run (from qpu-compiler/ project root, after `lake build`):
  lake env lean --run harness/CertifyQASM.lean \
    harness/samples/*.qasm
-/
import QpuCompiler
open QpuCompiler

def certifyFile (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  let gates := parseQASM src
  let circ : UCom 12 := ofList gates
  let r := certifySecurity heavyHex tenantF circ
  let tag := if r.accepted then "ACCEPT" else "REJECT"
  IO.println s!"{tag}  {path}  (gates={gates.length} legal={r.hardwareLegal} confined={r.policyConfined})"

def main (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.println "usage: CertifyQASM <file.qasm> [more.qasm ...]"
  else
    IO.println "verdict  file  (parsed gate count, hardware-legal?, policy-confined?)"
    for p in args do certifyFile p
