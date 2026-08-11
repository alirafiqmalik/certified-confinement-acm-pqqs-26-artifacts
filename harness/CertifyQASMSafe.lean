/-
CertifyQASMSafe.lean — Axis-2 ingestion with the SOUND lexer `parseQASMSafe` (§E3).
`CertifyQASM.lean` uses `parseQASM` and silently skips unrecognized tokens. This file
is different: it rejects any circuit with an unrecognized *support-bearing* statement.
`parseQASMSafe = none` means REJECT-PARSE. Device: 12-node ring. Tenant A={0..5}, F={6..11}.

Run (from qpu-compiler/ root, after `lake build`):
  lake env lean --run harness/CertifyQASMSafe.lean f1.qasm f2.qasm ...
-/
import QpuCompiler
open QpuCompiler

-- The device and tenant slot come from the library (`heavyHex`, `tenantF`). These are
-- the same objects that `CertifyQASM.lean` uses. This file previously declared its own
-- `ring12` and `tenantF12`. They had the same graph and region, but nothing checked
-- this fact. As a result, the old-lexer and new-lexer comparison also varied the device.
def certifyFileSafe (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match parseQASMSafe src with
  | none =>
      IO.println s!"REJECT-PARSE  {path}  (unrecognized support-bearing token)"
  | some gates =>
      let r := certifySecurity heavyHex tenantF (ofList gates)
      let tag := if r.accepted then "ACCEPT" else "REJECT"
      IO.println s!"{tag}  {path}  (gates={gates.length} legal={r.hardwareLegal} confined={r.policyConfined})"

def main (args : List String) : IO Unit := do
  IO.println "verdict  file  (parsed gate count, hardware-legal?, policy-confined?)"
  for p in args do certifyFileSafe p
