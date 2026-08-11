/-
CertifyQASMBuffered.lean — Axis-2 ingestion under the *buffered* confinement policy.

`CertifyQASMSafe.lean` certifies against the bare forbidden region `tenantF`. That is
the policy the checker can enforce. It is NOT the policy the paper recommends. A gate
one hop from a co-tenant qubit is where the measured crosstalk lives, and `tenantF`
allows it. This entry point closes that gap by certifying against the `k`-hop buffered
region.

Region: `bufferMemo tenantF (bufferArrK heavyHex tenantF k)`.

Two facts make this the right way to run it:

  * `bufferArrK_ext`            : the tabulated region IS `bufferK heavyHex tenantF k`
                                  (funext, not an approximation).
  * `certifySecurity_bufferArrK`: therefore the verdict matches the verdict that the
                                  unmemoized `bufferK` gives.

So the numbers this file produces are verdicts for the buffered *policy*, obtained at
the memoized *cost* (O(1) per region query after a Θ(k·n²) table build). Using
`bufferK` directly here costs Θ(nᵏ) per query — see the cost note in Buffer.lean.

Device: 12-node ring (`heavyHex`). Tenant A = {0..5}, F = {6..11}.
`k = 0` reproduces `CertifyQASMSafe.lean` exactly, since `bufferK g F 0 = F`.

Run (from the Artifact/ root, after `lake build`):
  lake env lean --run harness/CertifyQASMBuffered.lean <k> f1.qasm f2.qasm ...
-/
import QpuCompiler
open QpuCompiler

/-- The `k`-hop buffered forbidden region, built once as data. -/
def bufferedRegion (k : Nat) : Nat → Bool :=
  bufferMemo tenantF (bufferArrK heavyHex tenantF k)

def certifyFileBuffered (region : Nat → Bool) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match parseQASMSafe src with
  | none =>
      IO.println s!"REJECT-PARSE  {path}  (unrecognized support-bearing token)"
  | some gates =>
      let r := certifySecurity heavyHex region (ofList gates)
      let tag := if r.accepted then "ACCEPT" else "REJECT"
      IO.println s!"{tag}  {path}  (gates={gates.length} legal={r.hardwareLegal} confined={r.policyConfined})"

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "usage: CertifyQASMBuffered <k> file.qasm ..."
  | kStr :: paths =>
      let k := kStr.toNat!
      -- Build the region table ONCE, outside the file loop.
      let region := bufferedRegion k
      let blocked := (List.range 12).filter region
      IO.println s!"# buffered policy: k={k}  blocked={blocked}  (|blocked|={blocked.length}/12)"
      IO.println "verdict  file  (parsed gate count, hardware-legal?, policy-confined?)"
      for p in paths do certifyFileBuffered region p
