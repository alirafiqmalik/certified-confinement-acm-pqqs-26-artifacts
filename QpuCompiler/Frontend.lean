/-
QpuCompiler/Frontend.lean — OpenQASM-subset ingestion + §8.2 complexity artifact.

The lexer is an UNTRUSTED front-end. It turns an OpenQASM-subset string into a
`List GApp` (then `ofList` turns this list into a `UCom`). The lexer sits on the
*producer* side of the de-Bruijn architecture, next to the untrusted transpiler.
The lexer does not need a proof of correctness, because the trusted
`certifySecurity` checker validates the resulting circuit. This closes the
ingestion story: a QASM string goes in, and a `CertResult` comes out.

Two lexers share one classifier (`classifyStmt`). They differ only in their error
policy for a statement that the subset does not cover:

  * `parseQASMSafe` returns `none`, so the driver REJECTS the circuit. **Use this
    lexer.**
  * `parseQASM` silently drops the statement. This is UNSOUND. The §E3 fuzz pass
    turned 269 of 1120 crafted inputs into false accepts, through exactly this
    hole. The file keeps `parseQASM` only as the §E7/W2 counterexample.

Note on angles: OpenQASM `rz(θ)` gives θ in radians, often an irrational number
such as π/2. The rational-angle IR in this file cannot represent this value
exactly. The SECURITY certificate (`HWF` + confinement) depends ONLY on gate
*support* (which qubits a gate touches), not on angles. So the lexer records a
placeholder angle for `rz`. This placeholder is sound for the security check.
-/
import QpuCompiler.Confine

namespace QpuCompiler

/-! ## Untrusted OpenQASM-subset lexer

The basis-gate table exists in exactly ONE place: `gateOfSupportOnly`/`isGateTok`,
below. So adding a basis gate needs only one edit, and the two lexers cannot
drift apart. -/

/-- Parse a qubit operand `q[i]` (or a bare index) to `i`. -/
def parseQubit (s : String) : Option ℕ :=
  let t := s.trim
  match t.splitOn "[" with
  | [_, idx] => (idx.splitOn "]").head?.bind (fun x => x.trim.toNat?)
  | _        => t.toNat?

/-- Structural/header lines that carry no qubit support (safe to skip). -/
def isHeaderTok (g : String) : Bool :=
  g == "OPENQASM" || g == "include" || g == "creg" || g == "bit" || g == "barrier"
  || g == "gate" || g == "" || g.startsWith "qreg" || g.startsWith "qubit"
  || g.startsWith "//"   -- full-line comment: non-support-bearing, safe to skip

/-- Known basis-gate keyword. Must stay in step with `gateOfSupportOnly`. -/
def isGateTok (g : String) : Bool :=
  g == "x" || g == "sx" || g == "id" || g == "cz" || g == "cx" || g.startsWith "rz"

/-- Operands of a recognized basis gate map to a `GApp`. The result is `none` if the
operands are malformed (this means reject). This function runs only when
`isGateTok gate = true`, so the final case covers `cz`/`cx`.

**SUPPORT-ONLY — do not use this for functional or semantic equivalence checking.**
Every `rz(θ)` maps to `.rz 0`. The function DISCARDS the true angle from the QASM
source. It does not approximate the angle. This is sound for the security
certificate, because the certificate reads only gate *support* (which qubits a gate
touches — see the file-level note above). But the `GApp` value this function
returns is not a faithful copy of the source circuit.

Suppose a future caller needs the real angle, for example to check that the
compiled circuit still computes the same unitary as the source. Then this
function is the wrong starting point. It will silently produce a circuit that
denotes differently from the QASM input. -/
def gateOfSupportOnly (gate : String) (qs : List ℕ) : Option GApp :=
  if gate == "x" then qs.head?.map (fun q => .g1 .x q)
  else if gate == "sx" then qs.head?.map (fun q => .g1 .sx q)
  else if gate == "id" then qs.head?.map (fun q => .g1 .id q)
  else if gate.startsWith "rz" then qs.head?.map (fun q => .g1 (.rz 0) q)  -- angle discarded, not approximated: see docstring
  else match qs with | a :: b :: _ => some (.g2 a b) | _ => none  -- cz/cx

/-- Classify one statement. This function is the single source of truth for both
lexers. `none` means REJECT (an unrecognized or malformed support-bearing token,
for example `if(c==1)…`). `some none` means a recognized non-gate line (skip).
`some (some g)` means a gate. -/
def classifyStmt (s : String) : Option (Option GApp) :=
  match s.trim.splitOn " " with
  | []           => some none
  | gate :: rest =>
    if isHeaderTok gate then some none
    else if isGateTok gate then
      match gateOfSupportOnly gate (((String.intercalate " " rest).splitOn ",").filterMap parseQubit) with
      | some g => some (some g)
      | none   => none
    else none

/-- Parse one statement to a gate. This collapses both "skip" and "reject" to
`none` — that is, `classifyStmt` under the unsound error policy. -/
def parseStmt (s : String) : Option GApp := (classifyStmt s).join

/-- Drop a `//` line comment from one source line. Keep the text before it. -/
def stripComment (line : String) : String :=
  match line.splitOn "//" with
  | []          => line
  | before :: _ => before

/-- Split an OpenQASM source into statements.

ORDER MATTERS. This function splits on newline first. Then it removes the line
comment. Then it splits on `;`. An earlier version split on `;` first. That
version cut any `//` comment that contained a `;`, and left the tail of the
comment looking like a statement.

That version made `parseQASMSafe` reject
`samples/01_ok_confined.qasm`, whose comment reads `… slot A = {0..5}; all cz are
ring edges.`. The fragment `all cz are ring edges.` is an unrecognized
support-bearing token, so the sound lexer refused the whole file. The rejection
was in the safe direction, but it was a false reject on a positive sample. -/
def qasmStmts (src : String) : List String :=
  (src.splitOn "\n").flatMap (fun line => (stripComment line).splitOn ";")

/-! ### The two error policies over the shared classifier -/

/-- UNSOUND lexer: this function silently drops an unrecognized support-bearing
statement. So a gate hidden behind, for example, a classical guard vanishes, and
the remainder looks confined. The file keeps this lexer only as the §E7/W2
counterexample — see `parseQASMSafe`. -/
def parseQASM (src : String) : List GApp :=
  (qasmStmts src).filterMap parseStmt

/-- Sound (still untrusted) lexer: `none` means the certifier REJECTS. Any
unrecognized support-bearing token can now only cause a safe rejection, never a
silent skip. This restores the invariant that "a lexer gap can only cause a safe
rejection" for *skips*, not only for outright parse failures. -/
def parseQASMSafe (src : String) : Option (List GApp) :=
  (qasmStmts src).filterMapM classifyStmt

/-! ## End-to-end demonstration: QASM string → certificate -/

/-- A transpiled snippet confined to the tenant slot `A = {0,1,2}`. -/
def demoOK : String :=
"OPENQASM 3.0;
qubit[4] q;
x q[0];
sx q[1];
cz q[0], q[1];
rz(1.5707963267948966) q[0];"

/-- A transpiled snippet that touches the forbidden co-tenant qubit 3. -/
def demoBad : String := "x q[0]; cz q[0], q[3];"

-- The sound lexer produces the expected gate list (the angle is a placeholder):
#eval (parseQASMSafe demoOK).map (·.length)   -- some 4 (x, sx, cz, rz)
-- End-to-end: untrusted QASM string → ofList → trusted certifier → verdict.
#eval ((parseQASMSafe demoOK).map
        (fun gs => (certifySecurity heavyHexFrag fragF (ofList gs)).accepted))   -- some true
#eval ((parseQASMSafe demoBad).map
        (fun gs => (certifySecurity heavyHexFrag fragF (ofList gs)).accepted))   -- some false

/-! ## §8.2 — the checker's cost is polynomial and independent of 2ⁿ

`certifySecurity` equals `decide (HWF g ·)` combined with `confinedb (!F) ·`. Both
are structural folds. Each fold visits every gate once, with an O(1) per-gate
predicate (an edge lookup or a region-membership test). So the security
certificate costs Θ(#gates), INDEPENDENT of the 2ⁿ state space. This differs from
functional-equivalence checking, which costs Θ(2ⁿ) in the worst case
(QMA-complete). `checkerSteps` gives the exact per-gate work count, an honest
proxy for the polynomial cost.

CAVEAT: this Θ(#gates) figure assumes an O(1) region predicate. A *buffered*
region is not O(1) per query. See the cost accounting in `Buffer.lean`, which
also supplies the O(1) tabulated form. -/

/-- Number of gates the security checker inspects = the exact step count (a proxy for cost). -/
def checkerSteps {n : ℕ} : UCom n → ℕ
  | .seq c₁ c₂ => checkerSteps c₁ + checkerSteps c₂
  | .app1 _ _  => 1
  | .cz _ _    => 1

/-- The checker's work is additive over composition — the fold is linear in gate count. -/
theorem checkerSteps_seq {n : ℕ} (c₁ c₂ : UCom n) :
    checkerSteps (.seq c₁ c₂) = checkerSteps c₁ + checkerSteps c₂ := rfl

/-- A `g`-gate line circuit (a CZ chain on the fragment) for the feasibility demo. -/
def genLine : ℕ → UCom 4
  | 0     => .app1 .id 0
  | g + 1 => .seq (.cz 0 1) (genLine g)

-- Feasibility proxy: checker cost grows LINEARLY in #gates (here #qubits fixed at 4).
-- The same holds for any n. checkerSteps never references the 2ⁿ state space.
#eval checkerSteps (genLine 10)    -- 11
#eval checkerSteps (genLine 100)   -- 101
#eval checkerSteps (genLine 1000)  -- 1001
-- and the certifier runs on all of them (no 2ⁿ blowup):
#eval (certifySecurity heavyHexFrag fragF (genLine 1000)).accepted  -- true

/-! ## §E3 — the unsound skip, exhibited

`parseQASM` drops the guarded gate. `parseQASMSafe` rejects the statement it
cannot account for. This is the whole of the §E3 fix: one error policy, one
classifier. -/

-- the safe lexer REJECTS the conditioned-gate evasion …
#eval (parseQASMSafe "x q[6]; if(c==1) cz q[6],q[3];").isNone      -- true (SAFE)
-- … whereas the OLD lexer silently skips the guarded gate (the hole the fuzzer found):
#eval (parseQASM "x q[6]; if(c==1) cz q[6],q[3];").length          -- 1 (UNSOUND)

end QpuCompiler
