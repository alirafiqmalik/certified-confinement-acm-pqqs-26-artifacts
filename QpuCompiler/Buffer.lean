/-
QpuCompiler/Buffer.lean — neighbour-buffered confinement (the adjacency gap).

## The gap

`confinedb A c` (Confine.lean) is a pure *gate-support* predicate. It rejects `c`
only when some gate of `c` acts on a qubit outside `A`. So certifying against the
complement of a forbidden region `F` catches exactly one thing: the
transpiler *routing a gate onto* a co-tenant qubit (the `.cz 0 3` money example).

It is **blind to adjacency**. A victim circuit whose support is entirely disjoint
from `F`, but which sits on a coupling *edge* next to `F`, is ACCEPTED — even
though that adjacency is exactly the physical precondition for the documented
nearest-neighbour crosstalk side channel on superconducting hardware.

## The fix

`bufferF g F` is `F` together with its 1-hop neighbourhood in the coupling graph
`g`. Certifying with `certifySecurity g (bufferF g F)` rejects any circuit that
so much as touches a qubit *adjacent* to the co-tenant region, and this closes the gap.
`bufferK g F k` iterates this to a `k`-hop buffer.

## Soundness story (important — read before citing)

`bufferF g F` is **just another decidable region argument**. `certifySecurity` and
`certifySecurity_sound` are already universally quantified over the region
(`∀ (F : ℕ → Bool)`). So instantiating them at `bufferF g F` is a *use* of the
existing theorem, not a new assumption:

  `certifySecurity_sound g (bufferF g F) ext : accepted → HWF g ext ∧
      confinedb (fun x => !bufferF g F x) ext = true`

Hence **no new soundness theorem is required**, and the trusted base is unchanged
(`certifySecurity_sound` remains `[propext]`). What the buffered instantiation buys
is a *stronger conclusion* — support avoids `F` **and** every neighbour of `F` —
for the same one-call, kernel-checked, Θ(#gates) price.

NOTE ON SCOPE: this is a *structural* guarantee (no shared qubit, no shared edge).
It is not a bound on physical crosstalk magnitude. See HARDWARE-DEMO-PLAN.md.
-/
import QpuCompiler.Confine
import QpuCompiler.DeviceLib

namespace QpuCompiler

/-! ## The buffered region -/

/-- `bufferF g F` = the forbidden region `F` together with every qubit adjacent to
`F` in the coupling graph `g` (a 1-hop buffer). Decidable and computable: the
neighbour search ranges over `List.range n`, and `g.edge x y = true → y < n`, so
no neighbour is missed. -/
def bufferF {n : ℕ} (g : Coupling n) (F : ℕ → Bool) : ℕ → Bool :=
  fun x => F x || (List.range n).any (fun y => F y && g.edge x y)

/-- `k`-hop buffer: iterate the 1-hop neighbourhood `k` times.
`bufferK g F 0 = F` and `bufferK g F 1 = bufferF g F`. -/
def bufferK {n : ℕ} (g : Coupling n) (F : ℕ → Bool) : ℕ → ℕ → Bool
  | 0     => F
  | k + 1 => bufferF g (bufferK g F k)

/-- The buffer contains the forbidden region: buffering only ever *tightens* the
policy, so an accepted buffered certificate implies the unbuffered one. -/
theorem F_subset_bufferF {n : ℕ} (g : Coupling n) (F : ℕ → Bool) {x : ℕ}
    (h : F x = true) : bufferF g F x = true := by
  simp [bufferF, h]

/-- A qubit adjacent to a forbidden qubit is in the buffer — the property the
support-only predicate misses. -/
theorem adj_mem_bufferF {n : ℕ} (g : Coupling n) (F : ℕ → Bool) {x y : ℕ}
    (hy : F y = true) (hxy : g.edge x y = true) : bufferF g F x = true := by
  have hy_lt : y < n := (g.edge_bounds x y hxy).2
  simp only [bufferF, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨y, by simp [List.mem_range, hy_lt], by simp [hy, hxy]⟩

/-! ## A heavy-hex device patch with genuine degree-3 sites

The patch has one heavy hexagon (the 12-cycle `0..11`: six site qubits and six flag
qubits), plus two bridge qubits, `12` and `13`, that stub out toward neighbouring
hexagons. The bridges give qubits `1` and `8` **degree 3** — the distinguishing
heavy-hex feature that a plain ring (max degree 2) cannot show.

The patch is encoded through `EdgeSpec` (`DeviceLib.lean`), so `edge_symm`/`edge_irrefl`/
`edge_bounds` come from the generic construction instead of three per-device proofs. -/

/-- Canonical edge list: the 12-cycle `0..11`, plus the bridges `1–12` and `8–13`. -/
def specHeronPatch : EdgeSpec 14 where
  edges := [(0,1), (1,2), (2,3), (3,4), (4,5), (5,6), (6,7), (7,8), (8,9), (9,10),
            (10,11), (0,11), (1,12), (8,13)]
  ordered_all := by decide
  bounded_all := by decide

def heronPatch : Coupling 14 := specHeronPatch.toCoupling

-- Genuine degree-3 heavy-hex sites (unlike the C₁₂ ring's max degree 2):
example : heronPatch.edge 8 7 = true ∧ heronPatch.edge 8 9 = true
    ∧ heronPatch.edge 8 13 = true := by decide
example : heronPatch.edge 1 0 = true ∧ heronPatch.edge 1 2 = true
    ∧ heronPatch.edge 1 12 = true := by decide
-- the three neighbours of the degree-3 site are not interconnected:
example : heronPatch.edge 7 9 = false ∧ heronPatch.edge 7 13 = false := by decide

/-! ## The co-tenant policy and two victim placements -/

/-- Forbidden co-tenant region: the arc `{9, 10, 11}` of the hexagon. -/
def patchF : ℕ → Bool := fun q => decide (9 ≤ q ∧ q < 12)

/-- Victim placed **adjacent** to the co-tenant region: its support `{7, 8}` is
disjoint from `F = {9,10,11}`, but qubit `8` shares the coupling edge `(8,9)` with
`F` — and `8` is a genuine degree-3 site. -/
def vAdj : UCom 14 := .seq (.app1 .x 7) (.cz 7 8)

/-- Victim placed **far** from the co-tenant region: support `{4, 5}`, ≥ 2 hops
from every forbidden qubit. -/
def vFar : UCom 14 := .seq (.app1 .x 4) (.cz 4 5)

/-! ## The gap, and the fix — kernel-checked

Each `example` below is proved `by decide`, so these are kernel-checked facts, not
merely evaluations. The `#eval`s print the same verdicts for the record. -/

-- The buffer is exactly `F` plus its neighbours `{0, 8}`:
#eval (List.range 14).filter (bufferF heronPatch patchF)
example : (List.range 14).filter (bufferF heronPatch patchF) = [0, 8, 9, 10, 11] := by decide

-- (1) THE GAP — support-only confinement ACCEPTS the adjacent placement:
#eval (certifySecurity heronPatch patchF vAdj).accepted
example : (certifySecurity heronPatch patchF vAdj).accepted = true := by decide

-- (2) THE FIX — the neighbour-buffered policy REJECTS it (same driver, same proof):
#eval (certifySecurity heronPatch (bufferF heronPatch patchF) vAdj).accepted
example : (certifySecurity heronPatch (bufferF heronPatch patchF) vAdj).accepted = false := by
  decide

-- (3) NO OVER-BLOCKING — a genuinely distant placement is still ACCEPTED:
#eval (certifySecurity heronPatch (bufferF heronPatch patchF) vFar).accepted
example : (certifySecurity heronPatch (bufferF heronPatch patchF) vFar).accepted = true := by
  decide

-- The rejection is on the *policy* check, not hardware legality: the adjacent
-- placement is perfectly hardware-legal (7–8 is a real coupling edge).
#eval (certifySecurity heronPatch (bufferF heronPatch patchF) vAdj).hardwareLegal
example : (certifySecurity heronPatch (bufferF heronPatch patchF) vAdj).hardwareLegal = true := by
  decide

-- A 2-hop buffer additionally excludes qubit 7, so even `vAdj`'s *other* qubit is
-- covered. `vFar` (support {4,5}) is far enough to survive buffers up to 3 hops, and
-- is only rejected at 4 hops. That is, the policy knob trades isolation against usable
-- area, and on this patch a 4-hop buffer already sterilises most of the device.
#eval (List.range 14).filter (bufferK heronPatch patchF 2)  -- [0,1,7,8,9,10,11,13]
example : (certifySecurity heronPatch (bufferK heronPatch patchF 2) vFar).accepted = true := by
  decide
example : (certifySecurity heronPatch (bufferK heronPatch patchF 3) vFar).accepted = true := by
  decide
example : (certifySecurity heronPatch (bufferK heronPatch patchF 4) vFar).accepted = false := by
  decide

/-! ## Buffered preservation through the COMPILE pipeline (closing the composition gap)

The one-shot certifier story above only covers *externally supplied* circuits. The
pipeline preservation theorems (`route_hh_confine`, `optimize_conf`,
`compile_hh_confine_correct`) are stated for the plain support predicate. But they
are already **universally quantified over the region** (`{A F : ℕ → Bool}`), exactly
like `certifySecurity_sound`. So we obtain the buffered pipeline guarantee by
*instantiating* them at `A := fun x => !bufferF g F x` and `F := bufferF g F`. This is
a use of the existing theorems: no new assumption, and no new trusted base.

The content: if the source satisfies the **buffered** client policy (every gate, and
every routed `cz`'s `findPath`, avoids `F` *and every qubit adjacent to `F`*), then
the fully compiled circuit `optimize (route_hh c)` still touches neither `F` nor any
neighbour of `F`. That is, compilation cannot move a secret into the forbidden region
*or onto any qubit adjacent to it*, which is the nearest-neighbour ZZ precondition.
-/

/-- Monotonicity of the support predicate in the allowed region. -/
theorem confinedb_mono {A B : ℕ → Bool} {n : ℕ} (hAB : ∀ x, A x = true → B x = true) :
    ∀ {c : UCom n}, confinedb A c = true → confinedb B c = true := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro h
    simp only [confinedb, Bool.and_eq_true] at h ⊢
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | app1 g q => intro h; cases g <;> simp_all [confinedb]
  | cz a b =>
    intro h
    simp only [confinedb, Bool.and_eq_true] at h ⊢
    exact ⟨hAB a h.1, hAB b h.2⟩

/-- Buffered confinement is **strictly stronger** than plain confinement: avoiding
`F` and its neighbourhood implies avoiding `F`. -/
theorem confinedb_buffered_imp_plain {m n : ℕ} (g : Coupling m) (F : ℕ → Bool) {c : UCom n}
    (h : confinedb (fun x => !bufferF g F x) c = true) :
    confinedb (fun x => !F x) c = true := by
  refine confinedb_mono (fun x hx => ?_) h
  simp only [Bool.not_eq_true'] at hx ⊢
  by_contra hF
  exact absurd (F_subset_bufferF g F (by simpa using hF)) (by simp [hx])

/-! The per-stage buffered statements need no theorems of their own. `route_hh_confine`
and `optimize_conf` are already `∀ (A : ℕ → Bool)`. So the buffered forms are those
theorems *applied* at `A := fun x => !bufferF g F x`. Write
`route_hh_confine (A := fun x => !bufferF g F x) hpol` at the use site. If we name
them, we dress an instantiation up as a result — the opposite of this file's
argument. Only the composed end-to-end statements below earn names. -/

/-- **BUFFERED COMPILE-PRESERVATION.** A well-formed source that is routable within
the *neighbour-buffered* complement of `F` compiles (route + optimize) to a circuit
that is hardware-legal, equal to the source up to global phase, and touches neither
`F` **nor any qubit adjacent to `F`**. This is `compile_hh_confine_correct`
instantiated at the buffered region — no new axioms, no new trusted base. -/
theorem compile_hh_confine_buffered {m : ℕ} (g : Coupling m) (F : ℕ → Bool) {c : UCom 12}
    (h : WF c) (hpol : routableb (fun x => !bufferF g F x) c = true) :
    HWF heavyHex (optimize (route_hh c))
      ∧ UCom.CongPhase (optimize (route_hh c)) c
      ∧ confinedb (fun x => !bufferF g F x) (optimize (route_hh c)) = true :=
  compile_hh_confine_correct (F := bufferF g F) h hpol (by intro x hx; simpa using hx)

/-- The `k`-hop version of `compile_hh_confine_buffered`. -/
theorem compile_hh_confine_bufferedK {m : ℕ} (g : Coupling m) (F : ℕ → Bool) (k : ℕ)
    {c : UCom 12} (h : WF c) (hpol : routableb (fun x => !bufferK g F k x) c = true) :
    HWF heavyHex (optimize (route_hh c))
      ∧ UCom.CongPhase (optimize (route_hh c)) c
      ∧ confinedb (fun x => !bufferK g F k x) (optimize (route_hh c)) = true :=
  compile_hh_confine_correct (F := bufferK g F k) h hpol (by intro x hx; simpa using hx)

/-- **Pipeline output passes the buffered certifier.** Composes the compile-level
guarantee with the one-call driver: our own compiler's output is ACCEPTED by the
same `certifySecurity` used on untrusted external transpilers. -/
theorem certify_compile_hh_buffered (F : ℕ → Bool) {c : UCom 12}
    (h : WF c) (hpol : routableb (fun x => !bufferF heavyHex F x) c = true) :
    (certifySecurity heavyHex (bufferF heavyHex F) (optimize (route_hh c))).accepted = true := by
  obtain ⟨hHWF, _, hconf⟩ := compile_hh_confine_buffered heavyHex F h hpol
  simp only [CertResult.accepted, certifySecurity, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hHWF, hconf⟩

/-! ### Kernel-checked witnesses that the composed statement BITES

The compile pipeline targets `heavyHex : Coupling 12` (the C₁₂ heavy-hex unit cell).
On qubits `0..11` the demo patch `heronPatch` induces exactly those edges, so the two
devices give the *same* buffered region for `patchF = {9,10,11}` — namely
`{0, 8, 9, 10, 11}` (checked below), and both are used interchangeably here.

CAVEAT (matches the pre-existing note in `EvalWitnesses.lean`): `optimize`/`optFix`
use well-founded recursion that the kernel `decide` cannot reduce, so *negative*
verdicts about post-`optimize` circuits stay `#eval` witnesses. Positive post-`optimize`
verdicts are obtained here from the theorems above with `by decide` hypotheses, which
IS kernel-checked end to end. -/

/-- Source placed ≥ 2 hops from `patchF = {9,10,11}`: support/route `{2,3,4,5}`. -/
def srcFar : UCom 12 := .seq (.app1 .x 2) (.cz 2 5)
/-- Source placed **adjacent** to `patchF`: qubit 8 shares the edge `(8,9)` with `F`. -/
def srcAdj : UCom 12 := .seq (.app1 .x 7) (.cz 7 8)

-- the compile target and the demo patch induce the same buffered region on `0..11`:
example : (List.range 12).filter (bufferF heronPatch patchF)
        = (List.range 12).filter (bufferF heavyHex patchF) := by decide
example : (List.range 12).filter (bufferF heavyHex patchF) = [0, 8, 9, 10, 11] := by decide

-- (A) the buffered client policy ACCEPTS the far source …
example : routableb (fun x => !bufferF heronPatch patchF x) srcFar = true := by decide
example : WF srcFar := by decide
-- … and the FULLY COMPILED output is still buffered-confined (kernel-checked via the
-- theorem: both hypotheses are `by decide`):
example : confinedb (fun x => !bufferF heronPatch patchF x) (optimize (route_hh srcFar)) = true :=
  (compile_hh_confine_buffered heronPatch patchF (c := srcFar) (by decide) (by decide)).2.2
example : (certifySecurity heavyHex (bufferF heavyHex patchF)
    (optimize (route_hh srcFar))).accepted = true :=
  certify_compile_hh_buffered patchF (c := srcFar) (by decide) (by decide)

-- (B) THE GAP, end-to-end through the compiler: the PLAIN policy admits the adjacent
-- source and accepts its routed output …
example : routableb (fun x => !patchF x) srcAdj = true := by decide
example : (certifySecurity heavyHex patchF (route_hh srcAdj)).accepted = true := by decide
-- … while the BUFFERED policy rejects it at the front door and on the routed output:
example : routableb (fun x => !bufferF heronPatch patchF x) srcAdj = false := by decide
example : confinedb (fun x => !bufferF heronPatch patchF x) (route_hh srcAdj) = false := by decide
example : (certifySecurity heavyHex (bufferF heavyHex patchF) (route_hh srcAdj)).accepted
    = false := by decide
-- post-`optimize` rejection: `#eval` only (kernel cannot reduce `optFix` — see caveat):
#eval (certifySecurity heavyHex patchF (optimize (route_hh srcAdj))).accepted            -- true (GAP)
#eval (certifySecurity heavyHex (bufferF heavyHex patchF)
        (optimize (route_hh srcAdj))).accepted                                           -- false (FIX)

/-! ## Cost: the buffered region is NOT O(1) per query — and a precomputed fix

HONEST COST ACCOUNTING (this corrects the "Θ(#gates)" phrasing when a *buffered*
region is used). Write `E` for the cost of one `g.edge` query and `Φ` for the cost of
one `F` query. `certifySecurity` visits every gate once, and per gate it performs O(1)
region queries and O(1) edge queries. So its cost is

  Θ(#gates · (Φ + E))   — with a cheap region (`Φ = O(1)`) this is Θ(#gates).

But `bufferF g F` is `fun x => F x || (List.range n).any (fun y => F y && g.edge x y)`.
Each *query* allocates `List.range n` and scans it, so `Φ_bufferF = Θ(n · (Φ + E))`,
giving a total of Θ(#gates · n · (Φ + E)). Worse, `bufferK g F (k+1) x` re-evaluates
`bufferK g F k` at the point `x` **and** at all `n` scanned neighbours, so
`Φ_bufferK(k) = Θ(n^k · (Φ + E))` — exponential in `k`, not linear.
`checkerSteps` counts gates only and never evaluates the region predicate, so it is
blind to all of this: it is a *gate-traversal* count, not a cost model.

FIX: build the region once into an `Array Bool` (`bufferArr`) and query it in
O(1) (`bufferMemo`). Building the table costs Θ(n² · (Φ + E)) edge queries (the
`Coupling` interface exposes only `edge : ℕ → ℕ → Bool`, so we must find neighbours
by scanning — with an adjacency-list device model, the cost is Θ(n · deg)). Total:

  Θ(n² · (Φ + E) + #gates) for k = 1,  Θ(k · n² · (Φ + E) + #gates) for a k-hop buffer.

That is, the per-gate cost is back to O(1), and the `n`-dependence is a one-off
preprocessing term. `bufferMemo_ext` / `bufferArrK_ext` prove that the memoised region
is *the same function*, so `certifySecurity_bufferMemo` / `certifySecurity_bufferArrK`
give the identical verdict. The existing `bufferF`/`bufferK` definitions are untouched. -/

/-- Precomputed 1-hop buffer table over the device range `0..n-1`. -/
def bufferArr {n : ℕ} (g : Coupling n) (F : ℕ → Bool) : Array Bool :=
  (Array.range n).map (bufferF g F)

/-- A region backed by a precomputed table: O(1) per query inside the device range,
falling through to `F` outside it (where `bufferF` coincides with `F`). -/
def bufferMemo (F : ℕ → Bool) (t : Array Bool) : ℕ → Bool :=
  fun x => if h : x < t.size then t[x] else F x

/-- Outside the device range the buffer adds nothing: `g.edge x y = true → x < n`. -/
theorem bufferF_of_ge {n : ℕ} (g : Coupling n) (F : ℕ → Bool) {x : ℕ} (hx : n ≤ x) :
    bufferF g F x = F x := by
  have hedge : ∀ y, g.edge x y = false := by
    intro y
    cases h : g.edge x y with
    | false => rfl
    | true => exact absurd (g.edge_bounds x y h).1 (by omega)
  simp [bufferF, hedge]

theorem bufferMemo_eq {n : ℕ} (g : Coupling n) (F : ℕ → Bool) (x : ℕ) :
    bufferMemo F (bufferArr g F) x = bufferF g F x := by
  unfold bufferMemo
  split
  · next h => simp [bufferArr]
  · next h =>
      have hx : n ≤ x := by simp only [bufferArr, Array.size_map, Array.size_range] at h; omega
      exact (bufferF_of_ge g F hx).symm

/-- The memoised region is **the same function** as `bufferF g F`. -/
theorem bufferMemo_ext {n : ℕ} (g : Coupling n) (F : ℕ → Bool) :
    bufferMemo F (bufferArr g F) = bufferF g F :=
  funext (bufferMemo_eq g F)

/-- Hence the certifier returns the **identical verdict** with the cheap region. -/
theorem certifySecurity_bufferMemo {n : ℕ} (g : Coupling n) (F : ℕ → Bool) (ext : UCom n) :
    certifySecurity g (bufferMemo F (bufferArr g F)) ext
      = certifySecurity g (bufferF g F) ext := by
  rw [bufferMemo_ext]

/-! ### `k`-hop memoisation: the table must be a DATA value, not a function

MEASURED PITFALL (worth stating in the paper). The obvious recursion

  `def bad (g) (F) : ℕ → (ℕ → Bool) | 0 => F | k+1 => let p := bad g F k; bufferMemo p (bufferArr g p)`

is *slower than the unmemoised `bufferK`*. Its result type ends in a function, so the
compiler eta-expands it, and `bad g F k` becomes a partial application. The whole
table tower is then rebuilt on **every single query**. Measured on `heronPatch` (n = 14) via
`#eval`: `bufferK … 4` scanned over `0..13` returns instantly, while the eta-expanded
"memo" at k = 4 does not finish in 120 s.

The fix is to make the recursion return **data** (`Array Bool`), which cannot be
eta-expanded, and to hand the finished table to `bufferMemo` at the use site. Then
k = 200 is instant. -/

theorem bufferMemo_map {n : ℕ} (F A : ℕ → Bool) (x : ℕ) :
    bufferMemo F ((Array.range n).map A) x = if x < n then A x else F x := by
  unfold bufferMemo
  split
  · next h =>
      have hx : x < n := by simpa [Array.size_map, Array.size_range] using h
      simp [Array.getElem_map, Array.getElem_range, hx]
  · next h =>
      have hx : ¬ x < n := by simpa [Array.size_map, Array.size_range] using h
      simp [hx]

theorem bufferK_of_ge {n : ℕ} (g : Coupling n) (F : ℕ → Bool) {x : ℕ} (hx : n ≤ x) :
    ∀ k, bufferK g F k x = F x
  | 0     => rfl
  | k + 1 => by
      simp only [bufferK]
      rw [bufferF_of_ge g _ hx, bufferK_of_ge g F hx k]

/-- `k`-hop buffer built as one table per hop. Returns **data**, so each level
is built exactly once. `bufferMemo F (bufferArrK g F k)` is then O(1) per query. -/
def bufferArrK {n : ℕ} (g : Coupling n) (F : ℕ → Bool) : ℕ → Array Bool
  | 0     => (Array.range n).map F
  | k + 1 => (Array.range n).map (bufferF g (bufferMemo F (bufferArrK g F k)))

theorem bufferArrK_eq {n : ℕ} (g : Coupling n) (F : ℕ → Bool) :
    ∀ (k x : ℕ), bufferMemo F (bufferArrK g F k) x = bufferK g F k x
  | 0, x => by rw [bufferArrK, bufferMemo_map]; split <;> rfl
  | k + 1, x => by
      have ih : bufferMemo F (bufferArrK g F k) = bufferK g F k :=
        funext (bufferArrK_eq g F k)
      rw [bufferArrK, bufferMemo_map, ih]
      split
      · rfl
      · next h => exact (bufferK_of_ge g F (by omega) (k + 1)).symm

/-- The tabulated `k`-hop region is **the same function** as `bufferK g F k`. -/
theorem bufferArrK_ext {n : ℕ} (g : Coupling n) (F : ℕ → Bool) (k : ℕ) :
    bufferMemo F (bufferArrK g F k) = bufferK g F k :=
  funext (bufferArrK_eq g F k)

/-- Hence the certifier returns the **identical verdict** with the tabulated `k`-hop region. -/
theorem certifySecurity_bufferArrK {n : ℕ} (g : Coupling n) (F : ℕ → Bool) (k : ℕ)
    (ext : UCom n) :
    certifySecurity g (bufferMemo F (bufferArrK g F k)) ext
      = certifySecurity g (bufferK g F k) ext := by
  rw [bufferArrK_ext]

-- same region, same verdicts. The `decide`s go through the extensionality theorems,
-- because `Array.range`/`Array.map` are not kernel-reducible either.
#eval (List.range 14).filter (bufferMemo patchF (bufferArr heronPatch patchF))    -- [0,8,9,10,11]
#eval (List.range 14).filter (bufferMemo patchF (bufferArrK heronPatch patchF 2)) -- = bufferK … 2
#eval ((List.range 14).filter (bufferMemo patchF (bufferArrK heronPatch patchF 200))).length -- 14
example : (certifySecurity heronPatch (bufferMemo patchF (bufferArr heronPatch patchF))
    vAdj).accepted = false := by rw [certifySecurity_bufferMemo]; decide
example : (certifySecurity heronPatch (bufferMemo patchF (bufferArr heronPatch patchF))
    vFar).accepted = true := by rw [certifySecurity_bufferMemo]; decide
example : (certifySecurity heronPatch (bufferMemo patchF (bufferArrK heronPatch patchF 4))
    vFar).accepted = false := by rw [certifySecurity_bufferArrK]; decide

end QpuCompiler
