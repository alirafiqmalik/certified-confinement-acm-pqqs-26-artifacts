/-
QpuCompiler/CompileHH.lean — iteration 14: the HEAVY-HEX end-to-end compiler.

`heavyHex : Coupling 12` is the heavy-hex unit-cell ring: the cycle graph C₁₂.
Sites sit at even indices, flags at odd indices, wired 0–1–…–11–0. A verified-total
path finder (the `findPath` table, with `findPath_valid` by `decide`) clears the
symbolic routing crux. `routeCZ_hh` recovers the cons-cons shape and invariants
generically. It delegates to the banked `routeEdge_HWF`/`routeEdge_congPhase`.
Assembly is a line-for-line copy of i09 `Compile.lean` (routeCZ→routeCZ_hh,
lnnPath n→heavyHex).
-/
import QpuCompiler.RouteEdge
import QpuCompiler.Hardware

namespace QpuCompiler

open scoped QpuCompiler

/-! ## (a) `heavyHex : Coupling 12` — the cycle graph C₁₂ -/

/-- The heavy-hex unit-cell ring = the 12-cycle `0–1–…–11–0`. Edge predicate is a
single arithmetic `decide` (cheap Nat comparisons, no list membership) to keep the
kernel `decide` on `findPath_valid` tractable. -/
def heavyHex : Coupling 12 where
  edge a b := decide ((a + 1 = b ∨ b + 1 = a ∨ (a = 0 ∧ b = 11) ∨ (a = 11 ∧ b = 0))
                       ∧ a < 12 ∧ b < 12)
  edge_symm := by intro a b; rw [decide_eq_decide]; omega
  edge_irrefl := by intro a; simp only [decide_eq_false_iff_not]; omega
  edge_bounds := by
    intro a b h; simp only [decide_eq_true_eq] at h; exact ⟨h.2.1, h.2.2⟩

/-! ### CP0 smoke -/

example : IsEdgePath heavyHex [0, 1, 2, 3, 4, 5, 6] := by unfold IsEdgePath; decide

/-! ### CP1 (FLOOR) — a concrete distant-`cz` witness on genuine heavy-hex -/

example : HWF heavyHex (routeEdge 12 [0, 1, 2, 3, 4, 5, 6]) :=
  routeEdge_HWF (by omega) (by unfold IsEdgePath; decide)

example : UCom.CongPhase (routeEdge 12 [0, 1, 2, 3, 4, 5, 6]) (.cz 0 6) := by
  have := routeEdge_congPhase (n := 12) (g := heavyHex) (v0 := 0) (v1 := 1)
    (rest := [2, 3, 4, 5, 6]) (by omega) (by unfold IsEdgePath; decide) (by decide)
  simpa using this

/-! ## (b) path table + `findPath` + `pathValid` + `findPath_valid` -/

/-- Offline-searched (untrusted) path table: the ascending or descending arc of
the 12-cycle from `a` to `b`. Verified total-and-valid by `findPath_valid`. -/
def findPath : ℕ → ℕ → List ℕ
  | a, b => if a < b then List.range' a (b - a + 1)
            else if b < a then (List.range' b (a - b + 1)).reverse
            else []

/-- Bool mirror of `IsEdgePath` (avoids `Decidable (IsEdgePath …)` synthesis and
keeps the `findPath_valid` kernel reduction all-Bool and cheap). -/
def isEdgePathb {n} (g : Coupling n) : List ℕ → Bool
  | u :: v :: rest => g.edge u v && isEdgePathb g (v :: rest)
  | _              => true

theorem isEdgePathb_iff {n} (g : Coupling n) (p : List ℕ) :
    isEdgePathb g p = true ↔ IsEdgePath g p := by
  induction p with
  | nil => simp [isEdgePathb, IsEdgePath]
  | cons u rest ih =>
    cases rest with
    | nil => simp [isEdgePathb, IsEdgePath]
    | cons v rest =>
      rw [isEdgePathb, Bool.and_eq_true, ih]
      unfold IsEdgePath
      rw [List.isChain_cons_cons]

/-- Boolean validity of the table entry: length ≥ 2, correct endpoints, is a
heavy-hex edge-path, and simple (start not revisited). -/
def pathValid (a b : ℕ) : Bool :=
  let p := findPath a b
  decide (2 ≤ p.length)
    && (p.head? == some a) && (p.getLast? == some b)
    && isEdgePathb heavyHex p && decide (a ∉ p.tail)

set_option maxHeartbeats 1000000 in
theorem findPath_valid : ∀ a b : Fin 12, a ≠ b → pathValid a b = true := by decide

/-! ## (c) `routeCZ_hh` + generic shape recovery + universal HWF/congPhase -/

/-- Route a single `cz a b` on heavy-hex via the table path. -/
def routeCZ_hh (a b : ℕ) : UCom 12 := routeEdge 12 (findPath a b)

/-- Recover the cons-cons shape and all routing invariants for `findPath a b`
generically from `findPath_valid` (no per-pair case split). -/
theorem routeCZ_hh_shape {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b) :
    ∃ y rest, findPath a b = a :: y :: rest
      ∧ IsEdgePath heavyHex (a :: y :: rest)
      ∧ a ∉ (y :: rest)
      ∧ (y :: rest).getLast (by simp) = b := by
  have hv : pathValid a b = true := by
    have := findPath_valid ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [Fin.ext_iff] using hab)
    simpa using this
  unfold pathValid at hv
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨hlen, hhd⟩, hlast⟩, hchain⟩, htail⟩ := hv
  rcases hfp : findPath a b with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · rw [hfp] at hlen; simp at hlen
  · rw [hfp] at hlen; simp at hlen
  · rw [hfp] at hhd; rw [List.head?_cons, Option.some.injEq] at hhd; subst hhd
    refine ⟨y, rest, rfl, ?_, ?_, ?_⟩
    · rw [hfp] at hchain; exact (isEdgePathb_iff heavyHex _).mp hchain
    · have := htail; rw [hfp] at this; simpa using this
    · rw [hfp] at hlast
      rw [List.getLast?_eq_some_getLast (by simp), Option.some_inj] at hlast
      rw [← List.getLast_cons_cons (a := x)]
      exact hlast

theorem routeCZ_hh_HWF {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b) :
    HWF heavyHex (routeCZ_hh a b) := by
  obtain ⟨y, rest, hpath, hchain, _, _⟩ := routeCZ_hh_shape ha hb hab
  unfold routeCZ_hh; rw [hpath]; exact routeEdge_HWF (by omega) hchain

theorem routeCZ_hh_congPhase {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b) :
    UCom.CongPhase (routeCZ_hh a b) (.cz a b) := by
  obtain ⟨y, rest, hpath, hchain, hsimple, hlast⟩ := routeCZ_hh_shape ha hb hab
  unfold routeCZ_hh; rw [hpath]
  have := routeEdge_congPhase (n := 12) (g := heavyHex) (by omega) hchain hsimple
  rwa [hlast] at this

/-! ## (d) full routing pass + end-to-end heavy-hex compiler (i09 copy) -/

/-- Route an entire circuit on heavy-hex: recurse structurally, sending each `cz`
through `routeCZ_hh`. -/
def route_hh : UCom 12 → UCom 12
  | .seq c₁ c₂ => .seq (route_hh c₁) (route_hh c₂)
  | .app1 g q  => .app1 g q
  | .cz a b    => routeCZ_hh a b

theorem route_hh_HWF {c : UCom 12} (h : WF c) : HWF heavyHex (route_hh c) := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | app1 hq => exact .app1 hq
  | cz ha hb hab => exact routeCZ_hh_HWF ha hb hab

theorem route_hh_congPhase {c : UCom 12} (h : WF c) : UCom.CongPhase (route_hh c) c := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact UCom.CongPhase.seq_congr ih₁ ih₂
  | app1 => exact UCom.CongPhase.refl _
  | cz ha hb hab => exact routeCZ_hh_congPhase ha hb hab

theorem routeOpt_hh_HWF {c : UCom 12} (h : WF c) :
    HWF heavyHex (optimize (route_hh c)) := optimize_HWF (route_hh_HWF h)

theorem routeOpt_hh_congPhase {c : UCom 12} (h : WF c) :
    UCom.CongPhase (optimize (route_hh c)) c :=
  ((optimize_sound (route_hh_HWF h).toWF).toCongPhase).trans (route_hh_congPhase h)

/-- **HEADLINE (i14).** Any well-formed circuit compiles (route + optimize) to a
heavy-hex-legal circuit provably equivalent to the source up to a global phase. -/
theorem compile_correct_hh {c : UCom 12} (h : WF c) :
    HWF heavyHex (optimize (route_hh c)) ∧ UCom.CongPhase (optimize (route_hh c)) c :=
  ⟨routeOpt_hh_HWF h, routeOpt_hh_congPhase h⟩

/-! ## Smoke tests -/

example : HWF heavyHex (routeCZ_hh 0 6) := routeCZ_hh_HWF (by omega) (by omega) (by omega)
example : UCom.CongPhase (routeCZ_hh 0 6) (.cz 0 6) :=
  routeCZ_hh_congPhase (by omega) (by omega) (by omega)
example (h : WF (.seq (.app1 .x 0) (.cz 0 6) : UCom 12)) :
    HWF heavyHex (optimize (route_hh (.seq (.app1 .x 0) (.cz 0 6) : UCom 12))) ∧
    UCom.CongPhase (optimize (route_hh (.seq (.app1 .x 0) (.cz 0 6) : UCom 12)))
      (.seq (.app1 .x 0) (.cz 0 6)) :=
  compile_correct_hh h

end QpuCompiler
