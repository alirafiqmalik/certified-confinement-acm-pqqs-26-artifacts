/-
QpuCompiler/Compile.lean — the full routing pass and the end-to-end compiler
theorem (iteration 09). This file lifts single-CZ routing (`route1cz`) to a total
`routeCZ` on any pair, recurses over the UCom tree in `route`, and composes the
result with `optimize` to give `compile_correct`: every WF circuit compiles to a
hardware-legal circuit that is provably equivalent to the source up to a global phase.
-/
import QpuCompiler.Route

namespace QpuCompiler

open scoped QpuCompiler

/-! ## Total single-CZ routing -/

/-- Route a single `cz a b` for ANY pair `a b`. Adjacent pairs are already
lnnPath-legal in both orientations. Distant pairs delegate to `route1cz`
(ascending directly, descending after swapping endpoints). -/
def routeCZ (n a b : ℕ) : UCom n :=
  if a + 1 = b ∨ b + 1 = a then .cz a b
  else if a < b then route1cz n a b
  else route1cz n b a

theorem routeCZ_HWF {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    HWF (lnnPath n) (routeCZ n a b) := by
  unfold routeCZ
  split
  · rename_i h
    refine .cz ?_
    simp only [lnnPath, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨⟨h, ha⟩, hb⟩
  · split
    · exact route1cz_HWF (by omega) hb
    · exact route1cz_HWF (by omega) ha

theorem routeCZ_congPhase {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    UCom.CongPhase (routeCZ n a b) (.cz a b) := by
  unfold routeCZ
  split
  · exact UCom.CongPhase.refl (.cz a b)
  · split
    · exact route1cz_congPhase (by omega) hb
    · have h1 := route1cz_congPhase (n := n) (a := b) (b := a) (by omega) ha
      have hcomm : (UCom.cz b a : UCom n) ≋ .cz a b := padCZ_comm n b a
      exact h1.trans hcomm.toCongPhase

/-! ## Full routing pass over the UCom tree -/

/-- Route an entire circuit: recurse structurally, sending each `cz` through
`routeCZ`. -/
def route {n : ℕ} : UCom n → UCom n
  | .seq c₁ c₂ => .seq (route c₁) (route c₂)
  | .app1 g q  => .app1 g q
  | .cz a b    => routeCZ n a b

theorem route_HWF {n : ℕ} {c : UCom n} (h : WF c) :
    HWF (lnnPath n) (route c) := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | app1 hq => exact .app1 hq
  | cz ha hb hab => exact routeCZ_HWF ha hb hab

theorem route_congPhase {n : ℕ} {c : UCom n} (h : WF c) :
    UCom.CongPhase (route c) c := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact UCom.CongPhase.seq_congr ih₁ ih₂
  | app1 => exact UCom.CongPhase.refl _
  | cz ha hb hab => exact routeCZ_congPhase ha hb hab

/-! ## End-to-end compiler -/

theorem routeOpt_HWF {n : ℕ} {c : UCom n} (h : WF c) :
    HWF (lnnPath n) (optimize (route c)) :=
  optimize_HWF (route_HWF h)

theorem routeOpt_congPhase {n : ℕ} {c : UCom n} (h : WF c) :
    UCom.CongPhase (optimize (route c)) c :=
  ((optimize_sound (route_HWF h).toWF).toCongPhase).trans (route_congPhase h)

/-- **HEADLINE.** Any well-formed circuit compiles (route + optimize) to a
hardware-legal circuit provably equivalent to the source up to a global phase. -/
theorem compile_correct {n : ℕ} {c : UCom n} (h : WF c) :
    HWF (lnnPath n) (optimize (route c)) ∧ UCom.CongPhase (optimize (route c)) c :=
  ⟨routeOpt_HWF h, routeOpt_congPhase h⟩

/-! ## Smoke tests -/

example : HWF (lnnPath 4) (routeCZ 4 0 3) := routeCZ_HWF (by omega) (by omega) (by omega)
example : HWF (lnnPath 4) (routeCZ 4 3 0) := routeCZ_HWF (by omega) (by omega) (by omega)
example : HWF (lnnPath 4) (routeCZ 4 0 1) := routeCZ_HWF (by omega) (by omega) (by omega)
example : UCom.CongPhase (routeCZ 4 3 0) (.cz 3 0) :=
  routeCZ_congPhase (by omega) (by omega) (by omega)
example (h : WF (.seq (.app1 .x 0) (.cz 0 3) : UCom 4)) :
    HWF (lnnPath 4) (optimize (route (.seq (.app1 .x 0) (.cz 0 3) : UCom 4))) ∧
    UCom.CongPhase (optimize (route (.seq (.app1 .x 0) (.cz 0 3) : UCom 4)))
      (.seq (.app1 .x 0) (.cz 0 3)) :=
  compile_correct h

end QpuCompiler
