/-
QpuCompiler/Optimize.lean — first verified pass: single-sweep adjacent 1-qubit-gate
fusion on the gate-list normal form (voqc-style, cancel rules only, no commutation,
no fuel). Soundness: the pass preserves denotation (`optimize c ≋ c`).
-/
import QpuCompiler.GateList
import Mathlib.Data.Rat.Floor

namespace QpuCompiler

/-- Canonical representative of an rz angle (units of π) modulo the exact
4π-periodicity of `Gate.RZ`: `bound4 r ∈ [0, 4)`. -/
def bound4 (r : ℚ) : ℚ := 4 * Int.fract (r / 4)

theorem bound4_sub (r : ℚ) : r - bound4 r = 4 * (⌊r / 4⌋ : ℚ) := by
  unfold bound4
  have h := Int.self_sub_fract (r / 4)
  linear_combination 4 * h

theorem RZQ_bound4 (r : ℚ) :
    Gate.RZ (((bound4 r : ℚ) : ℝ) * Real.pi) = Gate.RZ ((r : ℝ) * Real.pi) := by
  have hsub : ((r : ℝ)) * Real.pi
      = ((bound4 r : ℚ) : ℝ) * Real.pi + (⌊r / 4⌋ : ℤ) * (4 * Real.pi) := by
    have h := congrArg (fun q : ℚ => ((q : ℝ))) (bound4_sub r)
    push_cast at h
    linear_combination Real.pi * h
  rw [hsub, Gate.RZ_add_int_mul_four_pi]

/-- Adjacent-fusion rules: `id` absorbs, `x·x ↦ id`, `rz` angles add.
Convention: `fuse g g' = some g''` means gate `g` *then* `g'` fuses to `g''`,
that is, `g''.matrix = g'.matrix * g.matrix`. -/
def fuse : Gate1 → Gate1 → Option Gate1
  | .id,   g     => some g
  | g,     .id   => some g
  | .x,    .x    => some .id
  | .sx,   .sx   => some .x
  | .rz r, .rz r' =>
      let s := bound4 (r + r')
      some (if s = 0 then .id else .rz s)
  | _,     _     => none

theorem fuse_sound {g g' g'' : Gate1} (h : fuse g g' = some g'') :
    g''.matrix = g'.matrix * g.matrix := by
  cases g <;> cases g' <;>
    simp only [fuse, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    simp only [Gate1.matrix, one_mul, mul_one]
  case x.x => exact Gate.X_mul_X.symm
  case sx.sx => exact Gate.SX_mul_SX.symm
  case rz.rz θ φ =>
    rw [Gate.RZ_mul_RZ,
      show (↑φ * Real.pi + ↑θ * Real.pi : ℝ) = ((θ + φ : ℚ) : ℝ) * Real.pi from by
        push_cast; ring,
      ← RZQ_bound4 (θ + φ)]
    split_ifs with hs
    · show (1 : Square 1) = Gate.RZ (↑(bound4 (θ + φ)) * Real.pi)
      rw [hs, Rat.cast_zero, zero_mul, Gate.RZ_zero]
    · rfl

/-- One fusion sweep. On a fusion hit the fused gate is reconsidered against
the next gate (so chains like `x, x, x` collapse in one sweep). Terminates:
the list length strictly decreases on the fused branch and the tail shrinks
otherwise. -/
def optAdj : List GApp → List GApp
  | [] => []
  | [a] => [a]
  | .g1 g q :: .g1 g' q' :: rest =>
      if q = q' then
        match fuse g g' with
        | some g'' => optAdj (.g1 g'' q :: rest)
        | none     => .g1 g q :: optAdj (.g1 g' q' :: rest)
      else .g1 g q :: optAdj (.g1 g' q' :: rest)
  | .g2 a b :: .g2 a' b' :: rest =>
      if (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') then optAdj rest
      else .g2 a b :: optAdj (.g2 a' b' :: rest)
  | .g1 (.rz r) q :: .g2 a b :: .g1 (.rz r') q' :: rest =>
      if q = q' then optAdj (.g2 a b :: .g1 (.rz (bound4 (r + r'))) q :: rest)
      else .g1 (.rz r) q :: optAdj (.g2 a b :: .g1 (.rz r') q' :: rest)
  | a :: rest => a :: optAdj rest
termination_by l => l.length

theorem optAdj_sound (n : ℕ) (l : List GApp)
    (hl : ∀ a ∈ l, a.wfb n = true) :
    listDenote n (optAdj l) = listDenote n l := by
  fun_induction optAdj with
  | case1 => rfl
  | case2 a => rfl
  | case3 g g' q rest g'' hfuse ih =>
    rw [ih (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · simpa [GApp.wfb] using hl (.g1 g q) List.mem_cons_self
      · exact hl a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)))]
    simp only [listDenote_cons, GApp.denote]
    rw [mul_assoc, padU_mul, ← fuse_sound hfuse]
  | case4 g g' q rest hfuse ih =>
    simp [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  | case5 g q g' q' rest hq ih =>
    simp [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  | case6 a b a' b' rest hguard ih =>
    have hw := hl (.g2 a b) List.mem_cons_self
    simp only [GApp.wfb, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨ha, hb⟩, hab⟩ := hw
    rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))]
    simp only [listDenote_cons, GApp.denote]
    rcases hguard with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [mul_assoc, padCZ_mul_self ha hb hab, mul_one]
    · rw [padCZ_comm n b a, mul_assoc, padCZ_mul_self ha hb hab, mul_one]
  | case7 a b a' b' rest hguard ih =>
    simp [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  | case8 r₁ ca cb r₂ q rest ih =>
    rw [ih (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rcases List.mem_cons.mp hx with rfl | hx
        · simpa [GApp.wfb] using hl (.g1 (.rz r₁) q) List.mem_cons_self
        · exact hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hx))))]
    simp only [listDenote_cons, GApp.denote, Gate1.matrix]
    have hcomm : padCZ n ca cb * padU n q (Gate.RZ (↑r₁ * Real.pi))
        = padU n q (Gate.RZ (↑r₁ * Real.pi)) * padCZ n ca cb :=
      padCZ_padU_rz_comm n ca cb q _
    have hmul : padU n q (Gate.RZ (↑r₂ * Real.pi)) * padU n q (Gate.RZ (↑r₁ * Real.pi))
        = padU n q (Gate.RZ (↑(r₁ + r₂) * Real.pi)) := by
      rw [padU_mul, Gate.RZ_mul_RZ]; congr 2; push_cast; ring
    rw [RZQ_bound4 (r₁ + r₂)]
    conv_rhs => rw [mul_assoc, hcomm, ← mul_assoc, mul_assoc _ _ (padU n q (Gate.RZ (↑r₁ * Real.pi))), hmul]
  | case9 r₁ q ca cb r₂ q' rest hq ih =>
    simp [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  | case10 a rest h1 h2 h3 h4 ih =>
    simp [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]

theorem optAdj_wfb {n : ℕ} {l : List GApp} (hl : ∀ a ∈ l, a.wfb n = true) :
    ∀ a ∈ optAdj l, a.wfb n = true := by
  fun_induction optAdj with
  | case1 => exact hl
  | case2 a => exact hl
  | case3 g g' q rest g'' hfuse ih =>
    refine ih ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simpa [GApp.wfb] using hl (.g1 g q) List.mem_cons_self
    · exact hl a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
  | case4 g g' q rest hfuse ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hl _ List.mem_cons_self
    · exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) a ha
  | case5 g q g' q' rest hq ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hl _ List.mem_cons_self
    · exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) a ha
  | case6 a b a' b' rest hguard ih =>
    exact ih (fun x hx =>
      hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  | case7 a b a' b' rest hguard ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl _ List.mem_cons_self
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx
  | case8 r₁ ca cb r₂ q rest ih =>
    refine ih ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rcases List.mem_cons.mp hx with rfl | hx
      · simpa [GApp.wfb] using hl (.g1 (.rz r₁) q) List.mem_cons_self
      · exact hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hx)))
  | case9 r₁ q ca cb r₂ q' rest hq ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl _ List.mem_cons_self
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx
  | case10 a rest h1 h2 h3 h4 ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl x List.mem_cons_self
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

/-- Iterate `optAdj` to a fixpoint. Fuel-free: every `optAdj` rewrite strictly
shrinks the list, so a sweep that changed anything shortened it. Recursion is
guarded by the length test itself. -/
def optFix (l : List GApp) : List GApp :=
  if h : (optAdj l).length < l.length then optFix (optAdj l) else l
termination_by l.length
decreasing_by exact h

theorem optFix_sound (n : ℕ) (l : List GApp)
    (hl : ∀ a ∈ l, a.wfb n = true) :
    listDenote n (optFix l) = listDenote n l := by
  fun_induction optFix with
  | case1 l _ ih =>
    rw [ih (optAdj_wfb hl), optAdj_sound n l hl]
  | case2 l _ => rfl

theorem optFix_wfb {n : ℕ} {l : List GApp} (hl : ∀ a ∈ l, a.wfb n = true) :
    ∀ a ∈ optFix l, a.wfb n = true := by
  fun_induction optFix with
  | case1 l _ ih => exact ih (optAdj_wfb hl)
  | case2 l _ => exact hl

/-! ### Fixpoint characterization (S1) -/

theorem optAdj_length_le (l : List GApp) : (optAdj l).length ≤ l.length := by
  fun_induction optAdj <;>
    simp_all only [List.length_cons, List.length_nil, le_refl] <;> omega

theorem optAdj_progress (l : List GApp) :
    optAdj l = l ∨ (optAdj l).length < l.length := by
  fun_induction optAdj with
  | case1 => left; rfl
  | case2 a => left; rfl
  | case3 g g' q rest g'' hfuse ih =>
    right
    have := optAdj_length_le (.g1 g'' q :: rest)
    simp only [List.length_cons] at *; omega
  | case4 g g' q rest hfuse ih =>
    rcases ih with h | h
    · left; rw [h]
    · right; simp only [List.length_cons] at *; omega
  | case5 g q g' q' rest hq ih =>
    rcases ih with h | h
    · left; rw [h]
    · right; simp only [List.length_cons] at *; omega
  | case6 a b a' b' rest hguard ih =>
    right
    have := optAdj_length_le rest
    simp only [List.length_cons]; omega
  | case7 a b a' b' rest hguard ih =>
    rcases ih with h | h
    · left; rw [h]
    · right; simp only [List.length_cons] at *; omega
  | case8 r₁ ca cb r₂ q rest ih =>
    right
    have := optAdj_length_le (.g2 ca cb :: .g1 (.rz (bound4 (r₁ + r₂))) q :: rest)
    simp only [List.length_cons] at *; omega
  | case9 r₁ q ca cb r₂ q' rest hq ih =>
    rcases ih with h | h
    · left; rw [h]
    · right; simp only [List.length_cons] at *; omega
  | case10 a rest h1 h2 h3 h4 ih =>
    rcases ih with h | h
    · left; rw [h]
    · right; simp only [List.length_cons] at *; omega

theorem optAdj_optFix (l : List GApp) : optAdj (optFix l) = optFix l := by
  fun_induction optFix with
  | case1 l _ ih => exact ih
  | case2 l h =>
    rcases optAdj_progress l with hp | hp
    · exact hp
    · exact absurd hp h

/-- The verified pass: flatten, sweep adjacent fusion/cancellation to a
fixpoint, rebuild. -/
def optimize {n : ℕ} (c : UCom n) : UCom n := ofList (optFix c.toList)

open scoped QpuCompiler in
theorem optimize_sound {n : ℕ} {c : UCom n} (h : WF c) : optimize c ≋ c := by
  show denote (optimize c) = denote c
  rw [optimize, denote_ofList h.pos, optFix_sound n _ (wfb_toList h), denote_toList]

theorem optimize_WF {n : ℕ} {c : UCom n} (h : WF c) : WF (optimize c) :=
  WF_ofList h.pos (optFix_wfb (wfb_toList h))

/-! Smoke tests: adjacent X gates cancel. Odd chains collapse in one sweep. -/
example : optAdj [GApp.g1 .x 0, GApp.g1 .x 0] = [GApp.g1 .id 0] := by
  simp [optAdj, fuse]
example : optAdj [GApp.g1 .x 3, GApp.g1 .x 3, GApp.g1 .x 3] = [GApp.g1 .x 3] := by
  simp [optAdj, fuse]
-- cz·cz cancels, including the swapped orientation
example : optAdj [GApp.g2 0 1, GApp.g2 0 1] = [] := by simp [optAdj]
example : optAdj [GApp.g2 0 1, GApp.g2 1 0] = [] := by simp [optAdj]
-- rz(r) then rz(-r) deletes (through .id), and the id then feeds absorption
example : optAdj [GApp.g1 (.rz 1) 0, GApp.g1 (.rz (-1)) 0, GApp.g1 .x 0]
    = [GApp.g1 .x 0] := by simp [optAdj, fuse, bound4, Int.fract]
-- bound4 canonicalizes: 3π + 3π = 6π ↦ 2π (mod 4, units of π)
example : fuse (.rz 3) (.rz 3) = some (.rz 2) := by
  simp only [fuse, bound4]
  norm_num [Int.fract]
-- S2: an rz on either side of a cz (same qubit) merges across the cz
example : optAdj [GApp.g1 (.rz 1) 0, GApp.g2 0 1, GApp.g1 (.rz 2) 0]
    = [GApp.g2 0 1, GApp.g1 (.rz (bound4 3)) 0] := by simp only [optAdj]; norm_num
-- optFix beats one sweep: deleting the inner cz·cz exposes the outer x·x pair
example : optFix [GApp.g1 .x 0, GApp.g2 0 1, GApp.g2 0 1, GApp.g1 .x 0]
    = [GApp.g1 .id 0] := by simp [optFix, optAdj, fuse]

end QpuCompiler
