/-
QpuCompiler/Circuit.lean — sqir-style circuit IR for the IBM Heron r2 basis. The
basis has one-qubit gates `x`, `sx`, `id`, `rz θ`, plus the native two-qubit `cz`.
It has well-formedness (bounds and distinctness), following sqir's `uc_well_typed`.

This is pure syntax: it has no matrices. Qubit arguments are bare `ℕ` (the sqir
convention). Well-formedness is a separate predicate. There is no `skip`
constructor (sqir has none too — `app1 .id 0` is the derived skip).
-/
import Mathlib.Data.Real.Basic

namespace QpuCompiler

/-- One-qubit gates of the Heron r2 basis. The `rz` angle is a rational number in
units of π (the VOQC `RzQ` convention): `rz r` denotes `RZ (r·π)`. Rational angles
give decidable equality. So they give decidable zero-rotation deletion. -/
inductive Gate1 : Type
  | x | sx | id | rz (r : ℚ)
  deriving DecidableEq

/-- Unitary circuits on `n` qubits: sequencing, one-qubit gate application,
and the native two-qubit CZ. -/
inductive UCom (n : ℕ) : Type
  | seq  (c₁ c₂ : UCom n)
  | app1 (g : Gate1) (q : ℕ)
  | cz   (a b : ℕ)

/-- Well-formedness: all qubit indices in range, CZ endpoints distinct. -/
inductive WF {n : ℕ} : UCom n → Prop
  | seq  {c₁ c₂ : UCom n} : WF c₁ → WF c₂ → WF (.seq c₁ c₂)
  | app1 {g : Gate1} {q : ℕ} : q < n → WF (.app1 g q)
  | cz   {a b : ℕ} : a < n → b < n → a ≠ b → WF (.cz a b)

/-- Boolean well-formedness check. -/
def UCom.wfb {n : ℕ} : UCom n → Bool
  | .seq c₁ c₂ => c₁.wfb && c₂.wfb
  | .app1 _ q  => decide (q < n)
  | .cz a b    => decide (a < n) && decide (b < n) && decide (a ≠ b)

theorem UCom.wfb_iff_WF {n : ℕ} (c : UCom n) : c.wfb = true ↔ WF c := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [wfb, Bool.and_eq_true, ih₁, ih₂]
    constructor
    · rintro ⟨h₁, h₂⟩; exact .seq h₁ h₂
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, h₂⟩
  | app1 g q =>
    simp only [wfb, decide_eq_true_eq]
    constructor
    · exact .app1
    · intro h; cases h with | app1 hq => exact hq
  | cz a b =>
    simp only [wfb, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩; exact .cz ha hb hab
    · intro h; cases h with | cz ha hb hab => exact ⟨⟨ha, hb⟩, hab⟩

/-- A well-formed circuit forces a positive register (every leaf has a qubit `< n`). -/
theorem WF.pos {n : ℕ} {c : UCom n} (h : WF c) : 0 < n := by
  induction h with
  | seq _ _ ih₁ _ => exact ih₁
  | app1 hq => omega
  | cz ha _ _ => omega

instance {n : ℕ} (c : UCom n) : Decidable (WF c) :=
  decidable_of_iff _ c.wfb_iff_WF

end QpuCompiler
