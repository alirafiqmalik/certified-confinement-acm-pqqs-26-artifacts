/-
QpuCompiler/Equiv.lean — semantic equivalence of circuits (sqir's `uc_equiv` and
`uc_cong`, written as plain defs, with no Setoid or Quotient). `seq_congr`
replaces `rw` under `seq`, and the `Trans` instance supports `calc`.
-/
import QpuCompiler.Denote

namespace QpuCompiler

/-- Semantic equivalence: equal denotations (sqir `uc_equiv`). -/
def UCom.Equiv {n : ℕ} (c₁ c₂ : UCom n) : Prop := denote c₁ = denote c₂

@[inherit_doc] scoped infix:50 " ≋ " => UCom.Equiv

namespace UCom.Equiv

theorem refl {n : ℕ} (c : UCom n) : c ≋ c := Eq.refl _
theorem symm {n : ℕ} {c₁ c₂ : UCom n} (h : c₁ ≋ c₂) : c₂ ≋ c₁ := Eq.symm h
theorem trans {n : ℕ} {c₁ c₂ c₃ : UCom n} (h₁ : c₁ ≋ c₂) (h₂ : c₂ ≋ c₃) : c₁ ≋ c₃ :=
  Eq.trans h₁ h₂

end UCom.Equiv

theorem UCom.equivalence_equiv (n : ℕ) : Equivalence (UCom.Equiv (n := n)) :=
  ⟨UCom.Equiv.refl, UCom.Equiv.symm, UCom.Equiv.trans⟩

instance {n : ℕ} : Trans (UCom.Equiv (n := n)) (UCom.Equiv (n := n)) (UCom.Equiv (n := n)) :=
  ⟨UCom.Equiv.trans⟩

/-- Congruence of `≋` under sequencing. This is the workhorse that replaces Coq's
`Proper`. -/
theorem UCom.Equiv.seq_congr {n : ℕ} {c₁ c₁' c₂ c₂' : UCom n}
    (h₁ : c₁ ≋ c₁') (h₂ : c₂ ≋ c₂') : UCom.seq c₁ c₂ ≋ UCom.seq c₁' c₂' := by
  show denote c₂ * denote c₁ = denote c₂' * denote c₁'
  rw [show denote c₁ = denote c₁' from h₁, show denote c₂ = denote c₂' from h₂]

/-- Equivalence up to a global phase (sqir `uc_cong`). -/
def UCom.CongPhase {n : ℕ} (c₁ c₂ : UCom n) : Prop :=
  ∃ θ : ℝ, denote c₁ = Complex.exp (θ * Complex.I) • denote c₂

theorem UCom.Equiv.toCongPhase {n : ℕ} {c₁ c₂ : UCom n} (h : c₁ ≋ c₂) :
    UCom.CongPhase c₁ c₂ :=
  ⟨0, by rw [show denote c₁ = denote c₂ from h]; simp [Complex.exp_zero]⟩

namespace UCom.CongPhase

theorem refl {n : ℕ} (c : UCom n) : CongPhase c c :=
  ⟨0, by simp [Complex.exp_zero]⟩

theorem symm {n : ℕ} {c₁ c₂ : UCom n} (h : CongPhase c₁ c₂) : CongPhase c₂ c₁ := by
  obtain ⟨θ, h⟩ := h
  refine ⟨-θ, ?_⟩
  rw [h, smul_smul, ← Complex.exp_add,
    show ((-θ : ℝ) : ℂ) * Complex.I + ((θ : ℝ) : ℂ) * Complex.I = 0 from by push_cast; ring,
    Complex.exp_zero, one_smul]

theorem trans {n : ℕ} {c₁ c₂ c₃ : UCom n}
    (h₁ : CongPhase c₁ c₂) (h₂ : CongPhase c₂ c₃) : CongPhase c₁ c₃ := by
  obtain ⟨θ₁, h₁⟩ := h₁
  obtain ⟨θ₂, h₂⟩ := h₂
  refine ⟨θ₁ + θ₂, ?_⟩
  rw [h₁, h₂, smul_smul, ← Complex.exp_add,
    show ((θ₁ : ℝ) : ℂ) * Complex.I + ((θ₂ : ℝ) : ℂ) * Complex.I
        = ((θ₁ + θ₂ : ℝ) : ℂ) * Complex.I from by push_cast; ring]

end UCom.CongPhase

theorem UCom.equivalence_congPhase (n : ℕ) : Equivalence (UCom.CongPhase (n := n)) :=
  ⟨UCom.CongPhase.refl, UCom.CongPhase.symm, UCom.CongPhase.trans⟩

/-- Congruence of `CongPhase` under sequencing (the phases multiply). -/
theorem UCom.CongPhase.seq_congr {n : ℕ} {c₁ c₁' c₂ c₂' : UCom n}
    (h₁ : CongPhase c₁ c₁') (h₂ : CongPhase c₂ c₂') :
    CongPhase (.seq c₁ c₂) (.seq c₁' c₂') := by
  obtain ⟨θ₁, h₁⟩ := h₁
  obtain ⟨θ₂, h₂⟩ := h₂
  refine ⟨θ₂ + θ₁, ?_⟩
  show denote c₂ * denote c₁
      = Complex.exp (↑(θ₂ + θ₁) * Complex.I) • (denote c₂' * denote c₁')
  rw [h₁, h₂, smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
    show ((θ₂ : ℝ) : ℂ) * Complex.I + ((θ₁ : ℝ) : ℂ) * Complex.I
        = ((θ₂ + θ₁ : ℝ) : ℂ) * Complex.I from by push_cast; ring]

/-- Named intro for a global-phase congruence. It reads more clearly than
`refine ⟨θ, ?_⟩`. -/
theorem UCom.CongPhase.of_phase {n : ℕ} {c₁ c₂ : UCom n} (θ : ℝ)
    (h : denote c₁ = Complex.exp (θ * Complex.I) • denote c₂) : CongPhase c₁ c₂ :=
  ⟨θ, h⟩

/-- Thread a phase through the RIGHT operand of a `seq` (fixed left factor `d`). -/
theorem UCom.CongPhase.seq_left {n : ℕ} (d : UCom n) {c c' : UCom n}
    (h : CongPhase c c') : CongPhase (.seq d c) (.seq d c') :=
  UCom.CongPhase.seq_congr (UCom.CongPhase.refl d) h

/-- Thread a phase through the LEFT operand of a `seq` (fixed right factor `d`). -/
theorem UCom.CongPhase.seq_right {n : ℕ} (d : UCom n) {c c' : UCom n}
    (h : CongPhase c c') : CongPhase (.seq c d) (.seq c' d) :=
  UCom.CongPhase.seq_congr h (UCom.CongPhase.refl d)

end QpuCompiler
