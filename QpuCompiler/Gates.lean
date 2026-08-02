/-
QpuCompiler/Gates.lean — IBM Heron r2 native 1-qubit gate matrices + unitarity.

Conventions (Qiskit):
* `RZ θ = diag(e^{-iθ/2}, e^{iθ/2})`, matching Qiskit's `RZGate`.
* `SX = √X` with global phase `e^{iπ/4}` folded in (Qiskit convention):
  `SX = (1/2) * [[1+i, 1-i], [1-i, 1+i]]`.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QpuCompiler.KronPow

namespace QpuCompiler

namespace Gate

def X : Square 1 := !![0, 1; 1, 0]

noncomputable def SX : Square 1 :=
  (2 : ℂ)⁻¹ • !![1 + Complex.I, 1 - Complex.I;
                 1 - Complex.I, 1 + Complex.I]

noncomputable def RZ (θ : ℝ) : Square 1 :=
  Matrix.diagonal ![Complex.exp (-(θ / 2 : ℝ) * Complex.I),
                    Complex.exp ((θ / 2 : ℝ) * Complex.I)]

theorem X_mul_X : X * X = 1 := by
  unfold X
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem X_mem_unitaryGroup : X ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star X = X := by
    rw [Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.conjTranspose_apply]
  rw [hstar, X_mul_X]

theorem SX_mul_SX : SX * SX = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SX, X, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff]

theorem SX_mem_unitaryGroup : SX ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    norm_num [Complex.ext_iff]

theorem RZ_mul_RZ (θ φ : ℝ) : RZ θ * RZ φ = RZ (θ + φ) := by
  unfold RZ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;>
    · show Complex.exp _ * Complex.exp _ = Complex.exp _
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

theorem RZ_zero : RZ 0 = 1 := by
  unfold RZ
  have h : (![Complex.exp (-((0 : ℝ) / 2 : ℝ) * Complex.I),
      Complex.exp (((0 : ℝ) / 2 : ℝ) * Complex.I)]) = fun _ : Fin 2 => (1 : ℂ) := by
    funext i
    fin_cases i <;> norm_num [Complex.exp_zero]
  rw [h]
  exact Matrix.diagonal_one

/-- `RZ` (Qiskit half-angle convention) is exactly 4π-periodic. -/
theorem RZ_add_int_mul_four_pi (θ : ℝ) (k : ℤ) :
    RZ (θ + k * (4 * Real.pi)) = RZ θ := by
  unfold RZ
  congr 1
  funext i
  fin_cases i
  · have h0 : Complex.exp (-↑((θ + ↑k * (4 * Real.pi)) / 2) * Complex.I)
        = Complex.exp (-↑(θ / 2) * Complex.I) := by
      rw [show (-↑((θ + ↑k * (4 * Real.pi)) / 2) * Complex.I : ℂ)
            = -↑(θ / 2) * Complex.I + ((-k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by
          push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simpa using h0
  · have h1 : Complex.exp (↑((θ + ↑k * (4 * Real.pi)) / 2) * Complex.I)
        = Complex.exp (↑(θ / 2) * Complex.I) := by
      rw [show (↑((θ + ↑k * (4 * Real.pi)) / 2) * Complex.I : ℂ)
            = ↑(θ / 2) * Complex.I + ((k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by
          push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simpa using h1

theorem RZ_mem_unitaryGroup (θ : ℝ) : RZ θ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have key : ∀ x : ℝ, Complex.exp (x * Complex.I) * star (Complex.exp (x * Complex.I)) = 1 := by
    intro x
    rw [← starRingEnd_apply, ← Complex.exp_conj, ← Complex.exp_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    exact Complex.exp_zero
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, RZ,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    fin_cases i
    · simpa using key (-(θ / 2))
    · simpa using key (θ / 2)
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

end Gate

end QpuCompiler
