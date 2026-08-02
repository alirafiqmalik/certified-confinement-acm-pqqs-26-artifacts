/-
QpuCompiler/Sanity.lean — sanity theorems for the Heron circuit semantics.
-/
import QpuCompiler.Denote

namespace QpuCompiler

/-- Smoke test: sequencing denotes to reversed matrix product (definitional). -/
theorem denote_seq {n : ℕ} (c₁ c₂ : UCom n) :
    denote (.seq c₁ c₂) = denote c₂ * denote c₁ := rfl

/-- Centerpiece: well-formed circuits denote unitaries. -/
theorem denote_mem_unitaryGroup_of_WF {n : ℕ} {c : UCom n} (h : WF c) :
    denote c ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction h with
  | seq h₁ h₂ ih₁ ih₂ => exact mul_mem ih₂ ih₁
  | app1 hq => exact padU_mem_unitaryGroup hq (Gate1.matrix_mem_unitaryGroup _)
  | cz ha hb hab => exact padCZ_mem_unitaryGroup ha hb hab

/-- Concrete equivalence: X;X = I on one qubit — seed of gate cancellation. -/
theorem denote_xx_cancel :
    denote (n := 1) (.seq (.app1 .x 0) (.app1 .x 0)) = 1 := by
  show padU 1 0 Gate.X * padU 1 0 Gate.X = 1
  rw [padU_mul, Gate.X_mul_X, padU_one (by omega)]

/-- Heron-specific: the native CZ is symmetric (direction-independence for free). -/
theorem denote_cz_comm {n : ℕ} (a b : ℕ) :
    denote (n := n) (.cz a b) = denote (.cz b a) := padCZ_comm n a b

/-! ### Endianness probes (n = 2 tripwires).
`padU` places qubit `q` at bit `q`. X on qubit 0 swaps indices 0 and 1.
X on qubit 1 swaps indices 0 and 2. `padCZ` flips the sign only on index 3. -/

theorem padU_probe_bit0 : padU 2 0 Gate.X 0 1 = 1 := by
  rw [padU, dif_pos (by norm_num), castSq_apply, kronPow_apply, kronPow_apply]
  norm_num [Gate.X, Matrix.one_apply]

theorem padU_probe_bit1 : padU 2 1 Gate.X 0 2 = 1 := by
  rw [padU, dif_pos (by norm_num), castSq_apply, kronPow_apply, kronPow_apply]
  norm_num [Gate.X, Matrix.one_apply]

theorem padU_probe_bit1_off : padU 2 1 Gate.X 0 1 = 0 := by
  rw [padU, dif_pos (by norm_num), castSq_apply, kronPow_apply, kronPow_apply]
  norm_num [Gate.X, Matrix.one_apply]

theorem padCZ_probe : padCZ 2 0 1 3 3 = -1 := by
  rw [padCZ, if_pos (by norm_num), Matrix.diagonal_apply_eq]
  norm_num
  decide

end QpuCompiler
