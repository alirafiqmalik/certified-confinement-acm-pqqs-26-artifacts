/-
QpuCompiler/Denote.lean — matrix denotation of Heron circuits.

Bit convention: qubit `q` corresponds to bit `q` of the `Fin (2^n)` index,
little-endian (the Qiskit convention; `Nat.testBit i q`). `padU` builds this as
`I(2^(n−q−1)) ⊗ u ⊗ I(2^q)`. The index equivalence (KronPow.lean) puts the first
Kronecker factor in the high bits, so `u` sits at bit `q`. `padCZ` tests bits `a`
and `b` directly. `padU_diagonal` and the probe theorems in Sanity.lean lock this
consistency.

sqir conventions: denotation is total, with `0` for out-of-range qubit
arguments. `seq` denotes as the reversed matrix product.
-/
import QpuCompiler.KronPow
import QpuCompiler.Gates
import QpuCompiler.Circuit

namespace QpuCompiler

/-- Matrix of a one-qubit gate. -/
noncomputable def Gate1.matrix : Gate1 → Square 1
  | .x    => Gate.X
  | .sx   => Gate.SX
  | .id   => 1
  | .rz r => Gate.RZ ((r : ℝ) * Real.pi)

theorem Gate1.matrix_mem_unitaryGroup (g : Gate1) :
    g.matrix ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  cases g with
  | x => exact Gate.X_mem_unitaryGroup
  | sx => exact Gate.SX_mem_unitaryGroup
  | id => exact one_mem _
  | rz r => exact Gate.RZ_mem_unitaryGroup _

/-- Embed a 1-qubit gate at qubit `q` (little-endian) in an `n`-qubit register:
    `I(2^(n-q-1)) ⊗ u ⊗ I(2^q)`. The value is `0` if `q` is out of range (sqir
    convention). -/
noncomputable def padU (n q : ℕ) (u : Square 1) : Square n :=
  if h : q + 1 ≤ n then
    castSq (by omega) (kronPow (kronPow (1 : Square (n - (q + 1))) u) (1 : Square q))
  else 0

/-- CZ on qubits `a`, `b` as a diagonal matrix: entry `i i` is `-1` when bits `a`
    and `b` of `i` are both set (qubit `q` corresponds to bit `q`, little-endian),
    and `1` otherwise. The value is `0` if the arguments are ill-formed. -/
def padCZ (n a b : ℕ) : Square n :=
  if a < n ∧ b < n ∧ a ≠ b then
    Matrix.diagonal (fun i : Fin (2 ^ n) =>
      if (i : ℕ).testBit a && (i : ℕ).testBit b then (-1 : ℂ) else 1)
  else 0

/-- Denotation of a circuit. This function is total: it gives `0` on ill-formed
applications. -/
noncomputable def denote {n : ℕ} : UCom n → Square n
  | .seq c₁ c₂ => denote c₂ * denote c₁      -- reversed order, the sqir convention
  | .app1 g q  => padU n q g.matrix
  | .cz a b    => padCZ n a b

/-! ### Pad lemmas -/

theorem padU_mul {n q : ℕ} (u v : Square 1) :
    padU n q u * padU n q v = padU n q (u * v) := by
  by_cases h : q + 1 ≤ n
  · simp only [padU, dif_pos h]
    rw [castSq_mul, ← kronPow_mul, ← kronPow_mul, one_mul, one_mul]
  · have h' : ¬ q < n := by omega
    simp [padU, h']

theorem padU_one {n q : ℕ} (h : q + 1 ≤ n) : padU n q (1 : Square 1) = 1 := by
  simp only [padU, dif_pos h]
  rw [kronPow_one, kronPow_one, castSq_one]

theorem padU_mem_unitaryGroup {n q : ℕ} (h : q + 1 ≤ n) {u : Square 1}
    (hu : u ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ) :
    padU n q u ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  simp only [padU, dif_pos h]
  exact castSq_mem_unitaryGroup _
    (kronPow_mem_unitaryGroup (kronPow_mem_unitaryGroup (one_mem _) hu) (one_mem _))

/-- The consistency lock: `padU` places a diagonal 1-qubit gate at bit `q`
(little-endian) of the index. -/
theorem padU_diagonal {n q : ℕ} (h : q + 1 ≤ n) (d : Fin 2 → ℂ) :
    padU n q (Matrix.diagonal d) =
      Matrix.diagonal (fun i : Fin (2 ^ n) =>
        d (if (i : ℕ).testBit q then 1 else 0)) := by
  have bridge : ∀ m : ℕ, (⟨m / 2 ^ q % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)
      = if m.testBit q then 1 else 0 := by
    intro m
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ q) with h' | h' <;>
      simp [Nat.testBit_eq_decide_div_mod_eq, h']
  rw [padU, dif_pos h, ← Matrix.diagonal_one (n := Fin (2 ^ (n - (q + 1)))),
    ← Matrix.diagonal_one (n := Fin (2 ^ q)), kronPow_diagonal, kronPow_diagonal,
    castSq_diagonal]
  congr 1
  funext i
  rw [one_mul, mul_one]
  congr 1
  exact bridge (i : ℕ)

theorem padCZ_mem_unitaryGroup {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    padCZ n a b ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [padCZ, if_pos ⟨ha, hb, hab⟩, Matrix.mem_unitaryGroup_iff,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    split <;> norm_num
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- CZ is an involution in the well-formed case. In the ill-formed case `padCZ`
is `0`, and the statement would be false. -/
theorem padCZ_mul_self {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    padCZ n a b * padCZ n a b = 1 := by
  rw [padCZ, if_pos ⟨ha, hb, hab⟩, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  split <;> norm_num

/-- CZ commutes with any RZ, on any qubit arguments, even ill-formed ones. Both
gates are diagonal in the computational basis. -/
theorem padCZ_padU_rz_comm (n a b q : ℕ) (θ : ℝ) :
    padCZ n a b * padU n q (Gate.RZ θ) = padU n q (Gate.RZ θ) * padCZ n a b := by
  by_cases hq : q + 1 ≤ n
  · by_cases hab : a < n ∧ b < n ∧ a ≠ b
    · rw [Gate.RZ, padU_diagonal hq, padCZ, if_pos hab,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    · rw [padCZ, if_neg hab, zero_mul, mul_zero]
  · rw [padU, dif_neg hq, mul_zero, zero_mul]

/-! ### i11 — the general entrywise value of `padU`

This proof uses only the exported `castSq_apply`/`kronPow_apply` (the
`Sanity.lean:34` chain). A nonzero entry means `i` and `j` agree off bit `v`: they
have equal division by `2^(v+1)` and equal remainder mod `2^v`. The surviving
factor is the 2×2 matrix `M` at the bit-`v` indices. -/
theorem padU_apply {n v : ℕ} (h : v + 1 ≤ n) (M : Square 1) (i j : Fin (2 ^ n)) :
    padU n v M i j
      = (if (i : ℕ) / 2 ^ (v + 1) = (j : ℕ) / 2 ^ (v + 1)
             ∧ (i : ℕ) % 2 ^ v = (j : ℕ) % 2 ^ v
          then M ⟨(i : ℕ) / 2 ^ v % 2, Nat.mod_lt _ (by norm_num)⟩
                 ⟨(j : ℕ) / 2 ^ v % 2, Nat.mod_lt _ (by norm_num)⟩
          else 0) := by
  rw [padU, dif_pos h, castSq_apply, kronPow_apply, kronPow_apply]
  simp only [Matrix.one_apply, Fin.mk.injEq, pow_one]
  have hdi : (i : ℕ) / 2 ^ v / 2 = (i : ℕ) / 2 ^ (v + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hdj : (j : ℕ) / 2 ^ v / 2 = (j : ℕ) / 2 ^ (v + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [hdi, hdj]
  by_cases hcond1 : (i : ℕ) / 2 ^ (v + 1) = (j : ℕ) / 2 ^ (v + 1) <;>
    by_cases hcond2 : (i : ℕ) % 2 ^ v = (j : ℕ) % 2 ^ v <;>
    simp [hcond1, hcond2]

theorem padCZ_comm (n a b : ℕ) : padCZ n a b = padCZ n b a := by
  unfold padCZ
  have hcond : (a < n ∧ b < n ∧ a ≠ b) ↔ (b < n ∧ a < n ∧ b ≠ a) := by tauto
  split_ifs with h₁ h₂ h₂
  · congr 1
    funext i
    rw [Bool.and_comm]
  · exact absurd (hcond.mp h₁) h₂
  · exact absurd (hcond.mpr h₂) h₁
  · rfl

end QpuCompiler
