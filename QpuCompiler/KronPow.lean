/-
QpuCompiler/KronPow.lean — cast quarantine.

All `Fin (2^n)` index plumbing lives in this file: reindexing Kronecker products
back to `Fin (2^(a+b))`, and casting between equal dimensions. `kronPow` and
`castSq` are never unfolded outside this file. Downstream code uses only the
lemmas proved here.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace QpuCompiler

open Matrix

/-- Square complex matrix on `n` qubits. It is an `abbrev` so that instances and
defeq fire (`Square 1` unifies with `Matrix (Fin 2) (Fin 2) ℂ`). -/
abbrev Square (n : ℕ) : Type := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- The canonical equivalence `Fin (2^a) × Fin (2^b) ≃ Fin (2^(a+b))`. -/
def sqEquiv (a b : ℕ) : Fin (2 ^ a) × Fin (2 ^ b) ≃ Fin (2 ^ (a + b)) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)

/-- Kronecker product of square matrices, reindexed to `Fin (2^(a+b))`. -/
def kronPow {a b : ℕ} (A : Square a) (B : Square b) : Square (a + b) :=
  Matrix.reindex (sqEquiv a b) (sqEquiv a b) (Matrix.kronecker A B)

/-- Cast a square matrix along an equality of qubit counts. -/
def castSq {a b : ℕ} (h : a = b) (A : Square a) : Square b :=
  Matrix.reindex (finCongr (by rw [h])) (finCongr (by rw [h])) A

/-! ### Generic reindex lemmas -/

theorem reindex_mul {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    (e : m ≃ p) (A B : Matrix m m ℂ) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem reindex_one {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    (e : m ≃ p) : Matrix.reindex e e (1 : Matrix m m ℂ) = 1 := by
  simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem star_reindex {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    (e : m ≃ p) (A : Matrix m m ℂ) :
    star (Matrix.reindex e e A) = Matrix.reindex e e (star A) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.star_apply]

theorem reindex_mem_unitaryGroup {m p : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] (e : m ≃ p) {A : Matrix m m ℂ}
    (hA : A ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup p ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [star_reindex, reindex_mul, hA, reindex_one]

/-! ### `kronPow` / `castSq` lemmas -/

theorem kronPow_mul {a b : ℕ} (A A' : Square a) (B B' : Square b) :
    kronPow (A * A') (B * B') = kronPow A B * kronPow A' B' := by
  unfold kronPow
  rw [Matrix.kronecker, Matrix.mul_kronecker_mul, ← reindex_mul]

theorem kronPow_one {a b : ℕ} : kronPow (1 : Square a) (1 : Square b) = 1 := by
  unfold kronPow
  rw [Matrix.kronecker, Matrix.one_kronecker_one, reindex_one]

theorem kronPow_mem_unitaryGroup {a b : ℕ} {A : Square a} {B : Square b}
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ a)) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin (2 ^ b)) ℂ) :
    kronPow A B ∈ Matrix.unitaryGroup (Fin (2 ^ (a + b))) ℂ :=
  reindex_mem_unitaryGroup _ (Matrix.kronecker_mem_unitary hA hB)

theorem castSq_mul {a b : ℕ} (h : a = b) (A B : Square a) :
    castSq h A * castSq h B = castSq h (A * B) := by
  unfold castSq
  rw [reindex_mul]

theorem castSq_one {a b : ℕ} (h : a = b) : castSq h (1 : Square a) = 1 := by
  unfold castSq
  rw [reindex_one]

theorem castSq_mem_unitaryGroup {a b : ℕ} (h : a = b) {A : Square a}
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ a)) ℂ) :
    castSq h A ∈ Matrix.unitaryGroup (Fin (2 ^ b)) ℂ :=
  reindex_mem_unitaryGroup _ hA

/-! ### Entry lemmas

Downstream files consume `kronPow`/`castSq` entries only through these lemmas
(quarantine discipline): all `finProdFinEquiv`/`divNat`/`modNat` plumbing is
discharged here, once. -/

theorem kron_div_lt {a b : ℕ} (i : Fin (2 ^ (a + b))) : (i : ℕ) / 2 ^ b < 2 ^ a :=
  (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr (by rw [← pow_add]; exact i.isLt)

theorem kron_mod_lt {a b : ℕ} (i : Fin (2 ^ (a + b))) : (i : ℕ) % 2 ^ b < 2 ^ b :=
  Nat.mod_lt _ (Nat.two_pow_pos b)

theorem sqEquiv_symm_fst {a b : ℕ} (i : Fin (2 ^ (a + b))) :
    ((((sqEquiv a b).symm i).1 : ℕ)) = (i : ℕ) / 2 ^ b := by
  simp [sqEquiv]

theorem sqEquiv_symm_snd {a b : ℕ} (i : Fin (2 ^ (a + b))) :
    ((((sqEquiv a b).symm i).2 : ℕ)) = (i : ℕ) % 2 ^ b := by
  simp [sqEquiv]

theorem castSq_apply {a b : ℕ} (h : a = b) (A : Square a) (i j : Fin (2 ^ b)) :
    castSq h A i j
      = A ⟨(i : ℕ), by subst h; exact i.isLt⟩ ⟨(j : ℕ), by subst h; exact j.isLt⟩ := by
  subst h
  simp [castSq, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem castSq_diagonal {a b : ℕ} (h : a = b) (d : Fin (2 ^ a) → ℂ) :
    castSq h (Matrix.diagonal d) =
      Matrix.diagonal (fun i : Fin (2 ^ b) => d ⟨(i : ℕ), by subst h; exact i.isLt⟩) := by
  subst h
  ext i j
  rw [castSq_apply rfl]

theorem kronPow_apply {a b : ℕ} (A : Square a) (B : Square b)
    (i j : Fin (2 ^ (a + b))) :
    kronPow A B i j =
      A ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ ⟨(j : ℕ) / 2 ^ b, kron_div_lt j⟩ *
        B ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩ ⟨(j : ℕ) % 2 ^ b, kron_mod_lt j⟩ := by
  rw [kronPow, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  congr 1

theorem kronPow_diagonal {a b : ℕ} (dA : Fin (2 ^ a) → ℂ) (dB : Fin (2 ^ b) → ℂ) :
    kronPow (Matrix.diagonal dA) (Matrix.diagonal dB) =
      Matrix.diagonal (fun i : Fin (2 ^ (a + b)) =>
        dA ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ * dB ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩) := by
  ext i j
  rw [kronPow_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have key : ((i : ℕ) / 2 ^ b ≠ (j : ℕ) / 2 ^ b) ∨ ((i : ℕ) % 2 ^ b ≠ (j : ℕ) % 2 ^ b) := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      refine hij (Fin.ext ?_)
      have h1 := (Nat.div_add_mod (i : ℕ) (2 ^ b)).symm
      have h2 := (Nat.div_add_mod (j : ℕ) (2 ^ b)).symm
      rw [h1, h2, hc.1, hc.2]
    rw [Matrix.diagonal_apply_ne _ hij]
    rcases key with key | key
    · rw [Matrix.diagonal_apply_ne dA (fun hc => key (congrArg Fin.val hc)), zero_mul]
    · rw [Matrix.diagonal_apply_ne dB (fun hc => key (congrArg Fin.val hc)), mul_zero]

/-! ### `castSq` bookkeeping helpers (quarantine — used by the placement bridges). -/

@[simp] theorem castSq_rfl {a : ℕ} (A : Square a) : castSq rfl A = A := by
  unfold castSq
  simp [finCongr_refl]

theorem castSq_castSq {a b c : ℕ} (h : a = b) (h' : b = c) (A : Square a) :
    castSq h' (castSq h A) = castSq (h.trans h') A := by
  subst h; subst h'; simp

theorem kronPow_castSq_left {a a' b : ℕ} (h : a = a') (A : Square a) (B : Square b) :
    kronPow (castSq h A) B = castSq (by rw [h]) (kronPow A B) := by
  subst h; simp

theorem kronPow_castSq_right {a b b' : ℕ} (h : b = b') (A : Square a) (B : Square b) :
    kronPow A (castSq h B) = castSq (by rw [h]) (kronPow A B) := by
  subst h; simp

theorem castSq_smul {a b : ℕ} (h : a = b) (c : ℂ) (A : Square a) :
    castSq h (c • A) = c • castSq h A := by
  subst h; simp

theorem kronPow_smul_left {a b : ℕ} (c : ℂ) (A : Square a) (B : Square b) :
    kronPow (c • A) B = c • kronPow A B := by
  ext i j; simp only [Matrix.smul_apply, kronPow_apply, smul_eq_mul]; ring

theorem kronPow_smul_right {a b : ℕ} (c : ℂ) (A : Square a) (B : Square b) :
    kronPow A (c • B) = c • kronPow A B := by
  ext i j; simp only [Matrix.smul_apply, kronPow_apply, smul_eq_mul]; ring

/-! ### Associativity of `kronPow` (banked for the SWAP-routing block, i05+). -/

/-- Reassociate a triple `kronPow`, producing a single `castSq`. The reindex /
`prodAssoc` / `finCongr` plumbing is proved entrywise here and never leaks. -/
theorem kronPow_assoc {a b c : ℕ} (A : Square a) (B : Square b) (C : Square c) :
    kronPow (kronPow A B) C
      = castSq (Nat.add_assoc a b c).symm (kronPow A (kronPow B C)) := by
  ext i j
  simp only [castSq_apply, kronPow_apply]
  have hAi : ((i : ℕ) / 2 ^ c) / 2 ^ b = (i : ℕ) / 2 ^ (b + c) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm c b]
  have hAj : ((j : ℕ) / 2 ^ c) / 2 ^ b = (j : ℕ) / 2 ^ (b + c) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm c b]
  have hBi : ((i : ℕ) / 2 ^ c) % 2 ^ b = ((i : ℕ) % 2 ^ (b + c)) / 2 ^ c := by
    rw [← Nat.mod_mul_right_div_self, ← pow_add, Nat.add_comm c b]
  have hBj : ((j : ℕ) / 2 ^ c) % 2 ^ b = ((j : ℕ) % 2 ^ (b + c)) / 2 ^ c := by
    rw [← Nat.mod_mul_right_div_self, ← pow_add, Nat.add_comm c b]
  have hCi : (i : ℕ) % 2 ^ c = ((i : ℕ) % 2 ^ (b + c)) % 2 ^ c :=
    (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_left c b))).symm
  have hCj : (j : ℕ) % 2 ^ c = ((j : ℕ) % 2 ^ (b + c)) % 2 ^ c :=
    (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_left c b))).symm
  rw [mul_assoc]
  congr 1
  · exact congr (congrArg A (Fin.ext hAi)) (Fin.ext hAj)
  · congr 1
    · exact congr (congrArg B (Fin.ext hBi)) (Fin.ext hBj)
    · exact congr (congrArg C (Fin.ext hCi)) (Fin.ext hCj)

/-- Reverse orientation of `kronPow_assoc`: cast the *left*-nested product to the
right-nested one. -/
theorem kronPow_assoc' {a b c : ℕ} (A : Square a) (B : Square b) (C : Square c) :
    castSq (Nat.add_assoc a b c) (kronPow (kronPow A B) C) = kronPow A (kronPow B C) := by
  rw [kronPow_assoc, castSq_castSq]
  exact castSq_rfl _

/-! ### Permutation lifts (i06 — qubit→bit tensor lift)

`prodPerm` / `castPerm` mirror `kronPow` / `castSq` at the *permutation* level:
they conjugate an `Equiv.Perm` along the same `sqEquiv` / `finCongr` reindexings.
The two lemmas `kronPow_permMatrix` / `castSq_permMatrix` then say that
`permMatrix` intertwines the two levels. Quarantined here since they unfold
`sqEquiv` / `finCongr`. -/

/-- The product permutation on `Fin (2^(a+b))` induced by `σ` on the high `a`
bits and `τ` on the low `b` bits, transported along `sqEquiv`. -/
def prodPerm {a b : ℕ} (σ : Equiv.Perm (Fin (2 ^ a))) (τ : Equiv.Perm (Fin (2 ^ b))) :
    Equiv.Perm (Fin (2 ^ (a + b))) :=
  (sqEquiv a b).permCongr (σ.prodCongr τ)

/-- Transport a permutation of `Fin (2^a)` to `Fin (2^b)` along `a = b`. -/
def castPerm {a b : ℕ} (h : a = b) (σ : Equiv.Perm (Fin (2 ^ a))) :
    Equiv.Perm (Fin (2 ^ b)) :=
  (finCongr (congrArg (2 ^ ·) h)).permCongr σ

set_option maxHeartbeats 2000000 in
/-- `kronPow` of two permutation matrices is the permutation matrix of the
product permutation. Mirrors `kronPow_diagonal`'s indicator-of-conjunction. -/
theorem kronPow_permMatrix {a b : ℕ}
    (σ : Equiv.Perm (Fin (2 ^ a))) (τ : Equiv.Perm (Fin (2 ^ b))) :
    kronPow (σ.permMatrix ℂ) (τ.permMatrix ℂ) = (prodPerm σ τ).permMatrix ℂ := by
  ext i j
  rw [kronPow_apply]
  have hi1 : ((sqEquiv a b).symm i).1 = ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ :=
    Fin.ext (sqEquiv_symm_fst i)
  have hi2 : ((sqEquiv a b).symm i).2 = ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩ :=
    Fin.ext (sqEquiv_symm_snd i)
  have hj1 : ((sqEquiv a b).symm j).1 = ⟨(j : ℕ) / 2 ^ b, kron_div_lt j⟩ :=
    Fin.ext (sqEquiv_symm_fst j)
  have hj2 : ((sqEquiv a b).symm j).2 = ⟨(j : ℕ) % 2 ^ b, kron_mod_lt j⟩ :=
    Fin.ext (sqEquiv_symm_snd j)
  have key : (j = prodPerm σ τ i) ↔
      ((⟨(j : ℕ) / 2 ^ b, kron_div_lt j⟩ : Fin (2 ^ a)) = σ ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ ∧
       (⟨(j : ℕ) % 2 ^ b, kron_mod_lt j⟩ : Fin (2 ^ b)) = τ ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩) := by
    rw [prodPerm, Equiv.permCongr_apply, ← Equiv.symm_apply_eq, Equiv.prodCongr_apply,
      Prod.ext_iff, Prod.map_fst, Prod.map_snd, hi1, hi2, hj1, hj2]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  simp only [key]
  by_cases h1 : (⟨(j : ℕ) / 2 ^ b, kron_div_lt j⟩ : Fin (2 ^ a)) = σ ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ <;>
    by_cases h2 : (⟨(j : ℕ) % 2 ^ b, kron_mod_lt j⟩ : Fin (2 ^ b)) = τ ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩ <;>
    simp [h1, h2]

/-- `castSq` of a permutation matrix is the permutation matrix of the transported
permutation. -/
theorem castSq_permMatrix {a b : ℕ} (h : a = b) (σ : Equiv.Perm (Fin (2 ^ a))) :
    castSq h (σ.permMatrix ℂ) = (castPerm h σ).permMatrix ℂ := by
  subst h
  have hp : castPerm rfl σ = σ := by
    ext x
    simp [castPerm, finCongr_refl]
  rw [castSq_rfl, hp]

/-! ### i08 — `prodPerm` / `castPerm` square lemmas (quarantine reopen, append-only)

Group-homomorphism-style lemmas for the permutation lifts, mirroring
`kronPow_one/_mul` + `castSq_one/_mul` at the `Equiv.Perm` level. They unfold
`permCongr`/`prodCongr`/`finCongr`. Downstream (Swap/Route) consumes only the
clean statements. -/

theorem prodPerm_one {a b : ℕ} :
    prodPerm (1 : Equiv.Perm (Fin (2 ^ a))) (1 : Equiv.Perm (Fin (2 ^ b))) = 1 := by
  ext x
  simp [prodPerm, Equiv.permCongr_apply, Equiv.prodCongr_apply, Prod.map]

theorem prodPerm_mul {a b : ℕ} (σ σ' : Equiv.Perm (Fin (2 ^ a)))
    (τ τ' : Equiv.Perm (Fin (2 ^ b))) :
    prodPerm σ τ * prodPerm σ' τ' = prodPerm (σ * σ') (τ * τ') := by
  ext x
  simp only [prodPerm, Equiv.Perm.mul_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Equiv.prodCongr_apply]
  congr 1

theorem castPerm_one {a b : ℕ} (h : a = b) :
    castPerm h (1 : Equiv.Perm (Fin (2 ^ a))) = 1 := by
  subst h; ext x; simp [castPerm, finCongr_refl]

theorem castPerm_mul {a b : ℕ} (h : a = b) (σ τ : Equiv.Perm (Fin (2 ^ a))) :
    castPerm h σ * castPerm h τ = castPerm h (σ * τ) := by
  subst h; ext x
  simp [castPerm, finCongr_refl, Equiv.Perm.mul_apply]

/-! ### i08 — div/mod value handles for the `bitSwap_testBit` crux

These re-enter the `sqEquiv`/`prodCongr` internals to expose how `prodPerm` /
`castPerm` act on the high (`/2^b`) and low (`%2^b`) parts of an index. They
export clean Nat-level equalities. Swap.lean consumes only these. -/

theorem prodPerm_apply_div {a b : ℕ} (σ : Equiv.Perm (Fin (2 ^ a)))
    (τ : Equiv.Perm (Fin (2 ^ b))) (i : Fin (2 ^ (a + b))) :
    (prodPerm σ τ i : ℕ) / 2 ^ b = (σ ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ : ℕ) := by
  have hi1 : ((sqEquiv a b).symm i).1 = ⟨(i : ℕ) / 2 ^ b, kron_div_lt i⟩ :=
    Fin.ext (sqEquiv_symm_fst i)
  rw [← sqEquiv_symm_fst (prodPerm σ τ i), prodPerm, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map_fst, hi1]

theorem prodPerm_apply_mod {a b : ℕ} (σ : Equiv.Perm (Fin (2 ^ a)))
    (τ : Equiv.Perm (Fin (2 ^ b))) (i : Fin (2 ^ (a + b))) :
    (prodPerm σ τ i : ℕ) % 2 ^ b = (τ ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩ : ℕ) := by
  have hi2 : ((sqEquiv a b).symm i).2 = ⟨(i : ℕ) % 2 ^ b, kron_mod_lt i⟩ :=
    Fin.ext (sqEquiv_symm_snd i)
  rw [← sqEquiv_symm_snd (prodPerm σ τ i), prodPerm, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map_snd, hi2]

theorem castPerm_apply_val {a b : ℕ} (h : a = b) (σ : Equiv.Perm (Fin (2 ^ a)))
    (i : Fin (2 ^ b)) :
    ((castPerm h σ i : ℕ)) = (σ ⟨(i : ℕ), by subst h; exact i.isLt⟩ : ℕ) := by
  subst h
  have hpp : castPerm (rfl : a = a) σ = σ := by ext x; simp [castPerm, finCongr_refl]
  rw [hpp]

end QpuCompiler
