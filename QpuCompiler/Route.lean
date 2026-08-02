/-
QpuCompiler/Route.lean — THE ROUTING ALGORITHM (iteration 07, capstone part 1).

The phase-accumulating swap-network fold, `swapNet` HWF, the single-CZ routing
definition `route1cz` with its HWF, and a concrete-example soundness witness.

Discipline: everything works at the `permDenote`/`Matrix` level. The KronPow
quarantine (`castSq`/`kronPow`/`prodPerm`/`castPerm`) is never unfolded here.
-/
import QpuCompiler.Swap

namespace QpuCompiler

open Matrix

/-! ## The fold — circuit side and index side -/

/-- A swap network: a right-nested `.seq` of adjacent swaps, one per index in the
list. Empty network is the derived skip `.app1 .id 0`. -/
def swapNet (n : ℕ) : List ℕ → UCom n
  | []      => .app1 .id 0
  | p :: ps => .seq (swapAdj n p) (swapNet n ps)

/-- Index-side mirror of `swapNet`: the product of the bit-swap permutations. -/
def bitSwapProd (n : ℕ) : List ℕ → Equiv.Perm (Fin (2 ^ n))
  | []      => 1
  | p :: ps => Layout.bitSwap n p * bitSwapProd n ps

/-- The fold lemma: `swapNet` denotes to the permutation matrix of the mirrored
bit-swap product, up to a global phase (phases accumulate additively). -/
theorem denote_swapNet {n : ℕ} (hn : 0 < n) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p + 1 < n) :
    ∃ θ : ℝ, denote (swapNet n ps)
      = Complex.exp (θ * Complex.I) • Layout.permDenote (bitSwapProd n ps) := by
  induction ps with
  | nil =>
    refine ⟨0, ?_⟩
    simp only [swapNet, denote, Gate1.matrix, bitSwapProd, Layout.permDenote_one,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    exact padU_one (by omega)
  | cons p ps ih =>
    obtain ⟨θp, hp⟩ := denote_swapAdj_bitSwap (hps p List.mem_cons_self)
    obtain ⟨θps, hps'⟩ := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    refine ⟨θp + θps, ?_⟩
    show denote (swapNet n ps) * denote (swapAdj n p)
        = Complex.exp (↑(θp + θps) * Complex.I) • Layout.permDenote (bitSwapProd n (p :: ps))
    rw [hp, hps', smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
      show ((θps : ℝ) : ℂ) * Complex.I + ((θp : ℝ) : ℂ) * Complex.I
          = ((θp + θps : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      ← Layout.permDenote_mul, bitSwapProd]

/-! ## `swapNet` hardware well-formedness -/

theorem swapNet_HWF {n : ℕ} (hn : 0 < n) (ps : List ℕ)
    (hps : ∀ p ∈ ps, (lnnPath n).edge p (p + 1) = true) :
    HWF (lnnPath n) (swapNet n ps) := by
  induction ps with
  | nil => exact .app1 hn
  | cons p ps ih =>
    exact .seq (swapAdj_HWF (hps p List.mem_cons_self))
      (ih (fun q hq => hps q (List.mem_cons_of_mem p hq)))

/-! ## Move-list construction -/

/-- The list of adjacent-swap positions that carries a qubit from `i` to `j`
(ascending `range'` if `i ≤ j`, else the descending reverse). -/
def moveList (i j : ℕ) : List ℕ :=
  if i ≤ j then List.range' i (j - i)
  else (List.range' j (i - j)).reverse

/-- Every position in `moveList i j` is a valid adjacent-swap low index, that is,
`p + 1 < n`, given both endpoints are `< n`. -/
theorem moveList_mem_bound {n i j : ℕ} (hi : i < n) (hj : j < n) :
    ∀ p ∈ moveList i j, p + 1 < n := by
  intro p hp
  unfold moveList at hp
  split at hp
  · rw [List.mem_range'] at hp; omega
  · rw [List.mem_reverse, List.mem_range'] at hp; omega

/-- A move network realizing `moveList i j`. -/
def moveAdj (n i j : ℕ) : UCom n := swapNet n (moveList i j)

theorem moveAdj_HWF {n i j : ℕ} (hn : 0 < n) (hi : i < n) (hj : j < n) :
    HWF (lnnPath n) (moveAdj n i j) := by
  refine swapNet_HWF hn (moveList i j) (fun p hp => ?_)
  have hb := moveList_mem_bound hi hj p hp
  simp only [lnnPath, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨Or.inl trivial, ?_⟩, ?_⟩ <;> omega

/-! ## Single-CZ routing -/

/-- Route a single `cz a b` (`a + 1 < b`): move `b` down to `a + 1`, apply the
native `cz a (a+1)`, then move it back. Returns to the original layout. -/
def route1cz (n a b : ℕ) : UCom n :=
  .seq (.seq (moveAdj n b (a + 1)) (.cz a (a + 1))) (moveAdj n (a + 1) b)

theorem route1cz_HWF {n a b : ℕ} (hab : a + 1 < b) (hb : b < n) :
    HWF (lnnPath n) (route1cz n a b) := by
  have hn : 0 < n := by omega
  have hedge : (lnnPath n).edge a (a + 1) = true := by
    simp only [lnnPath, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    refine ⟨⟨Or.inl trivial, ?_⟩, ?_⟩ <;> omega
  exact .seq (.seq (moveAdj_HWF hn (by omega) (by omega)) (.cz hedge))
    (moveAdj_HWF hn (by omega) (by omega))

/-! ## Concrete soundness witness -/

set_option maxHeartbeats 2000000 in
theorem bitConj3_example :
    Layout.permDenote (Layout.bitSwap 3 1) = !![
      (1:ℂ),0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0;
      0,0,0,0,0,1,0,0;
      0,0,1,0,0,0,0,0;
      0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,1] := by
  unfold Layout.permDenote Equiv.Perm.permMatrix
  ext i j
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  fin_cases i <;> fin_cases j <;> simp <;> decide

set_option maxHeartbeats 2000000 in
/-- The residual index identity: conjugating `padCZ 3 0 1` by the (self-inverse)
bit-swap of bits 1,2 yields `padCZ 3 0 2`. -/
theorem conj_identity_example :
    Layout.permDenote (Layout.bitSwap 3 1) *
      (padCZ 3 0 1 * Layout.permDenote (Layout.bitSwap 3 1)) = padCZ 3 0 2 := by
  rw [bitConj3_example]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, padCZ, Matrix.diagonal_apply,
      Nat.testBit_eq_decide_div_mod_eq]

set_option maxHeartbeats 2000000 in
theorem route1cz_congPhase_example :
    UCom.CongPhase (route1cz 3 0 2) (.cz 0 2) := by
  obtain ⟨θ, hθ⟩ := denote_swapNet (n := 3) (by omega) [1]
    (by intro p hp; simp only [List.mem_singleton] at hp; omega)
  refine UCom.CongPhase.of_phase (θ + θ) ?_
  simp only [route1cz, denote]
  rw [show moveAdj 3 1 2 = swapNet 3 [1] from rfl,
      show moveAdj 3 2 1 = swapNet 3 [1] from rfl, hθ,
      show bitSwapProd 3 [1] = Layout.bitSwap 3 1 from by simp [bitSwapProd]]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
      show ((θ : ℝ) : ℂ) * Complex.I + ((θ : ℝ) : ℂ) * Complex.I
          = ((θ + θ : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  congr 1
  exact conj_identity_example

/-! ## i08 — general routing soundness (FLOOR: matrix/list algebra) -/

/-- Conjugating a diagonal by a permutation matrix and its inverse collapses to a
reindexed diagonal. Generic PEquiv algebra. No `bitSwap`. -/
theorem permMatrix_conj_diagonal {N : Type*} [Fintype N] [DecidableEq N]
    (P Q : Equiv.Perm N) (d : N → ℂ) (h : P = Q.symm) :
    P.permMatrix ℂ * Matrix.diagonal d * Q.permMatrix ℂ
      = Matrix.diagonal (d ∘ Q.symm) := by
  rw [Matrix.mul_assoc,
      show (P.permMatrix ℂ) = P.toPEquiv.toMatrix from rfl,
      show (Q.permMatrix ℂ) = Q.toPEquiv.toMatrix from rfl,
      PEquiv.mul_toMatrix_toPEquiv,
      PEquiv.toMatrix_toPEquiv_mul,
      Matrix.submatrix_submatrix, h]
  simp only [Function.comp_id, Function.id_comp]
  rw [Matrix.submatrix_diagonal_equiv]

theorem bitSwapProd_append {n : ℕ} (ps qs : List ℕ) :
    bitSwapProd n (ps ++ qs) = bitSwapProd n ps * bitSwapProd n qs := by
  induction ps with
  | nil => simp [bitSwapProd]
  | cons p ps ih => simp only [List.cons_append, bitSwapProd, ih, mul_assoc]

theorem bitSwapProd_reverse {n : ℕ} (ps : List ℕ) :
    bitSwapProd n ps.reverse = (bitSwapProd n ps)⁻¹ := by
  induction ps with
  | nil => simp [bitSwapProd]
  | cons p ps ih =>
    rw [List.reverse_cons, bitSwapProd_append, ih]
    show (bitSwapProd n ps)⁻¹ * bitSwapProd n [p]
        = (Layout.bitSwap n p * bitSwapProd n ps)⁻¹
    rw [_root_.mul_inv_rev]
    simp only [bitSwapProd, mul_one]
    congr 1
    exact (inv_eq_of_mul_eq_one_right Layout.bitSwap_mul_self).symm

/-! ## i08 — TARGET: the conjugation induction ⇒ general `route1cz_congPhase` -/

set_option maxHeartbeats 2000000 in
/-- Conjugating `padCZ n a c` by the self-inverse `bitSwap n q` (with `a < q`, so
the `a`-bit is fixed) transports the second CZ index `c` by `swap q (q+1)`. -/
theorem conj_bitSwap_padCZ {n a q c : ℕ} (hq : q + 2 ≤ n) (haq : a < q)
    (hc : c < n) (hac : a ≠ c) :
    Layout.permDenote (Layout.bitSwap n q) * padCZ n a c
        * Layout.permDenote (Layout.bitSwap n q)
      = padCZ n a (Equiv.swap q (q + 1) c) := by
  have hself : Layout.bitSwap n q = (Layout.bitSwap n q).symm := by
    rw [← Equiv.Perm.inv_def, inv_eq_of_mul_eq_one_right Layout.bitSwap_mul_self]
  have hcond : a < n ∧ c < n ∧ a ≠ c := ⟨by omega, hc, hac⟩
  have hswap_lt : Equiv.swap q (q + 1) c < n := by
    rw [Equiv.swap_apply_def]; split_ifs <;> omega
  have hne : a ≠ Equiv.swap q (q + 1) c := by
    rw [Equiv.swap_apply_def]; split_ifs <;> omega
  simp only [Layout.permDenote]
  rw [padCZ, if_pos hcond, permMatrix_conj_diagonal _ _ _ hself,
      padCZ, if_pos ⟨by omega, hswap_lt, hne⟩]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [← hself, Layout.bitSwap_testBit hq, Layout.bitSwap_testBit hq,
      Equiv.swap_apply_of_ne_of_ne (by omega : a ≠ q) (by omega : a ≠ q + 1)]

set_option maxHeartbeats 2000000 in
/-- General analog of `conj_bitSwap_padCZ`: conjugating `padCZ n a c` by the
self-inverse `bitSwap' n u v` transposes BOTH CZ indices by `swap u v`. -/
theorem conj_bitSwap'_padCZ {n u v a c : ℕ}
    (hu : u < n) (hv : v < n) (ha : a < n) (hc : c < n) (hac : a ≠ c) :
    Layout.permDenote (Layout.bitSwap' n u v) * padCZ n a c
        * Layout.permDenote (Layout.bitSwap' n u v)
      = padCZ n (Equiv.swap u v a) (Equiv.swap u v c) := by
  have hself : Layout.bitSwap' n u v = (Layout.bitSwap' n u v).symm := by
    rw [← Equiv.Perm.inv_def, inv_eq_of_mul_eq_one_right Layout.bitSwap'_mul_self]
  have hsa : Equiv.swap u v a < n := by
    rw [Equiv.swap_apply_def]; split_ifs <;> omega
  have hsc : Equiv.swap u v c < n := by
    rw [Equiv.swap_apply_def]; split_ifs <;> omega
  have hsne : Equiv.swap u v a ≠ Equiv.swap u v c := fun hh =>
    hac ((Equiv.swap u v).injective hh)
  simp only [Layout.permDenote]
  rw [padCZ, if_pos ⟨ha, hc, hac⟩, permMatrix_conj_diagonal _ _ _ hself,
      padCZ, if_pos ⟨hsa, hsc, hsne⟩]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [← hself, Layout.bitSwap'_testBit hu hv, Layout.bitSwap'_testBit hu hv]

/-- Applying the chain of adjacent swaps `range' m k` (left to right) to the
starting index `m` walks it up to `m + k`. -/
theorem foldl_swap_range' (m k : ℕ) :
    (List.range' m k).foldl (fun x q => Equiv.swap q (q + 1) x) m = m + k := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ, List.foldl_cons, Equiv.swap_apply_left, ih (m + 1)]
    omega

set_option maxHeartbeats 2000000 in
/-- The conjugation induction: conjugating `padCZ n a c` by the product of the
bit-swaps in `ps` (each position `q` with `a < q`) transports `c` by the fold of
`swap q (q+1)` along `ps`. The back leg is the reversed product. -/
theorem bitSwapProd_conj_padCZ {n a : ℕ} (ps : List ℕ)
    (hps : ∀ q ∈ ps, a < q ∧ q + 2 ≤ n) :
    ∀ c, c < n → a ≠ c →
      Layout.permDenote (bitSwapProd n ps) * padCZ n a c
          * Layout.permDenote (bitSwapProd n ps.reverse)
        = padCZ n a (ps.foldl (fun x q => Equiv.swap q (q + 1) x) c) := by
  induction ps with
  | nil =>
    intro c _ _
    simp [bitSwapProd, Layout.permDenote_one]
  | cons p ps ih =>
    intro c hc hac
    obtain ⟨hap, hpn⟩ := hps p List.mem_cons_self
    have hps' : ∀ q ∈ ps, a < q ∧ q + 2 ≤ n := fun q hq => hps q (List.mem_cons_of_mem p hq)
    have hc' : Equiv.swap p (p + 1) c < n := by rw [Equiv.swap_apply_def]; split_ifs <;> omega
    have hac' : a ≠ Equiv.swap p (p + 1) c := by rw [Equiv.swap_apply_def]; split_ifs <;> omega
    rw [bitSwapProd, List.reverse_cons, bitSwapProd_append]
    simp only [bitSwapProd, mul_one, Layout.permDenote_mul]
    set A := Layout.permDenote (bitSwapProd n ps) with hA
    set Ar := Layout.permDenote (bitSwapProd n ps.reverse) with hAr
    set B := Layout.permDenote (Layout.bitSwap n p) with hB
    rw [mul_assoc A B (padCZ n a c), ← mul_assoc (A * (B * padCZ n a c)) B Ar,
        mul_assoc A (B * padCZ n a c) B, conj_bitSwap_padCZ hpn hap hc hac,
        ih hps' (Equiv.swap p (p + 1) c) hc' hac', List.foldl_cons]

set_option maxHeartbeats 2000000 in
/-- **Headline (TARGET).** Routing a single distant `cz a b` (`a+1 < b`) through the
move-network is correct up to a global phase. -/
theorem route1cz_congPhase {n a b : ℕ} (hab : a + 1 < b) (hb : b < n) :
    UCom.CongPhase (route1cz n a b) (.cz a b) := by
  have hn : 0 < n := by omega
  have han : a + 1 < n := by omega
  obtain ⟨θ1, hθ1⟩ := denote_swapNet (n := n) hn (moveList (a + 1) b)
    (moveList_mem_bound han hb)
  obtain ⟨θ2, hθ2⟩ := denote_swapNet (n := n) hn (moveList b (a + 1))
    (moveList_mem_bound hb han)
  have hrev : moveList b (a + 1) = (moveList (a + 1) b).reverse := by
    unfold moveList; rw [if_neg (by omega), if_pos (by omega)]
  have hrange : moveList (a + 1) b = List.range' (a + 1) (b - (a + 1)) := by
    unfold moveList; rw [if_pos (by omega)]
  have hps : ∀ q ∈ moveList (a + 1) b, a < q ∧ q + 2 ≤ n := by
    intro q hq
    rw [hrange, List.mem_range'_1] at hq
    omega
  refine UCom.CongPhase.of_phase (θ1 + θ2) ?_
  simp only [route1cz, denote]
  rw [show moveAdj n (a + 1) b = swapNet n (moveList (a + 1) b) from rfl,
      show moveAdj n b (a + 1) = swapNet n (moveList b (a + 1)) from rfl, hθ1, hθ2]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
      show ((θ1 : ℝ) : ℂ) * Complex.I + ((θ2 : ℝ) : ℂ) * Complex.I
          = ((θ1 + θ2 : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  congr 1
  rw [hrev, ← mul_assoc,
      bitSwapProd_conj_padCZ (moveList (a + 1) b) hps (a + 1) han (by omega),
      hrange, foldl_swap_range', show (a + 1) + (b - (a + 1)) = b from by omega]

end QpuCompiler
