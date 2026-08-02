/-
QpuCompiler/Swap.lean — SWAP-routing block, part 1 (iteration 05).

SWAP on the adjacent pair `(q, q+1)` is a *derived native macro* over
`{cz, sx, rz}`, not a new `UCom` constructor. Thus every exhaustive match in
the accepted stack stays unchanged. Contents:

* `namespace Layout` — index-level `Equiv.Perm (Fin (2^n))` → `permMatrix`
  algebra (the layout bank for i06 routing).
* `swapAdj` macro (H = rz(1/2);sx;rz(1/2); CNOT = H;CZ;H; SWAP = 3·CNOT) with
  `WF` / `HWF` / unitarity.
* `padTwo` — 2-qubit placement on the adjacent pair — cloned from the `padU`
  family, plus the two placement bridges (A: two `padU`s equal one `padTwo`.
  B: `padCZ` equals `padTwo CZ4`).
* the stretch denotation identity `denote_swapAdj`.

Quarantine discipline: this file never unfolds `castSq`, `kronPow`, or
`reindex`. It applies only the exported KronPow lemmas.
-/
import QpuCompiler.Hardware
import Mathlib.LinearAlgebra.Matrix.Swap

namespace QpuCompiler

open Matrix

/-! ## Index-level permutation algebra (`namespace Layout`)

The *layout* is an index-level permutation `σ : Equiv.Perm (Fin (2^n))`. Its
denotation is the permutation matrix. Mathlib does all the algebra. This is
banked for i06 (qubit→bit tensor lift). -/

namespace Layout

/-- Denote an index-level permutation as its permutation matrix. -/
noncomputable def permDenote {n : ℕ} (σ : Equiv.Perm (Fin (2 ^ n))) : Square n :=
  σ.permMatrix ℂ

@[simp] theorem permDenote_one {n : ℕ} :
    permDenote (1 : Equiv.Perm (Fin (2 ^ n))) = 1 := by
  unfold permDenote
  exact Matrix.permMatrix_one

/-- ANTIHOMOMORPHISM orientation (matches `Matrix.permMatrix_mul`). -/
theorem permDenote_mul {n : ℕ} (σ τ : Equiv.Perm (Fin (2 ^ n))) :
    permDenote (σ * τ) = permDenote τ * permDenote σ := by
  simp only [permDenote, Matrix.permMatrix_mul]

theorem permDenote_mem_unitaryGroup {n : ℕ} (σ : Equiv.Perm (Fin (2 ^ n))) :
    permDenote σ ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permDenote,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

/-- The 4×4 SWAP spec object (index-level swap of `1` and `2`). -/
noncomputable def swap4 : Square 2 := Matrix.swap ℂ (1 : Fin 4) (2 : Fin 4)

/-- The index permutation on `Fin (2^n)` that swaps bits `q` and `q+1`
(little-endian), that is, the layout an adjacent SWAP on `(q, q+1)` realizes.
Total: `1` when out of range. Shape mirrors `padTwo`'s
`castSq (kronPow (kronPow 1 M) 1)` exactly. -/
def bitSwap (n q : ℕ) : Equiv.Perm (Fin (2 ^ n)) :=
  if h : q + 2 ≤ n then
    castPerm (show (n - (q + 2)) + 2 + q = n by omega)
      (prodPerm (prodPerm (1 : Equiv.Perm (Fin (2 ^ (n - (q + 2)))))
                          (Equiv.swap (1 : Fin (2 ^ 2)) (2 : Fin (2 ^ 2))))
                (1 : Equiv.Perm (Fin (2 ^ q))))
  else 1

theorem permDenote_bitSwap_unitary {n q : ℕ} :
    permDenote (bitSwap n q) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  permDenote_mem_unitaryGroup _

/-! ### Fixed-`n` decidable sanity — `bitSwap 4 1` exchanges bit 1 and bit 2. -/

/-! ### i08 — `bitSwap` involutivity (consumes the KronPow square lemmas). -/

theorem bitSwap_mul_self {n q : ℕ} : bitSwap n q * bitSwap n q = 1 := by
  unfold bitSwap
  by_cases h : q + 2 ≤ n
  · rw [dif_pos h, castPerm_mul, prodPerm_mul, prodPerm_mul, Equiv.swap_mul_self]
    simp only [mul_one, prodPerm_one, castPerm_one]
  · rw [dif_neg h, mul_one]

/-! ### i08 — the `bitSwap_testBit` crux (unfolds `bitSwap`, consumes KronPow
value handles + `Nat.testBit_*`). -/

/-- Bit 0 of the `Fin 4` transposition `(1 2)` applied to `x` equals bit 1 of `x`. -/
theorem swap4val_testBit0 (x : Fin (2 ^ 2)) :
    Nat.testBit ((Equiv.swap (1 : Fin (2 ^ 2)) (2 : Fin (2 ^ 2)) x : ℕ)) 0
      = Nat.testBit (x : ℕ) 1 := by
  fin_cases x <;> decide

/-- Bit 1 of the `Fin 4` transposition `(1 2)` applied to `x` equals bit 0 of `x`. -/
theorem swap4val_testBit1 (x : Fin (2 ^ 2)) :
    Nat.testBit ((Equiv.swap (1 : Fin (2 ^ 2)) (2 : Fin (2 ^ 2)) x : ℕ)) 1
      = Nat.testBit (x : ℕ) 0 := by
  fin_cases x <;> decide

/-- Divide-then-`testBit` shifts the bit index. -/
theorem testBit_div_two_pow (x s t : ℕ) :
    Nat.testBit (x / 2 ^ s) t = Nat.testBit x (s + t) := by
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

set_option maxHeartbeats 2000000 in
/-- **The crux.** `bitSwap n q` swaps bits `q` and `q+1` of the index and fixes
all other bits: `testBit (bitSwap n q i) k = testBit i (swap q (q+1) k)`. -/
theorem bitSwap_testBit {n q : ℕ} (h : q + 2 ≤ n) (i : Fin (2 ^ n)) (k : ℕ) :
    Nat.testBit ((bitSwap n q) i : ℕ) k
      = Nat.testBit (i : ℕ) (Equiv.swap q (q + 1) k) := by
  -- low q bits are unchanged
  have hWmod : ((bitSwap n q) i : ℕ) % 2 ^ q = (i : ℕ) % 2 ^ q := by
    rw [bitSwap, dif_pos h, castPerm_apply_val, prodPerm_apply_mod]
    simp
  -- high bits: 2-bit middle block gets `swap (1 2)`, the rest is fixed
  have hWdiv : ((bitSwap n q) i : ℕ) / 2 ^ q
      = 2 ^ 2 * ((i : ℕ) / 2 ^ q / 2 ^ 2)
        + (Equiv.swap (1 : Fin (2 ^ 2)) (2 : Fin (2 ^ 2))
            ⟨(i : ℕ) / 2 ^ q % 2 ^ 2, Nat.mod_lt _ (Nat.two_pow_pos 2)⟩ : ℕ) := by
    rw [bitSwap, dif_pos h, castPerm_apply_val, prodPerm_apply_div]
    refine (Nat.div_add_mod _ (2 ^ 2)).symm.trans ?_
    rw [prodPerm_apply_div, prodPerm_apply_mod]
    simp
  -- reconstruct the value from its low/high parts and split into bit ranges
  rw [show ((bitSwap n q) i : ℕ)
        = 2 ^ q * (((bitSwap n q) i : ℕ) / 2 ^ q) + ((bitSwap n q) i : ℕ) % 2 ^ q
      from (Nat.div_add_mod _ _).symm, hWdiv, hWmod,
      Nat.testBit_two_pow_mul_add _ (Nat.mod_lt (i : ℕ) (Nat.two_pow_pos q))]
  by_cases hk : k < q
  · -- below the swapped pair: bit fixed
    rw [if_pos hk, Nat.testBit_mod_two_pow,
        Equiv.swap_apply_of_ne_of_ne (by omega : k ≠ q) (by omega : k ≠ q + 1)]
    simp [hk]
  · rw [if_neg hk, Nat.testBit_two_pow_mul_add _ (Fin.isLt _)]
    rcases (show k - q = 0 ∨ k - q = 1 ∨ 2 ≤ k - q by omega) with hd | hd | hd
    · -- k = q : maps to bit q+1
      rw [if_pos (by omega), hd, swap4val_testBit0, Nat.testBit_mod_two_pow,
          testBit_div_two_pow, show k = q by omega, Equiv.swap_apply_left]
      simp
    · -- k = q+1 : maps to bit q
      rw [if_pos (by omega), hd, swap4val_testBit1, Nat.testBit_mod_two_pow,
          testBit_div_two_pow, show k = q + 1 by omega, Equiv.swap_apply_right]
      simp
    · -- k ≥ q+2 : bit fixed
      rw [if_neg (by omega), testBit_div_two_pow, testBit_div_two_pow,
          Equiv.swap_apply_of_ne_of_ne (by omega : k ≠ q) (by omega : k ≠ q + 1)]
      congr 1
      omega

example : (bitSwap 4 1) 2 = 4 := by decide   -- 0b0010 ↦ 0b0100
example : (bitSwap 4 1) 4 = 2 := by decide   -- 0b0100 ↦ 0b0010
example : (bitSwap 4 1) 6 = 6 := by decide   -- bits 1,2 both set: fixed
example : (bitSwap 4 1) 0 = 0 := by decide

/-! ### i10 — general (non-adjacent) bit transposition `bitSwap'`.
This is an XOR-conditional Nat map, lifted via `Function.Involutive.toPerm`.
It stays at the `Nat.testBit` level (no `sqEquiv`/`prodPerm` internals). -/

/-- Swap bits `u,v` of `i`: flip both iff they differ (XOR with `2^u ||| 2^v`). -/
def natBitSwap (u v i : ℕ) : ℕ :=
  if i.testBit u = i.testBit v then i else i ^^^ (2 ^ u ||| 2 ^ v)

/-- **Crux (elementary).** Bit `k` of `natBitSwap u v i` is bit `swap u v k` of `i`. -/
theorem natBitSwap_testBit (u v i k : ℕ) :
    (natBitSwap u v i).testBit k = i.testBit (Equiv.swap u v k) := by
  unfold natBitSwap
  by_cases h : i.testBit u = i.testBit v
  · rw [if_pos h]
    rcases eq_or_ne k u with rfl | hku
    · rw [Equiv.swap_apply_left, h]
    · rcases eq_or_ne k v with rfl | hkv
      · rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hku hkv]
  · rw [if_neg h, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow, Nat.testBit_two_pow]
    rcases eq_or_ne k u with rfl | hku
    · rw [Equiv.swap_apply_left]
      simp only [decide_true, Bool.true_or]
      revert h; cases i.testBit k <;> cases i.testBit v <;> decide
    · rcases eq_or_ne k v with rfl | hkv
      · rw [Equiv.swap_apply_right]
        simp only [decide_true, Bool.or_true]
        revert h; cases i.testBit u <;> cases i.testBit k <;> decide
      · rw [Equiv.swap_apply_of_ne_of_ne hku hkv,
            decide_eq_false (Ne.symm hku), decide_eq_false (Ne.symm hkv)]
        simp

/-- `natBitSwap` maps `[0, 2^n)` into itself when `u,v < n`. -/
theorem natBitSwap_lt {n u v : ℕ} (hu : u < n) (hv : v < n) {i : ℕ} (hi : i < 2 ^ n) :
    natBitSwap u v i < 2 ^ n := by
  unfold natBitSwap
  split
  · exact hi
  · exact Nat.xor_lt_two_pow hi
      (Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) hu)
                         (Nat.pow_lt_pow_right (by decide) hv))

/-- The `Fin (2^n)` bit-transposition. Total: identity when `u,v` out of range. -/
def bitSwap' (n u v : ℕ) : Equiv.Perm (Fin (2 ^ n)) :=
  if h : u < n ∧ v < n then
    Function.Involutive.toPerm
      (fun i : Fin (2 ^ n) => ⟨natBitSwap u v i, natBitSwap_lt h.1 h.2 i.isLt⟩)
      (fun i => Fin.ext (by
        show natBitSwap u v (natBitSwap u v (i : ℕ)) = (i : ℕ)
        refine Nat.eq_of_testBit_eq (fun k => ?_)
        rw [natBitSwap_testBit, natBitSwap_testBit, Equiv.swap_apply_self]))
  else 1

theorem permDenote_bitSwap'_unitary {n u v : ℕ} :
    permDenote (bitSwap' n u v) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  permDenote_mem_unitaryGroup _

/-- `bitSwap'` swaps bits `u,v` of the index (positive branch). -/
theorem bitSwap'_testBit {n u v : ℕ} (hu : u < n) (hv : v < n)
    (i : Fin (2 ^ n)) (k : ℕ) :
    ((bitSwap' n u v) i : ℕ).testBit k = (i : ℕ).testBit (Equiv.swap u v k) := by
  rw [bitSwap', dif_pos ⟨hu, hv⟩]
  simp only [Function.Involutive.coe_toPerm]
  exact natBitSwap_testBit u v (i : ℕ) k

theorem bitSwap'_mul_self {n u v : ℕ} : bitSwap' n u v * bitSwap' n u v = 1 := by
  by_cases h : u < n ∧ v < n
  · ext i
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
    refine Nat.eq_of_testBit_eq (fun k => ?_)
    rw [bitSwap'_testBit h.1 h.2, bitSwap'_testBit h.1 h.2, Equiv.swap_apply_self]
  · rw [bitSwap', dif_neg h, mul_one]

/-! ### i11 — CNOT as an index permutation `cnotPerm` (mirror `bitSwap'`).
`natCnot u v` flips bit `v` iff bit `u` is set (the classical CNOT action).
It is lifted to `Equiv.Perm (Fin (2^n))` via `Function.Involutive.toPerm`.
Involutivity needs `u ≠ v`. It stays at the `Nat.testBit` level. -/

/-- CNOT (control `u`, target `v`) as a Nat map: flip bit `v` iff bit `u` set. -/
def natCnot (u v i : ℕ) : ℕ := if i.testBit u then i ^^^ 2 ^ v else i

/-- Bit `k` of `natCnot u v i`: bit `k` of `i`, XOR-flipped at `k = v` iff bit `u` set. -/
theorem natCnot_testBit (u v i k : ℕ) :
    (natCnot u v i).testBit k
      = (if i.testBit u then i.testBit k ^^ decide (k = v) else i.testBit k) := by
  unfold natCnot
  split
  · rw [Nat.testBit_xor]
    congr 1
    rw [Nat.testBit_two_pow]
    exact decide_eq_decide.mpr eq_comm
  · rfl

/-- `natCnot` maps `[0, 2^n)` into itself when `v < n`. -/
theorem natCnot_lt {n u v : ℕ} (hv : v < n) {i : ℕ} (hi : i < 2 ^ n) :
    natCnot u v i < 2 ^ n := by
  unfold natCnot
  split
  · exact Nat.xor_lt_two_pow hi (Nat.pow_lt_pow_right (by decide) hv)
  · exact hi

/-- `natCnot u v` is involutive when `u ≠ v` (it flips bit `v` twice and leaves bit `u` unchanged). -/
theorem natCnot_involutive {u v : ℕ} (huv : u ≠ v) (i : ℕ) :
    natCnot u v (natCnot u v i) = i := by
  refine Nat.eq_of_testBit_eq (fun k => ?_)
  have hbu : (natCnot u v i).testBit u = i.testBit u := by
    rw [natCnot_testBit]
    split
    · rw [decide_eq_false huv]; simp
    · rfl
  rw [natCnot_testBit, hbu]
  by_cases hu : i.testBit u
  · rw [if_pos hu, natCnot_testBit, if_pos hu]
    cases i.testBit k <;> cases hc : decide (k = v) <;> simp
  · rw [if_neg hu, natCnot_testBit, if_neg hu]

/-- The `Fin (2^n)` CNOT permutation. Total: identity when `u,v` out of range or `u = v`. -/
def cnotPerm (n u v : ℕ) : Equiv.Perm (Fin (2 ^ n)) :=
  if h : u < n ∧ v < n ∧ u ≠ v then
    Function.Involutive.toPerm
      (fun i : Fin (2 ^ n) => ⟨natCnot u v i, natCnot_lt h.2.1 i.isLt⟩)
      (fun i => Fin.ext (natCnot_involutive h.2.2 (i : ℕ)))
  else 1

theorem cnotPerm_val {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) (i : Fin (2 ^ n)) :
    ((cnotPerm n u v) i : ℕ) = natCnot u v (i : ℕ) := by
  rw [cnotPerm, dif_pos ⟨hu, hv, huv⟩]
  simp only [Function.Involutive.coe_toPerm]

theorem cnotPerm_testBit {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (i : Fin (2 ^ n)) (k : ℕ) :
    ((cnotPerm n u v) i : ℕ).testBit k
      = (if (i : ℕ).testBit u then (i : ℕ).testBit k ^^ decide (k = v)
         else (i : ℕ).testBit k) := by
  rw [cnotPerm_val hu hv huv, natCnot_testBit]

theorem permDenote_cnotPerm_unitary {n u v : ℕ} :
    permDenote (cnotPerm n u v) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  permDenote_mem_unitaryGroup _

end Layout

/-! ## `swapAdj` macro + well-formedness / hardware-legality / unitarity -/

variable {n : ℕ}

/-- Native Hadamard at wire `q`, up to global phase: `rz(1/2); sx; rz(1/2)`. -/
def hMac (q : ℕ) : UCom n :=
  .seq (.seq (.app1 (.rz (1 / 2)) q) (.app1 .sx q)) (.app1 (.rz (1 / 2)) q)

/-- CNOT `a → b` via `H_b · CZ · H_b` (CZ symmetric ⇒ no direction fix). -/
def cnotMac (a b : ℕ) : UCom n :=
  .seq (.seq (hMac b) (.cz a b)) (hMac b)

/-- SWAP on the adjacent pair `(q, q+1)` = `CNOT q (q+1); CNOT (q+1) q; CNOT q (q+1)`. -/
def swapAdj (n q : ℕ) : UCom n :=
  .seq (.seq (cnotMac q (q + 1)) (cnotMac (q + 1) q)) (cnotMac q (q + 1))

/-! ### Well-formedness -/

theorem hMac_WF {q : ℕ} (h : q < n) : WF (hMac (n := n) q) :=
  .seq (.seq (.app1 h) (.app1 h)) (.app1 h)

theorem cnotMac_WF {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    WF (cnotMac (n := n) a b) :=
  .seq (.seq (hMac_WF hb) (.cz ha hb hab)) (hMac_WF hb)

theorem swapAdj_WF {n q : ℕ} (h : q + 1 < n) : WF (swapAdj n q) := by
  have hq : q < n := by omega
  have hne : q ≠ q + 1 := by omega
  exact .seq (.seq (cnotMac_WF hq h hne) (cnotMac_WF h hq (Ne.symm hne)))
    (cnotMac_WF hq h hne)

/-! ### Hardware well-formedness -/

theorem hMac_HWF {g : Coupling n} {q : ℕ} (h : q < n) : HWF g (hMac (n := n) q) :=
  .seq (.seq (.app1 h) (.app1 h)) (.app1 h)

theorem cnotMac_HWF {g : Coupling n} {a b : ℕ} (hb : b < n)
    (hab : g.edge a b = true) : HWF g (cnotMac (n := n) a b) :=
  .seq (.seq (hMac_HWF hb) (.cz hab)) (hMac_HWF hb)

theorem swapAdj_HWF {n : ℕ} {g : Coupling n} {q : ℕ}
    (h : g.edge q (q + 1) = true) : HWF g (swapAdj n q) := by
  obtain ⟨hq, hq1⟩ := g.edge_bounds q (q + 1) h
  have h' : g.edge (q + 1) q = true := by rw [g.edge_symm]; exact h
  exact .seq (.seq (cnotMac_HWF hq1 h) (cnotMac_HWF hq h')) (cnotMac_HWF hq1 h)

/-! ### Unitarity -/

theorem padU_gate_unitary {q : ℕ} (h : q + 1 ≤ n) (g : Gate1) :
    padU n q g.matrix ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  padU_mem_unitaryGroup h g.matrix_mem_unitaryGroup

theorem hMac_unitary {q : ℕ} (h : q + 1 ≤ n) :
    denote (hMac (n := n) q) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  unfold hMac
  simp only [denote]
  exact mul_mem (padU_gate_unitary h _)
    (mul_mem (padU_gate_unitary h _) (padU_gate_unitary h _))

theorem cnotMac_unitary {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hbn : b + 1 ≤ n) :
    denote (cnotMac (n := n) a b) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  unfold cnotMac
  simp only [denote]
  exact mul_mem (hMac_unitary hbn)
    (mul_mem (padCZ_mem_unitaryGroup ha hb hab) (hMac_unitary hbn))

theorem swapAdj_unitary {n q : ℕ} (h : q + 1 < n) :
    denote (swapAdj n q) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hq : q < n := by omega
  have hne : q ≠ q + 1 := by omega
  unfold swapAdj
  simp only [denote]
  have h1 := cnotMac_unitary hq h hne (by omega)
  have h2 := cnotMac_unitary h hq (Ne.symm hne) (by omega)
  exact mul_mem h1 (mul_mem h2 h1)

/-! ## i10 — general `swapEdge` macro on an arbitrary index-distinct pair -/

/-- SWAP on an arbitrary index-distinct pair `(u, v)` (a coupling edge):
`CNOT u v; CNOT v u; CNOT u v`. Generalizes `swapAdj` (= `swapEdge n q (q+1)`)
by using `cz u v` for arbitrary `u,v`. -/
def swapEdge (n u v : ℕ) : UCom n :=
  .seq (.seq (cnotMac u v) (cnotMac v u)) (cnotMac u v)

theorem swapEdge_WF {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    WF (swapEdge n u v) :=
  .seq (.seq (cnotMac_WF hu hv huv) (cnotMac_WF hv hu huv.symm)) (cnotMac_WF hu hv huv)

theorem swapEdge_HWF {n : ℕ} {g : Coupling n} {u v : ℕ}
    (h : g.edge u v = true) : HWF g (swapEdge n u v) := by
  obtain ⟨hu, hv⟩ := g.edge_bounds u v h
  have h' : g.edge v u = true := by rw [g.edge_symm]; exact h
  exact .seq (.seq (cnotMac_HWF hv h) (cnotMac_HWF hu h')) (cnotMac_HWF hv h)

theorem swapEdge_unitary {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    denote (swapEdge n u v) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  unfold swapEdge
  simp only [denote]
  have h1 := cnotMac_unitary hu hv huv (by omega)
  have h2 := cnotMac_unitary hv hu (Ne.symm huv) (by omega)
  exact mul_mem h1 (mul_mem h2 h1)

/-! ## `padTwo` — 2-qubit placement on the adjacent pair `(q, q+1)`

Structural clone of the `padU` family (`u : Square 1` ↦ `M : Square 2`,
`q+1 ≤ n` ↦ `q+2 ≤ n`). -/

/-- Embed a 2-qubit gate on the adjacent pair `(q, q+1)` (little-endian, `q` low):
    `I(2^(n-(q+2))) ⊗ M ⊗ I(2^q)`, `0` if `q+2 > n`. -/
noncomputable def padTwo (n q : ℕ) (M : Square 2) : Square n :=
  if h : q + 2 ≤ n then
    castSq (by omega) (kronPow (kronPow (1 : Square (n - (q + 2))) M) (1 : Square q))
  else 0

theorem padTwo_mul {n q : ℕ} (M N : Square 2) :
    padTwo n q M * padTwo n q N = padTwo n q (M * N) := by
  by_cases h : q + 2 ≤ n
  · simp only [padTwo, dif_pos h]
    rw [castSq_mul, ← kronPow_mul, ← kronPow_mul, one_mul, one_mul]
  · simp [padTwo, h]

theorem padTwo_one {n q : ℕ} (h : q + 2 ≤ n) : padTwo n q (1 : Square 2) = 1 := by
  simp only [padTwo, dif_pos h]
  rw [kronPow_one, kronPow_one, castSq_one]

theorem padTwo_mem_unitaryGroup {n q : ℕ} (h : q + 2 ≤ n) {M : Square 2}
    (hM : M ∈ Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ) :
    padTwo n q M ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  simp only [padTwo, dif_pos h]
  exact castSq_mem_unitaryGroup _
    (kronPow_mem_unitaryGroup (kronPow_mem_unitaryGroup (one_mem _) hM) (one_mem _))

theorem padTwo_smul {n q : ℕ} (c : ℂ) (M : Square 2) :
    padTwo n q (c • M) = c • padTwo n q M := by
  by_cases h : q + 2 ≤ n
  · simp only [padTwo, dif_pos h]
    rw [kronPow_smul_right, kronPow_smul_left, castSq_smul]
  · simp [padTwo, h]

/-! ### Bridge A — two `padU`s on the pair = one `padTwo` -/

theorem padU_hi_eq_padTwo {n q : ℕ} (u : Square 1) :
    padU n (q + 1) u = padTwo n q (kronPow u (1 : Square 1)) := by
  by_cases h : q + 2 ≤ n
  · rw [padU, dif_pos (by omega), padTwo, dif_pos h]
    -- split the low identity 1_{q+1} = castSq (kronPow 1_1 1_q)
    have e1 : (1 : Square (q + 1))
        = castSq (Nat.add_comm 1 q) (kronPow (1 : Square 1) (1 : Square q)) := by
      rw [kronPow_one, castSq_one]
    rw [e1, kronPow_castSq_right, castSq_castSq, ← kronPow_assoc',
      castSq_castSq]
    -- RHS: reassociate 1_m ⊗ (u ⊗ 1_1)
    rw [← kronPow_assoc', kronPow_castSq_left, castSq_castSq]
  · rw [padU, dif_neg (by omega), padTwo, dif_neg (by omega)]

/-- Unlike `padU_hi_eq_padTwo`, this needs `q + 2 ≤ n`: at the boundary `q+1 = n`
the LHS is nonzero while `padTwo` is `0`. -/
theorem padU_lo_eq_padTwo {n q : ℕ} (h : q + 2 ≤ n) (v : Square 1) :
    padU n q v = padTwo n q (kronPow (1 : Square 1) v) := by
  rw [padU, dif_pos (by omega), padTwo, dif_pos h]
  -- split the high identity 1_{n-(q+1)} = castSq (kronPow 1_m 1_1)
  have e2 : (1 : Square (n - (q + 1)))
      = castSq (show n - (q + 2) + 1 = n - (q + 1) by omega)
          (kronPow (1 : Square (n - (q + 2))) (1 : Square 1)) := by
    rw [kronPow_one, castSq_one]
  rw [e2, kronPow_castSq_left, kronPow_castSq_left, castSq_castSq,
    ← kronPow_assoc', kronPow_castSq_left, castSq_castSq]

theorem padU_padU_eq_padTwo {n q : ℕ} (u v : Square 1) :
    padU n (q + 1) u * padU n q v = padTwo n q (kronPow u v) := by
  by_cases h : q + 2 ≤ n
  · rw [padU_hi_eq_padTwo, padU_lo_eq_padTwo h, padTwo_mul, ← kronPow_mul, one_mul, mul_one]
  · rw [padU, dif_neg (show ¬ q + 1 + 1 ≤ n by omega), zero_mul, padTwo, dif_neg h]

/-! ### Bridge B — `padCZ` on the adjacent pair = `padTwo CZ4` -/

/-- The 4×4 CZ block: `diag(1,1,1,-1)`. -/
def CZ4 : Square 2 := Matrix.diagonal ![1, 1, 1, -1]

theorem padCZ_eq_padTwo {n q : ℕ} (h : q + 2 ≤ n) :
    padCZ n q (q + 1) = padTwo n q CZ4 := by
  have hq : q < n := by omega
  have hq1 : q + 1 < n := by omega
  have hne : q ≠ q + 1 := by omega
  rw [padTwo, dif_pos h, CZ4,
      ← Matrix.diagonal_one (n := Fin (2 ^ (n - (q + 2)))),
      ← Matrix.diagonal_one (n := Fin (2 ^ q)),
      kronPow_diagonal, kronPow_diagonal, castSq_diagonal,
      padCZ, if_pos ⟨hq, hq1, hne⟩]
  congr 1
  funext i
  rw [one_mul, mul_one]
  have hmat : ∀ d : Fin 4, (![1, 1, 1, -1] : Fin 4 → ℂ) d = if (d : ℕ) = 3 then -1 else 1 := by
    intro d; fin_cases d <;> simp
  rw [hmat]
  have hcond : ((i : ℕ).testBit q && (i : ℕ).testBit (q + 1)) = true
      ↔ (i : ℕ) / 2 ^ q % 2 ^ 2 = 3 := by
    simp only [Bool.and_eq_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    rw [pow_succ, ← Nat.div_div_eq_div_mul, show (2 : ℕ) ^ 2 = 4 from by norm_num]
    omega
  by_cases hb : ((i : ℕ).testBit q && (i : ℕ).testBit (q + 1)) = true
  · rw [if_pos hb, if_pos (hcond.mp hb)]
  · rw [if_neg hb, if_neg (fun hx => hb (hcond.mpr hx))]

/-! ## STRETCH — the SWAP denotation identity (matrix form, up to global phase)

`denote (swapAdj n q)` collapses to a single fixed 4×4 block `padTwo n q Mprod`
(independent of `n`, `q`), and `Mprod = i • swap4` (the macro-Hadamard carries the
phase `e^{-iπ/4}`. Six of them give `e^{-i3π/2} = i`). Hence the honest phase form
`denote_swapAdj_phase` with `θ = π/2`. -/

/-- The 2×2 macro-Hadamard `RZ(π/2)·SX·RZ(π/2)` (`= H` up to phase `e^{-iπ/4}`). -/
noncomputable def Hmac2 : Square 1 :=
  Gate1.matrix (.rz (1 / 2)) * (Gate1.matrix .sx * Gate1.matrix (.rz (1 / 2)))

theorem denote_hMac {n q : ℕ} : denote (hMac (n := n) q) = padU n q Hmac2 := by
  simp only [hMac, denote, Hmac2]
  rw [padU_mul, padU_mul]

/-- `denote (swapAdj n q)` as a single 4×4 block on the pair `(q, q+1)`. -/
theorem denote_swapAdj_eq {n q : ℕ} (h : q + 2 ≤ n) :
    denote (swapAdj n q)
      = padTwo n q
          ((kronPow Hmac2 (1 : Square 1) * (CZ4 * kronPow Hmac2 (1 : Square 1))) *
            ((kronPow (1 : Square 1) Hmac2 * (CZ4 * kronPow (1 : Square 1) Hmac2)) *
              (kronPow Hmac2 (1 : Square 1) * (CZ4 * kronPow Hmac2 (1 : Square 1))))) := by
  simp only [swapAdj, cnotMac, denote, denote_hMac]
  rw [padCZ_comm n (q + 1) q, padU_hi_eq_padTwo, padU_lo_eq_padTwo h,
    padCZ_eq_padTwo h]
  simp only [padTwo_mul]

/-! ### The 4×4 block computations (exp reasoning isolated to `hrz`/`Hmac2_eq`) -/

/-- `RZ(π/2)` as an explicit diagonal (all `exp(±iπ/4)` reasoning happens here). -/
theorem hrz : Gate1.matrix (.rz (1 / 2))
    = Matrix.diagonal ![(Real.sqrt 2 / 2 : ℂ) - (Real.sqrt 2 / 2) * Complex.I,
                        (Real.sqrt 2 / 2 : ℂ) + (Real.sqrt 2 / 2) * Complex.I] := by
  have key : ∀ s : ℝ, Complex.exp ((s : ℂ) * Complex.I)
      = (Real.cos s : ℂ) + (Real.sin s : ℂ) * Complex.I := by
    intro s; rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  unfold Gate1.matrix Gate.RZ
  refine congrArg Matrix.diagonal ?_
  funext k
  fin_cases k
  · rw [show (-(↑(↑(1 / 2 : ℚ) * Real.pi / 2)) * Complex.I : ℂ)
          = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring, key,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  · rw [show ((↑(↑(1 / 2 : ℚ) * Real.pi / 2)) * Complex.I : ℂ)
          = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring, key,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring

/-- The macro-Hadamard as an explicit 2×2 (no `exp`). -/
theorem Hmac2_eq : Hmac2 =
    !![(1 - Complex.I) / 2, (1 - Complex.I) / 2;
       (1 - Complex.I) / 2, (-1 + Complex.I) / 2] := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rw [Hmac2, hrz, Matrix.diagonal_vec2]
  simp only [Gate1.matrix, Gate.SX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, smul_eq_mul, Fin.isValue, Fin.mk_zero, Fin.mk_one] <;>
    ring_nf <;> simp only [hs, Complex.I_sq, hI3] <;> ring

theorem Hhi_eq : kronPow Hmac2 (1 : Square 1) =
    !![(1 - Complex.I) / 2, 0, (1 - Complex.I) / 2, 0;
       0, (1 - Complex.I) / 2, 0, (1 - Complex.I) / 2;
       (1 - Complex.I) / 2, 0, (-1 + Complex.I) / 2, 0;
       0, (1 - Complex.I) / 2, 0, (-1 + Complex.I) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronPow_apply, Hmac2_eq, Matrix.one_apply]

theorem Hlo_eq : kronPow (1 : Square 1) Hmac2 =
    !![(1 - Complex.I) / 2, (1 - Complex.I) / 2, 0, 0;
       (1 - Complex.I) / 2, (-1 + Complex.I) / 2, 0, 0;
       0, 0, (1 - Complex.I) / 2, (1 - Complex.I) / 2;
       0, 0, (1 - Complex.I) / 2, (-1 + Complex.I) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronPow_apply, Hmac2_eq, Matrix.one_apply]

theorem CZ4_eq : CZ4 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, (-1 : ℂ)] := by
  unfold CZ4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem swap4_eq :
    Layout.swap4 = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, (1 : ℂ)] := by
  unfold Layout.swap4 Matrix.swap
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Equiv.swap_apply_def]

set_option maxHeartbeats 2000000 in
theorem cnothi_eq :
    kronPow Hmac2 (1 : Square 1) * (CZ4 * kronPow Hmac2 (1 : Square 1))
      = !![-Complex.I, 0, 0, 0; 0, 0, 0, -Complex.I;
           0, 0, -Complex.I, 0; 0, -Complex.I, 0, 0] := by
  rw [Hhi_eq, CZ4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem cnotlo_eq :
    kronPow (1 : Square 1) Hmac2 * (CZ4 * kronPow (1 : Square 1) Hmac2)
      = !![-Complex.I, 0, 0, 0; 0, -Complex.I, 0, 0;
           0, 0, 0, -Complex.I; 0, 0, -Complex.I, 0] := by
  rw [Hlo_eq, CZ4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff] <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The fixed 4×4 SWAP-macro product equals `i • swap4`. -/
theorem swapProd_eq :
    (kronPow Hmac2 (1 : Square 1) * (CZ4 * kronPow Hmac2 (1 : Square 1))) *
      ((kronPow (1 : Square 1) Hmac2 * (CZ4 * kronPow (1 : Square 1) Hmac2)) *
        (kronPow Hmac2 (1 : Square 1) * (CZ4 * kronPow Hmac2 (1 : Square 1))))
      = Complex.I • Layout.swap4 := by
  rw [cnothi_eq, cnotlo_eq, swap4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff]

/-- STRETCH (honest phase form): `SWAP` on the adjacent pair denotes to the SWAP
permutation up to the global phase `e^{iπ/2} = i`. -/
theorem denote_swapAdj_phase {n q : ℕ} (h : q + 1 < n) :
    ∃ θ : ℝ, denote (swapAdj n q)
      = Complex.exp ((θ : ℝ) * Complex.I) • padTwo n q Layout.swap4 := by
  have h2 : q + 2 ≤ n := by omega
  refine ⟨Real.pi / 2, ?_⟩
  have hexp : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  rw [denote_swapAdj_eq h2, swapProd_eq, padTwo_smul, hexp]

/-! ## i06 — the qubit→bit tensor lift (block bridge + headline) -/

/-- Block bridge: the 2-qubit SWAP placed on the adjacent pair `(q, q+1)` equals
the permutation matrix of the index-level bit swap. Both sides collapse to
`permMatrix` of the same derived permutation via `kronPow_permMatrix` /
`castSq_permMatrix`. -/
theorem padTwo_swap4_eq_permDenote {n q : ℕ} (h : q + 2 ≤ n) :
    padTwo n q Layout.swap4 = Layout.permDenote (Layout.bitSwap n q) := by
  unfold Layout.permDenote Layout.bitSwap
  rw [dif_pos h]
  simp only [padTwo, dif_pos h]
  rw [show Layout.swap4
        = (Equiv.swap (1 : Fin (2 ^ 2)) (2 : Fin (2 ^ 2))).permMatrix ℂ from rfl,
      ← Matrix.permMatrix_one (n := Fin (2 ^ (n - (q + 2)))) (R := ℂ),
      ← Matrix.permMatrix_one (n := Fin (2 ^ q)) (R := ℂ),
      kronPow_permMatrix, kronPow_permMatrix, castSq_permMatrix]

/-- Headline semantic bridge: `swapAdj n q` denotes to the permutation matrix of
the bit swap `bitSwap n q`, up to a global phase `e^{iθ}` (`θ = π/2`). -/
theorem denote_swapAdj_bitSwap {n q : ℕ} (h : q + 1 < n) :
    ∃ θ : ℝ, denote (swapAdj n q)
      = Complex.exp ((θ : ℝ) * Complex.I) • Layout.permDenote (Layout.bitSwap n q) := by
  obtain ⟨θ, hθ⟩ := denote_swapAdj_phase h
  exact ⟨θ, by rw [hθ, padTwo_swap4_eq_permDenote (by omega)]⟩

/-! ### Decidability smoke test -/

example : HWF (lnnPath 4) (swapAdj 4 1) := swapAdj_HWF (by decide)

/-! ### i10 — `swapEdge` / `bitSwap'` decidable smokes -/

/-- General SWAP is well-formed on a non-index-adjacent pair `(0, 2)`. -/
example : WF (swapEdge 4 0 2) := swapEdge_WF (by decide) (by decide) (by decide)

/-- A small three-node coupling with the genuinely non-adjacent edge `0 — 2`. -/
def gEdge02 : Coupling 3 where
  edge a b := decide ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0))
  edge_symm := by intro a b; rw [decide_eq_decide]; tauto
  edge_irrefl := by
    intro a; simp only [decide_eq_false_iff_not]; rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega
  edge_bounds := by
    intro a b h; simp only [decide_eq_true_eq] at h
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- HWF of `swapEdge` on a real non-adjacent edge. -/
example : HWF gEdge02 (swapEdge 3 0 2) := swapEdge_HWF (by decide)

example : (Layout.bitSwap' 4 0 2) 1 = 4 := by decide   -- bit 0 ↦ bit 2
example : (Layout.bitSwap' 4 0 2) 4 = 1 := by decide   -- bit 2 ↦ bit 0
example : (Layout.bitSwap' 4 0 2) 5 = 5 := by decide   -- bits 0,2 both set: fixed
example : (Layout.bitSwap' 4 0 2) 2 = 2 := by decide   -- bit 1 untouched
example : Layout.bitSwap' 4 0 2 * Layout.bitSwap' 4 0 2 = 1 := Layout.bitSwap'_mul_self

/-! ## i11 — the non-adjacent semantic bridge (Route B, CNOT-as-permutation)

`denote (cnotMac u v) = padU v Hmac2 · padCZ u v · padU v Hmac2` collapses to a
`phase • permMatrix` via the PROJECTOR-SPLIT. Split `padCZ` as `Pu0 + Pu1·padU v Z`.
Commute `Pu0/Pu1` past the sandwich (`padU_comm_diag`). Collapse each term with the
two 2×2 facts `Hmac2_sq` and `Hmac2_Z_Hmac2`. Recognize `Pu0 + Pu1·padU v X` as the
CNOT permutation matrix. Then `swapEdge = 3·cnotMac` chains the phase `(-i)³ = i`. -/

/-- The 2×2 Pauli-`Z` as a diagonal (matches the `Hmac2` computational style). -/
noncomputable def Zmat : Square 1 := Matrix.diagonal ![1, -1]

theorem Zmat_eq : Zmat = !![1, 0; 0, (-1 : ℂ)] := by
  rw [Zmat, Matrix.diagonal_vec2]

set_option maxHeartbeats 2000000 in
/-- `Hmac2² = -i·1` (the macro-Hadamard squares to `-i` times identity). -/
theorem Hmac2_sq : Hmac2 * Hmac2 = (-Complex.I) • (1 : Square 1) := by
  rw [Hmac2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.ext_iff] <;> norm_num

set_option maxHeartbeats 2000000 in
/-- `Hmac2·Z·Hmac2 = -i·X` (conjugating `Z` by the macro-Hadamard gives `-i·X`). -/
theorem Hmac2_Z_Hmac2 : Hmac2 * Zmat * Hmac2 = (-Complex.I) • Gate.X := by
  rw [Hmac2_eq, Zmat_eq, Gate.X]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-- Scalar pulls through `padU` (analog of `padTwo_smul`). -/
theorem padU_smul {n q : ℕ} (c : ℂ) (M : Square 1) :
    padU n q (c • M) = c • padU n q M := by
  by_cases h : q + 1 ≤ n
  · simp only [padU, dif_pos h]
    rw [kronPow_smul_right, kronPow_smul_left, castSq_smul]
  · simp [padU, h]

/-! ### Crux-support lemmas (consume `padU_apply` + `Layout.testBit_div_two_pow`). -/

/-- If `i,j` agree off bit `v` (equal div by `2^(v+1)`, equal mod `2^v`), they agree
on every bit `u ≠ v`. -/
theorem testBit_eq_of_off {v : ℕ} {i j : ℕ}
    (hd : i / 2 ^ (v + 1) = j / 2 ^ (v + 1)) (hm : i % 2 ^ v = j % 2 ^ v)
    {u : ℕ} (huv : u ≠ v) : i.testBit u = j.testBit u := by
  rcases lt_trichotomy u v with hlt | heq | hgt
  · have hi : (i % 2 ^ v).testBit u = i.testBit u := by
      rw [Nat.testBit_mod_two_pow]; simp [hlt]
    have hj : (j % 2 ^ v).testBit u = j.testBit u := by
      rw [Nat.testBit_mod_two_pow]; simp [hlt]
    rw [← hi, ← hj, hm]
  · exact absurd heq huv
  · have hi : i.testBit u = (i / 2 ^ (v + 1)).testBit (u - (v + 1)) := by
      rw [Layout.testBit_div_two_pow]; congr 1; omega
    have hj : j.testBit u = (j / 2 ^ (v + 1)).testBit (u - (v + 1)) := by
      rw [Layout.testBit_div_two_pow]; congr 1; omega
    rw [hi, hj, hd]

/-- `p ^^^ 2^v = q` iff `p,q` agree off bit `v` but differ at bit `v`. -/
theorem xor_two_pow_eq_iff (v p q : ℕ) :
    p ^^^ 2 ^ v = q
      ↔ (p / 2 ^ (v + 1) = q / 2 ^ (v + 1) ∧ p % 2 ^ v = q % 2 ^ v
           ∧ p / 2 ^ v % 2 ≠ q / 2 ^ v % 2) := by
  constructor
  · intro h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · refine Nat.eq_of_testBit_eq (fun t => ?_)
      rw [Layout.testBit_div_two_pow, Layout.testBit_div_two_pow, Nat.testBit_xor,
        Nat.testBit_two_pow, decide_eq_false (by omega : ¬ v = v + 1 + t)]
      simp
    · refine Nat.eq_of_testBit_eq (fun t => ?_)
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_xor,
        Nat.testBit_two_pow]
      by_cases ht : t < v
      · rw [decide_eq_true ht, decide_eq_false (by omega : ¬ v = t)]; simp
      · rw [decide_eq_false ht]; simp
    · have hxorv : (p ^^^ 2 ^ v).testBit v = !(p.testBit v) := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_true rfl]
        cases p.testBit v <;> simp
      have hpv : p.testBit v = decide (p / 2 ^ v % 2 = 1) :=
        Nat.testBit_eq_decide_div_mod_eq
      have hqv : (p ^^^ 2 ^ v).testBit v = decide ((p ^^^ 2 ^ v) / 2 ^ v % 2 = 1) :=
        Nat.testBit_eq_decide_div_mod_eq
      intro hcontra
      have : p.testBit v = (p ^^^ 2 ^ v).testBit v := by rw [hpv, hqv, hcontra]
      rw [hxorv] at this
      cases p.testBit v <;> simp_all
  · rintro ⟨hd, hm, hn⟩
    refine Nat.eq_of_testBit_eq (fun t => ?_)
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases ht : t = v
    · subst ht
      rw [decide_eq_true rfl]
      have hpv : p.testBit t = decide (p / 2 ^ t % 2 = 1) :=
        Nat.testBit_eq_decide_div_mod_eq
      have hqv : q.testBit t = decide (q / 2 ^ t % 2 = 1) :=
        Nat.testBit_eq_decide_div_mod_eq
      have h1 : p / 2 ^ t % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : q / 2 ^ t % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rw [hpv, hqv]
      have : (p / 2 ^ t % 2 = 0 ∧ q / 2 ^ t % 2 = 1)
          ∨ (p / 2 ^ t % 2 = 1 ∧ q / 2 ^ t % 2 = 0) := by omega
      rcases this with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> simp
    · rw [decide_eq_false (by omega : ¬ v = t)]
      simp only [Bool.xor_false]
      exact testBit_eq_of_off hd hm ht

/-- A diagonal depending only on bit `u` commutes with `padU n v M` when `u ≠ v`
(nonzero `padU` entries agree off bit `v`, so bit `u` matches). -/
theorem padU_comm_diag {n v u : ℕ} (M : Square 1) (g : Bool → ℂ) (huv : u ≠ v) :
    padU n v M * Matrix.diagonal (fun i : Fin (2 ^ n) => g ((i : ℕ).testBit u))
      = Matrix.diagonal (fun i : Fin (2 ^ n) => g ((i : ℕ).testBit u)) * padU n v M := by
  by_cases hv : v + 1 ≤ n
  · ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases eq_or_ne (padU n v M i j) 0 with hz | hnz
    · rw [hz]; simp
    · have hnz' := hnz
      rw [padU_apply hv] at hnz'
      have hcond : (i : ℕ) / 2 ^ (v + 1) = (j : ℕ) / 2 ^ (v + 1)
          ∧ (i : ℕ) % 2 ^ v = (j : ℕ) % 2 ^ v := by
        by_contra hc; rw [if_neg hc] at hnz'; exact hnz' rfl
      have hbit : (i : ℕ).testBit u = (j : ℕ).testBit u :=
        testBit_eq_of_off hcond.1 hcond.2 huv
      rw [hbit]; ring
  · rw [padU, dif_neg hv, zero_mul, mul_zero]

/-- Projector split of `padCZ`: `padCZ u v = Pu0 + Pu1 · padU v Z`, where `Pu0/Pu1`
are the diagonal projectors onto `testBit u = 0/1`. -/
theorem padCZ_split {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    padCZ n u v
      = Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then 0 else 1)
      + Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then 1 else 0)
        * padU n v Zmat := by
  rw [Zmat, padU_diagonal (show v + 1 ≤ n by omega) ![1, -1],
      Matrix.diagonal_mul_diagonal, padCZ, if_pos ⟨hu, hv, huv⟩]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
    cases hbu : (i : ℕ).testBit u <;> cases hbv : (i : ℕ).testBit v <;> simp
  · simp [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij]

/-- Entrywise value of `padU n v X`: the CNOT-target `X` at bit `v` flips it, so the
entry is `1` exactly when `i ^^^ 2^v = j`. -/
theorem padU_X_apply {n v : ℕ} (hv : v < n) (i j : Fin (2 ^ n)) :
    padU n v Gate.X i j = (if (i : ℕ) ^^^ 2 ^ v = (j : ℕ) then 1 else 0) := by
  rw [padU_apply (by omega)]
  have hXgen : ∀ (a b : ℕ) (ha : a < 2) (hb : b < 2),
      Gate.X ⟨a, ha⟩ ⟨b, hb⟩ = if a = b then 0 else 1 := by
    intro a b ha hb
    interval_cases a <;> interval_cases b <;> simp [Gate.X]
  rw [hXgen]
  by_cases hP : (i : ℕ) ^^^ 2 ^ v = (j : ℕ)
  · rw [if_pos hP]
    obtain ⟨hd, hm, hn⟩ := (xor_two_pow_eq_iff v (i : ℕ) (j : ℕ)).mp hP
    rw [if_pos ⟨hd, hm⟩, if_neg hn]
  · rw [if_neg hP]
    by_cases hC : (i : ℕ) / 2 ^ (v + 1) = (j : ℕ) / 2 ^ (v + 1)
        ∧ (i : ℕ) % 2 ^ v = (j : ℕ) % 2 ^ v
    · rw [if_pos hC]
      by_cases hE : (i : ℕ) / 2 ^ v % 2 = (j : ℕ) / 2 ^ v % 2
      · rw [if_pos hE]
      · exact absurd ((xor_two_pow_eq_iff v (i : ℕ) (j : ℕ)).mpr ⟨hC.1, hC.2, hE⟩) hP
    · rw [if_neg hC]

/-- The projector-permutation identity: `Pu0 + Pu1 · padU v X = permMatrix (cnotPerm)`. -/
theorem cnotMac_perm_final {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
      Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then 0 else 1)
    + Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then 1 else 0)
      * padU n v Gate.X
    = Layout.permDenote (Layout.cnotPerm n u v) := by
  ext i j
  have hji : (j = Layout.cnotPerm n u v i) ↔ ((j : ℕ) = Layout.natCnot u v (i : ℕ)) := by
    rw [Fin.ext_iff, Layout.cnotPerm_val hu hv huv]
  rw [Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_mul, padU_X_apply hv]
  simp only [Layout.permDenote, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply,
    Pi.single_apply, hji, Layout.natCnot]
  by_cases hbu : (i : ℕ).testBit u = true
  · simp only [hbu, if_true]
    rw [ite_self, zero_add, one_mul]
    by_cases hxy : (i : ℕ) ^^^ 2 ^ v = (j : ℕ)
    · rw [if_pos hxy, if_pos hxy.symm]
    · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]
  · rw [Bool.not_eq_true] at hbu
    simp only [hbu, Bool.false_eq_true, if_false]
    rw [zero_mul, add_zero]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij (Fin.ext h.symm))]

set_option maxHeartbeats 2000000 in
/-- **THE CRUX.** `denote (cnotMac u v)` collapses to `-i` times the CNOT permutation
matrix (projector-split: commute `Pu0/Pu1` past the Hadamard sandwich, then the two
2×2 phase facts collapse each term). -/
theorem denote_cnotMac_perm {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    denote (cnotMac (n := n) u v)
      = (-Complex.I) • Layout.permDenote (Layout.cnotPerm n u v) := by
  have hvn : v + 1 ≤ n := by omega
  have hc0 : padU n v Hmac2
        * Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (0 : ℂ) else 1)
      = Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (0 : ℂ) else 1)
        * padU n v Hmac2 :=
    padU_comm_diag Hmac2 (fun b => if b then 0 else 1) huv
  have hc1 : padU n v Hmac2
        * Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (1 : ℂ) else 0)
      = Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (1 : ℂ) else 0)
        * padU n v Hmac2 :=
    padU_comm_diag Hmac2 (fun b => if b then 1 else 0) huv
  have hA : padU n v Hmac2
        * (Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (0 : ℂ) else 1)
           * padU n v Hmac2)
      = (-Complex.I)
        • Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (0 : ℂ) else 1) := by
    rw [← mul_assoc, hc0, mul_assoc, padU_mul, Hmac2_sq, padU_smul, padU_one hvn,
        mul_smul_comm, mul_one]
  have hB : padU n v Hmac2
        * (Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (1 : ℂ) else 0)
           * padU n v Zmat * padU n v Hmac2)
      = (-Complex.I)
        • (Matrix.diagonal (fun i : Fin (2 ^ n) => if (i : ℕ).testBit u then (1 : ℂ) else 0)
           * padU n v Gate.X) := by
    rw [mul_assoc, padU_mul, ← mul_assoc, hc1, mul_assoc, padU_mul,
        ← mul_assoc Hmac2 Zmat Hmac2, Hmac2_Z_Hmac2, padU_smul, mul_smul_comm]
  unfold cnotMac
  simp only [denote, denote_hMac]
  rw [padCZ_split hu hv huv, Matrix.add_mul, Matrix.mul_add, hA, hB, ← smul_add,
      cnotMac_perm_final hu hv huv]

/-- `CNOT(u→v) · CNOT(v→u) · CNOT(u→v) = SWAP(u,v)` at the permutation level. -/
theorem Layout.cnotPerm_cubed {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    Layout.cnotPerm n u v * Layout.cnotPerm n v u * Layout.cnotPerm n u v
      = Layout.bitSwap' n u v := by
  have hkey : ∀ m : ℕ,
      Layout.natCnot u v (Layout.natCnot v u (Layout.natCnot u v m))
        = Layout.natBitSwap u v m := by
    intro m
    refine Nat.eq_of_testBit_eq (fun k => ?_)
    rw [Layout.natBitSwap_testBit]
    simp only [Layout.natCnot_testBit]
    by_cases hku : k = u
    · rw [hku, Equiv.swap_apply_left]
      cases m.testBit u <;> cases m.testBit v <;> simp_all
    · by_cases hkv : k = v
      · rw [hkv, Equiv.swap_apply_right]
        cases m.testBit u <;> cases m.testBit v <;> simp_all
      · rw [Equiv.swap_apply_of_ne_of_ne hku hkv]
        simp_all
  have hbs : ∀ i : Fin (2 ^ n), ((Layout.bitSwap' n u v i) : ℕ) = Layout.natBitSwap u v (i : ℕ) := by
    intro i
    rw [Layout.bitSwap', dif_pos ⟨hu, hv⟩]
    simp only [Function.Involutive.coe_toPerm]
  ext i
  simp only [Equiv.Perm.mul_apply, Layout.cnotPerm_val hu hv huv,
    Layout.cnotPerm_val hv hu (Ne.symm huv), hbs, hkey]

/-- **THE BRIDGE (STRETCH capstone).** General-graph SWAP denotes to the bit-swap
permutation matrix up to global phase `e^{iπ/2} = i`. Completes general SWAP
correctness. -/
theorem denote_swapEdge_bitSwap {n u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    ∃ θ : ℝ, denote (swapEdge n u v)
      = Complex.exp (θ * Complex.I) • Layout.permDenote (Layout.bitSwap' n u v) := by
  refine ⟨Real.pi / 2, ?_⟩
  have hexp : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hmat : Layout.permDenote (Layout.cnotPerm n u v)
        * (Layout.permDenote (Layout.cnotPerm n v u)
           * Layout.permDenote (Layout.cnotPerm n u v))
      = Layout.permDenote (Layout.bitSwap' n u v) := by
    rw [← Layout.permDenote_mul, ← Layout.permDenote_mul, Layout.cnotPerm_cubed hu hv huv]
  unfold swapEdge
  simp only [denote]
  rw [denote_cnotMac_perm hu hv huv, denote_cnotMac_perm hv hu (Ne.symm huv), hexp]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hmat]
  congr 1
  rw [neg_mul_neg, Complex.I_mul_I]; ring

end QpuCompiler
