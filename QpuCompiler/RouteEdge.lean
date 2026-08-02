/-
QpuCompiler/RouteEdge.lean — general edge-path routing (iteration 12).

A direct, lighter port of the i07 `lnnPath` routing (`Route.lean`) to an
arbitrary `Coupling` graph. Every proof is a shape-preserving port of an accepted
i07 lemma with the atom substituted:
  swapAdj → swapEdge, bitSwap → bitSwap', denote_swapAdj_bitSwap →
  denote_swapEdge_bitSwap, swapAdj_HWF → swapEdge_HWF. The concrete example's
  fin_cases matrix identity becomes ONE `conj_bitSwap'_padCZ` application.

Paths are `List.IsChain` edge-chains (Batteries — `List.Chain'` was renamed).
General `routeEdge_congPhase` is DEFERRED to i13.
-/
import QpuCompiler.Route

namespace QpuCompiler

open Matrix

/-! ## Path abstraction -/

/-- A vertex list is an edge-path when consecutive vertices are coupled. -/
def IsEdgePath {n} (g : Coupling n) (p : List ℕ) : Prop :=
  List.IsChain (fun u v => g.edge u v = true) p

/-- The consecutive-pair edges of a vertex list. -/
def pathEdges : List ℕ → List (ℕ × ℕ)
  | u :: v :: rest => (u, v) :: pathEdges (v :: rest)
  | _              => []

/-- Every edge produced by `pathEdges` on an edge-path is a coupling edge. -/
theorem pathEdges_mem_edge {n} {g : Coupling n} :
    ∀ {p}, IsEdgePath g p → ∀ e ∈ pathEdges p, g.edge e.1 e.2 = true := by
  intro p
  induction p with
  | nil => intro _ e he; simp only [pathEdges, List.not_mem_nil] at he
  | cons u rest ihu =>
    cases rest with
    | nil => intro _ e he; simp only [pathEdges, List.not_mem_nil] at he
    | cons v rest =>
      intro hp e he
      rw [IsEdgePath, List.isChain_cons_cons] at hp
      obtain ⟨huv, htail⟩ := hp
      simp only [pathEdges, List.mem_cons] at he
      rcases he with rfl | he
      · exact huv
      · exact ihu htail e he

/-! ## The fold — circuit side and index side -/

/-- A swap network: a right-nested `.seq` of general edge swaps, one per pair. -/
def swapEdgeNet (n : ℕ) : List (ℕ × ℕ) → UCom n
  | []          => .app1 .id 0
  | (u,v) :: es => .seq (swapEdge n u v) (swapEdgeNet n es)

/-- Index-side mirror: the product of the bit-swap permutations. -/
def bitSwapProd' (n : ℕ) : List (ℕ × ℕ) → Equiv.Perm (Fin (2 ^ n))
  | []          => 1
  | (u,v) :: es => Layout.bitSwap' n u v * bitSwapProd' n es

/-- The fold lemma: `swapEdgeNet` denotes to the permutation matrix of the
mirrored bit-swap product, up to a global phase. -/
theorem denote_swapEdgeNet {n} (hn : 0 < n) (es : List (ℕ × ℕ))
    (hes : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) :
    ∃ θ : ℝ, denote (swapEdgeNet n es)
      = Complex.exp (θ * Complex.I) • Layout.permDenote (bitSwapProd' n es) := by
  induction es with
  | nil =>
    refine ⟨0, ?_⟩
    simp only [swapEdgeNet, denote, Gate1.matrix, bitSwapProd', Layout.permDenote_one,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    exact padU_one (by omega)
  | cons e es ih =>
    obtain ⟨hu, hv, huv⟩ := hes e List.mem_cons_self
    obtain ⟨u, v⟩ := e
    obtain ⟨θe, he⟩ := denote_swapEdge_bitSwap hu hv huv
    obtain ⟨θes, hes'⟩ := ih (fun e' h' => hes e' (List.mem_cons_of_mem _ h'))
    refine ⟨θe + θes, ?_⟩
    show denote (swapEdgeNet n es) * denote (swapEdge n u v)
        = Complex.exp (↑(θe + θes) * Complex.I) • Layout.permDenote (bitSwapProd' n ((u, v) :: es))
    rw [he, hes', smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
      show ((θes : ℝ) : ℂ) * Complex.I + ((θe : ℝ) : ℂ) * Complex.I
          = ((θe + θes : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      ← Layout.permDenote_mul, bitSwapProd']

/-! ## `swapEdgeNet` hardware well-formedness -/

/-- A coupling edge gives in-bounds distinct endpoints. -/
theorem edge_bounds_ne {n} {g : Coupling n} {u v} (h : g.edge u v = true) :
    u < n ∧ v < n ∧ u ≠ v := by
  obtain ⟨hu, hv⟩ := g.edge_bounds u v h
  refine ⟨hu, hv, ?_⟩
  intro rfl
  rw [g.edge_irrefl] at h
  exact absurd h (by simp)

theorem swapEdgeNet_HWF {n} {g : Coupling n} (hn : 0 < n) (es : List (ℕ × ℕ))
    (hes : ∀ e ∈ es, g.edge e.1 e.2 = true) : HWF g (swapEdgeNet n es) := by
  induction es with
  | nil => exact .app1 hn
  | cons e es ih =>
    obtain ⟨u, v⟩ := e
    exact .seq (swapEdge_HWF (hes (u, v) List.mem_cons_self))
      (ih (fun e' h' => hes e' (List.mem_cons_of_mem _ h')))

/-! ## Cheap i13 down-payments -/

theorem bitSwapProd'_append {n} (es fs : List (ℕ × ℕ)) :
    bitSwapProd' n (es ++ fs) = bitSwapProd' n es * bitSwapProd' n fs := by
  induction es with
  | nil => simp [bitSwapProd']
  | cons e es ih =>
    obtain ⟨u, v⟩ := e
    simp only [List.cons_append, bitSwapProd', ih, mul_assoc]

theorem bitSwapProd'_reverse {n} (es : List (ℕ × ℕ)) :
    bitSwapProd' n es.reverse = (bitSwapProd' n es)⁻¹ := by
  induction es with
  | nil => simp [bitSwapProd']
  | cons e es ih =>
    obtain ⟨u, v⟩ := e
    rw [List.reverse_cons, bitSwapProd'_append, ih]
    show (bitSwapProd' n es)⁻¹ * bitSwapProd' n [(u, v)]
        = (Layout.bitSwap' n u v * bitSwapProd' n es)⁻¹
    rw [_root_.mul_inv_rev]
    simp only [bitSwapProd', mul_one]
    congr 1
    exact (inv_eq_of_mul_eq_one_right Layout.bitSwap'_mul_self).symm

/-! ## General single-CZ routing -/

/-- Route a single `cz v0 v1` along an edge-path `v0 :: v1 :: rest`: swap the far
endpoint down to the near edge along all edges except the near one, apply the
native `cz v0 v1`, then swap back. -/
def routeEdge (n : ℕ) : List ℕ → UCom n
  | v0 :: v1 :: rest =>
      let E := pathEdges (v1 :: rest)
      .seq (.seq (swapEdgeNet n E.reverse) (.cz v0 v1)) (swapEdgeNet n E)
  | _ => .app1 .id 0

theorem routeEdge_HWF {n} {g : Coupling n} (hn : 0 < n)
    {v0 v1 : ℕ} {rest : List ℕ} (hp : IsEdgePath g (v0 :: v1 :: rest)) :
    HWF g (routeEdge n (v0 :: v1 :: rest)) := by
  rw [IsEdgePath, List.isChain_cons_cons] at hp
  obtain ⟨hedge, htail⟩ := hp
  have hE : ∀ e ∈ pathEdges (v1 :: rest), g.edge e.1 e.2 = true :=
    pathEdges_mem_edge htail
  have hErev : ∀ e ∈ (pathEdges (v1 :: rest)).reverse, g.edge e.1 e.2 = true :=
    fun e h => hE e (List.mem_reverse.mp h)
  exact .seq (.seq (swapEdgeNet_HWF hn _ hErev) (HWF.cz hedge))
    (swapEdgeNet_HWF hn _ hE)

/-! ## Concrete soundness witness — the headline -/

/-- A small coupling with the genuinely non-adjacent path `0 — 1 — 3`. -/
def gPath : Coupling 4 where
  edge a b := decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1))
  edge_symm := by intro a b; rw [decide_eq_decide]; tauto
  edge_irrefl := by
    intro a; simp only [decide_eq_false_iff_not]
    rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> omega
  edge_bounds := by
    intro a b h; simp only [decide_eq_true_eq] at h
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega

set_option maxHeartbeats 2000000 in
/-- **Headline.** Routing a single `cz 0 3` along the edge-path `0 — 1 — 3`
is correct up to a global phase — the first general-graph routing soundness
witness (routing a `cz` along a non-adjacent path). -/
theorem routeEdge_congPhase_example :
    UCom.CongPhase (routeEdge 4 [0, 1, 3]) (.cz 0 3) := by
  obtain ⟨θ, hθ⟩ := denote_swapEdgeNet (n := 4) (by omega) [(1, 3)]
    (by intro e he; simp only [List.mem_singleton] at he; subst he
        exact ⟨by omega, by omega, by omega⟩)
  refine UCom.CongPhase.of_phase (θ + θ) ?_
  simp only [routeEdge, pathEdges, List.reverse_cons, List.reverse_nil,
    List.nil_append, denote]
  rw [hθ, show bitSwapProd' 4 [(1, 3)] = Layout.bitSwap' 4 1 3 from by simp [bitSwapProd']]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
      show ((θ : ℝ) : ℂ) * Complex.I + ((θ : ℝ) : ℂ) * Complex.I
          = ((θ + θ : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  congr 1
  rw [← mul_assoc, conj_bitSwap'_padCZ (by omega) (by omega) (by omega) (by omega) (by omega)]
  congr 1

/-! ### Decidability smoke tests -/

example : IsEdgePath gPath [0, 1, 3] := by unfold IsEdgePath; decide

example : HWF gPath (routeEdge 4 [0, 1, 3]) :=
  routeEdge_HWF (by omega) (by unfold IsEdgePath; decide)

/-! ## i13 — general `routeEdge_congPhase` -/

/-- Both endpoints of any edge produced by `pathEdges P` lie in `P`. -/
theorem pathEdges_endpoints_mem :
    ∀ {P : List ℕ} {e : ℕ × ℕ}, e ∈ pathEdges P → e.1 ∈ P ∧ e.2 ∈ P := by
  intro P
  induction P with
  | nil => intro e he; simp only [pathEdges, List.not_mem_nil] at he
  | cons u rest ihu =>
    cases rest with
    | nil => intro e he; simp only [pathEdges, List.not_mem_nil] at he
    | cons v rest =>
      intro e he
      simp only [pathEdges, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · obtain ⟨h1, h2⟩ := ihu he
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- Walking the near operand `v1` along the swap fold of `pathEdges (v1 :: rest)`
carries it to the far endpoint `getLast`. Uses only unconditional `swap_apply_left`. -/
theorem foldl_swap_pathEdges (v1 : ℕ) (rest : List ℕ) :
    (pathEdges (v1 :: rest)).foldl (fun x e => Equiv.swap e.1 e.2 x) v1
      = (v1 :: rest).getLast (by simp) := by
  induction rest generalizing v1 with
  | nil => simp [pathEdges]
  | cons v2 rest' ih =>
    rw [pathEdges, List.foldl_cons, Equiv.swap_apply_left, ih, List.getLast_cons_cons]

set_option maxHeartbeats 2000000 in
/-- The conjugation induction (crux): conjugating `padCZ n a c` by the product of
the bit-swaps in `es` (with `a` disjoint from every edge, so the `a`-index is
fixed) transports `c` by the fold of `swap e.1 e.2` along `es`. The back leg is
the reversed product. -/
theorem bitSwapProd'_conj_padCZ {n a : ℕ} (es : List (ℕ × ℕ))
    (hb : ∀ e ∈ es, e.1 < n ∧ e.2 < n) (ha : a < n)
    (hafix : ∀ e ∈ es, a ≠ e.1 ∧ a ≠ e.2) :
    ∀ c, c < n → a ≠ c →
      Layout.permDenote (bitSwapProd' n es) * padCZ n a c
          * Layout.permDenote (bitSwapProd' n es.reverse)
        = padCZ n a (es.foldl (fun x e => Equiv.swap e.1 e.2 x) c) := by
  induction es with
  | nil =>
    intro c _ _
    simp [bitSwapProd', Layout.permDenote_one]
  | cons e es ih =>
    obtain ⟨u, v⟩ := e
    intro c hc hac
    obtain ⟨hu, hv⟩ := hb (u, v) List.mem_cons_self
    obtain ⟨hau, hav⟩ := hafix (u, v) List.mem_cons_self
    have hb' : ∀ e ∈ es, e.1 < n ∧ e.2 < n := fun e he => hb e (List.mem_cons_of_mem _ he)
    have hafix' : ∀ e ∈ es, a ≠ e.1 ∧ a ≠ e.2 := fun e he => hafix e (List.mem_cons_of_mem _ he)
    have hc' : Equiv.swap u v c < n := by rw [Equiv.swap_apply_def]; split_ifs <;> assumption
    have hac' : a ≠ Equiv.swap u v c := by
      rw [Equiv.swap_apply_def]; split_ifs <;> [exact hav; exact hau; exact hac]
    rw [bitSwapProd', List.reverse_cons, bitSwapProd'_append]
    simp only [bitSwapProd', mul_one, Layout.permDenote_mul]
    set A := Layout.permDenote (bitSwapProd' n es) with hA
    set Ar := Layout.permDenote (bitSwapProd' n es.reverse) with hAr
    set B := Layout.permDenote (Layout.bitSwap' n u v) with hB
    rw [mul_assoc A B (padCZ n a c), ← mul_assoc (A * (B * padCZ n a c)) B Ar,
        mul_assoc A (B * padCZ n a c) B, conj_bitSwap'_padCZ hu hv ha hc hac,
        Equiv.swap_apply_of_ne_of_ne hau hav,
        ih hb' hafix' (Equiv.swap u v c) hc' hac', List.foldl_cons]

set_option maxHeartbeats 2000000 in
/-- **Headline (TARGET).** Routing a single `cz v0 (far endpoint)` along ANY simple
edge-path `v0 :: v1 :: rest` (with `v0 ∉ v1 :: rest`) is correct up to a global
phase. This completes general-graph routing soundness. -/
theorem routeEdge_congPhase {n} {g : Coupling n} (hn : 0 < n)
    {v0 v1 : ℕ} {rest : List ℕ}
    (hp : IsEdgePath g (v0 :: v1 :: rest))
    (hsimple : v0 ∉ (v1 :: rest)) :
    UCom.CongPhase (routeEdge n (v0 :: v1 :: rest))
      (.cz v0 ((v1 :: rest).getLast (by simp))) := by
  rw [IsEdgePath, List.isChain_cons_cons] at hp
  obtain ⟨hedge, htail⟩ := hp
  obtain ⟨hv0n, hv1n, hv01⟩ := edge_bounds_ne hedge
  have hEmem : ∀ e ∈ pathEdges (v1 :: rest), g.edge e.1 e.2 = true := pathEdges_mem_edge htail
  have hEb : ∀ e ∈ pathEdges (v1 :: rest), e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2 :=
    fun e he => edge_bounds_ne (hEmem e he)
  have hafix : ∀ e ∈ pathEdges (v1 :: rest), v0 ≠ e.1 ∧ v0 ≠ e.2 := by
    intro e he
    obtain ⟨h1, h2⟩ := pathEdges_endpoints_mem he
    exact ⟨fun h => hsimple (h ▸ h1), fun h => hsimple (h ▸ h2)⟩
  obtain ⟨θ1, h1⟩ := denote_swapEdgeNet hn (pathEdges (v1 :: rest)) hEb
  obtain ⟨θ2, h2⟩ := denote_swapEdgeNet hn (pathEdges (v1 :: rest)).reverse
                       (fun e he => hEb e (List.mem_reverse.mp he))
  refine UCom.CongPhase.of_phase (θ1 + θ2) ?_
  simp only [routeEdge, denote]
  rw [h1, h2, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
      show ((θ1:ℝ):ℂ)*Complex.I + ((θ2:ℝ):ℂ)*Complex.I
          = ((θ1+θ2:ℝ):ℂ)*Complex.I from by push_cast; ring]
  congr 1
  rw [← mul_assoc,
      bitSwapProd'_conj_padCZ (pathEdges (v1 :: rest))
        (fun e he => ⟨(hEb e he).1, (hEb e he).2.1⟩) hv0n hafix v1 hv1n hv01,
      foldl_swap_pathEdges]

end QpuCompiler
