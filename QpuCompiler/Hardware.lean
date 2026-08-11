/-
QpuCompiler/Hardware.lean — coupling-graph hardware model (heavy-hex abstraction),
decidable hardware-well-formedness (HWF, strengthens WF), and a proof that the
optimizer preserves hardware validity. padCZ symmetry (padCZ_comm) justifies the
undirected edges. CZ is the only two-qubit gate, and it is symmetric. This
file has no routing or SWAP (i05).
-/
import QpuCompiler.Optimize

namespace QpuCompiler

/-- A coupling graph on `n` qubits: a symmetric, irreflexive, in-bounds
Boolean adjacency relation. -/
structure Coupling (n : ℕ) where
  edge        : ℕ → ℕ → Bool
  edge_symm   : ∀ a b, edge a b = edge b a
  edge_irrefl : ∀ a, edge a a = false
  edge_bounds : ∀ a b, edge a b = true → a < n ∧ b < n

/-- Linear nearest-neighbor path coupling: `a — a+1` for all `a < n`. -/
def lnnPath (n : ℕ) : Coupling n where
  edge a b := (decide (a + 1 = b) || decide (b + 1 = a))
              && decide (a < n) && decide (b < n)
  edge_symm := by
    intro a b
    simp only [Bool.and_assoc]
    rw [Bool.or_comm (decide (a + 1 = b)),
        Bool.and_comm (decide (a < n)) (decide (b < n))]
  edge_irrefl := by
    intro a
    simp
  edge_bounds := by
    intro a b h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2, h.2⟩

/-- Hardware well-formedness: one-qubit gates in range, every CZ on a coupled
pair. Strengthens `WF` (see `HWF.toWF`). -/
inductive HWF {n : ℕ} (g : Coupling n) : UCom n → Prop
  | seq  {c₁ c₂ : UCom n} : HWF g c₁ → HWF g c₂ → HWF g (.seq c₁ c₂)
  | app1 {gt : Gate1} {q : ℕ} : q < n → HWF g (.app1 gt q)
  | cz   {a b : ℕ} : g.edge a b = true → HWF g (.cz a b)

/-- Boolean hardware-well-formedness check. -/
def UCom.hwfb {n : ℕ} (g : Coupling n) : UCom n → Bool
  | .seq c₁ c₂ => c₁.hwfb g && c₂.hwfb g
  | .app1 _ q  => decide (q < n)
  | .cz a b    => g.edge a b

theorem UCom.hwfb_iff_HWF {n : ℕ} (g : Coupling n) (c : UCom n) :
    c.hwfb g = true ↔ HWF g c := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [hwfb, Bool.and_eq_true, ih₁, ih₂]
    constructor
    · rintro ⟨h₁, h₂⟩; exact .seq h₁ h₂
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, h₂⟩
  | app1 gt q =>
    simp only [hwfb, decide_eq_true_eq]
    constructor
    · exact .app1
    · intro h; cases h with | app1 hq => exact hq
  | cz a b =>
    simp only [hwfb]
    constructor
    · intro h; exact .cz h
    · intro h; cases h with | cz hab => exact hab

instance {n : ℕ} (g : Coupling n) (c : UCom n) : Decidable (HWF g c) :=
  decidable_of_iff _ (c.hwfb_iff_HWF g)

/-- Hardware validity strengthens well-formedness. -/
theorem HWF.toWF {n : ℕ} {g : Coupling n} {c : UCom n} (h : HWF g c) : WF c := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | app1 hq => exact .app1 hq
  | @cz a b hab =>
    obtain ⟨ha, hb⟩ := g.edge_bounds a b hab
    have hne : a ≠ b := by
      intro h; subst h
      rw [g.edge_irrefl] at hab; exact absurd hab (by simp)
    exact .cz ha hb hne

/-! ### Decidability smoke tests -/

example : HWF (lnnPath 4) (.cz 0 1) := by decide
example : ¬ HWF (lnnPath 4) (.cz 0 2) := by decide
example : HWF (lnnPath 4) (.seq (.app1 .x 0) (.cz 1 2)) := by decide
example (h : HWF (lnnPath 4) (.cz 0 1)) : WF (n := 4) (.cz 0 1) := h.toWF

/-! ### Gate-list transfer -/

/-- Per-gate hardware validity on the flat gate-list. -/
def GApp.respects1 {n : ℕ} (g : Coupling n) : GApp → Bool
  | .g1 _ q => decide (q < n)
  | .g2 a b => g.edge a b

theorem respects_toList {n : ℕ} {g : Coupling n} {c : UCom n} (h : HWF g c) :
    ∀ a ∈ c.toList, a.respects1 g = true := by
  induction h with
  | seq h₁ h₂ ih₁ ih₂ =>
    intro a ha
    rw [UCom.toList, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ih₁ a ha
    · exact ih₂ a ha
  | @app1 gt q hq =>
    intro a ha
    rw [UCom.toList, List.mem_singleton] at ha
    subst ha; simp [GApp.respects1, hq]
  | @cz a b hab =>
    intro x hx
    rw [UCom.toList, List.mem_singleton] at hx
    subst hx; simp [GApp.respects1, hab]

theorem HWF_ofList {n : ℕ} {g : Coupling n} (hn : 0 < n) {l : List GApp}
    (hl : ∀ a ∈ l, a.respects1 g = true) : HWF g (ofList (n := n) l) := by
  induction l with
  | nil => exact .app1 hn
  | cons a l ih =>
    refine .seq ?_ (ih fun x hx => hl x (List.mem_cons_of_mem a hx))
    have ha := hl a List.mem_cons_self
    cases a with
    | g1 gt q =>
      simp only [GApp.respects1, decide_eq_true_eq] at ha
      exact .app1 ha
    | g2 x y =>
      simp only [GApp.respects1] at ha
      exact .cz ha

theorem optAdj_respects {n : ℕ} {g : Coupling n} {l : List GApp}
    (hl : ∀ a ∈ l, a.respects1 g = true) :
    ∀ a ∈ optAdj l, a.respects1 g = true := by
  fun_induction optAdj with
  | case1 => exact hl
  | case2 a => exact hl
  | case3 g' g'' q rest gf hfuse ih =>
    refine ih ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simpa [GApp.respects1] using hl (.g1 g' q) List.mem_cons_self
    · exact hl a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
  | case4 g' g'' q rest hfuse ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hl _ List.mem_cons_self
    · exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) a ha
  | case5 g' q g'' q' rest hq ih =>
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
      · simpa [GApp.respects1] using hl (.g1 (.rz r₁) q) List.mem_cons_self
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

theorem optFix_respects {n : ℕ} {g : Coupling n} {l : List GApp}
    (hl : ∀ a ∈ l, a.respects1 g = true) :
    ∀ a ∈ optFix l, a.respects1 g = true := by
  fun_induction optFix with
  | case1 l _ ih => exact ih (optAdj_respects hl)
  | case2 l _ => exact hl

theorem optimize_HWF {n : ℕ} {g : Coupling n} {c : UCom n} (h : HWF g c) :
    HWF g (optimize c) :=
  HWF_ofList h.toWF.pos (optFix_respects (respects_toList h))

example (h : HWF (lnnPath 4) (.seq (.cz 0 1) (.cz 0 1))) :
    HWF (lnnPath 4) (optimize (.seq (.cz 0 1) (.cz 0 1))) := optimize_HWF h

end QpuCompiler
