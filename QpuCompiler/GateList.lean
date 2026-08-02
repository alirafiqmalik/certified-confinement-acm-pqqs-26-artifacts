/-
QpuCompiler/GateList.lean — voqc-style flat gate-application list normal form
(UnitaryListRepresentation). `seq` trees flatten to `List GApp`. `listDenote` is
the reversed product (sqir order). Round-trip theorems connect the two forms.
-/
import QpuCompiler.Denote
import QpuCompiler.Equiv

namespace QpuCompiler

/-- Flat gate application (register size is a phantom bound, as in `UCom`). -/
inductive GApp : Type
  | g1 (g : Gate1) (q : ℕ)
  | g2 (a b : ℕ)                     -- CZ
  deriving DecidableEq

/-- Per-gate well-formedness bound (mirrors `UCom.wfb` leaf cases). -/
def GApp.wfb (n : ℕ) : GApp → Bool
  | .g1 _ q => decide (q < n)
  | .g2 a b => decide (a < n) && decide (b < n) && decide (a ≠ b)

/-- Matrix of one gate application. -/
noncomputable def GApp.denote (n : ℕ) : GApp → Square n
  | .g1 g q => padU n q g.matrix
  | .g2 a b => padCZ n a b

/-- Back to the tree IR (single application). -/
def GApp.toUCom {n : ℕ} : GApp → UCom n
  | .g1 g q => .app1 g q
  | .g2 a b => .cz a b

theorem GApp.denote_toUCom {n : ℕ} (a : GApp) :
    QpuCompiler.denote (a.toUCom (n := n)) = a.denote n := by cases a <;> rfl

/-- Flatten a circuit to its gate list (program order). -/
def UCom.toList {n : ℕ} : UCom n → List GApp
  | .seq c₁ c₂ => c₁.toList ++ c₂.toList
  | .app1 g q  => [.g1 g q]
  | .cz a b    => [.g2 a b]

/-- Denotation of a gate list: reversed product (sqir convention),
`listDenote n (a :: l) = listDenote n l * a.denote n`. -/
noncomputable def listDenote (n : ℕ) : List GApp → Square n
  | []     => 1
  | a :: l => listDenote n l * a.denote n

@[simp] theorem listDenote_nil (n : ℕ) : listDenote n [] = 1 := rfl
@[simp] theorem listDenote_cons (n : ℕ) (a : GApp) (l : List GApp) :
    listDenote n (a :: l) = listDenote n l * a.denote n := rfl

theorem listDenote_append (n : ℕ) (l₁ l₂ : List GApp) :
    listDenote n (l₁ ++ l₂) = listDenote n l₂ * listDenote n l₁ := by
  induction l₁ with
  | nil => rw [List.nil_append, listDenote_nil, mul_one]
  | cons a l ih => rw [List.cons_append, listDenote_cons, listDenote_cons, ih, mul_assoc]

theorem denote_toList {n : ℕ} (c : UCom n) : listDenote n c.toList = denote c := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    rw [UCom.toList, listDenote_append, ih₁, ih₂]; rfl
  | app1 g q => rw [UCom.toList, listDenote_cons, listDenote_nil, one_mul]; rfl
  | cz a b => rw [UCom.toList, listDenote_cons, listDenote_nil, one_mul]; rfl

/-- Rebuild a circuit. `[]` becomes the derived skip `app1 .id 0`. -/
def ofList {n : ℕ} : List GApp → UCom n
  | []     => .app1 .id 0
  | a :: l => .seq a.toUCom (ofList l)

theorem denote_ofList {n : ℕ} (hn : 0 < n) (l : List GApp) :
    denote (ofList (n := n) l) = listDenote n l := by
  induction l with
  | nil =>
    show padU n 0 Gate1.id.matrix = 1
    exact padU_one (by omega)
  | cons a l ih =>
    show denote (ofList (n := n) l) * denote (GApp.toUCom a) = _
    rw [ih, GApp.denote_toUCom, listDenote_cons]

/-! ### Well-formedness transfer -/

theorem wfb_toList {n : ℕ} {c : UCom n} (h : WF c) :
    ∀ a ∈ c.toList, a.wfb n = true := by
  induction h with
  | seq h₁ h₂ ih₁ ih₂ =>
    intro a ha
    rw [UCom.toList, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ih₁ a ha
    · exact ih₂ a ha
  | @app1 g q hq =>
    intro a ha
    rw [UCom.toList, List.mem_singleton] at ha
    subst ha
    simp [GApp.wfb, hq]
  | @cz a b ha hb hab =>
    intro x hx
    rw [UCom.toList, List.mem_singleton] at hx
    subst hx
    simp [GApp.wfb, ha, hb, hab]

theorem WF_ofList {n : ℕ} (hn : 0 < n) {l : List GApp}
    (hl : ∀ a ∈ l, a.wfb n = true) : WF (ofList (n := n) l) := by
  induction l with
  | nil => exact .app1 hn
  | cons a l ih =>
    refine .seq ?_ (ih fun x hx => hl x (List.mem_cons_of_mem a hx))
    have ha := hl a List.mem_cons_self
    cases a with
    | g1 g q =>
      simp only [GApp.wfb, decide_eq_true_eq] at ha
      exact .app1 ha
    | g2 x y =>
      simp only [GApp.wfb, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact .cz ha.1.1 ha.1.2 ha.2

end QpuCompiler
