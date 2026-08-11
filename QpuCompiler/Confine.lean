/-
QpuCompiler/Confine.lean — C3: verified multi-tenant confinement of secret qubits.

A client policy names an allowed physical region `A` (a decidable Bool predicate on
qubit indices) and a forbidden tenant region `F`. `confinedb A c` decides that every
non-trivial gate of `c` acts only on qubits in `A`. Identity gates are no-ops
(`denote (.app1 .id q) = I`), so the predicate exempts them. We prove that heavy-hex
routing (`route_hh`) preserves confinement (`route_hh_confine`) when the source is
routable within `A`. We also prove that confinement to `A`, disjoint from `F`, means
the routed circuit never touches `F` (`confinedb_avoids`). So compilation creates no
secret-forbidden co-location channel, the SWAP/crosstalk multi-tenant threat.

Headline: `route_hh_confine_correct` bundles HWF, CongPhase, and confinement.
-/
import QpuCompiler.CompileHH
import QpuCompiler.DeviceLib

namespace QpuCompiler

open scoped QpuCompiler

/-! ## Confinement predicate -/

/-- `c` acts only on qubits in region `A`. Identity gates are exempt: they denote to `I`. -/
def confinedb (A : ℕ → Bool) {n : ℕ} : UCom n → Bool
  | .seq c₁ c₂ => confinedb A c₁ && confinedb A c₂
  | .app1 .id _ => true
  | .app1 _ q   => A q
  | .cz a b     => A a && A b

/-! ## The SWAP macro touches only its two qubits -/

theorem swapEdge_confined {A : ℕ → Bool} {n u v : ℕ}
    (hu : A u = true) (hv : A v = true) : confinedb A (swapEdge n u v) = true := by
  simp [swapEdge, cnotMac, hMac, confinedb, hu, hv]

theorem swapEdgeNet_confined {A : ℕ → Bool} {n : ℕ} :
    ∀ {es : List (ℕ × ℕ)}, (∀ e ∈ es, A e.1 = true ∧ A e.2 = true) →
      confinedb A (swapEdgeNet n es) = true := by
  intro es
  induction es with
  | nil => intro _; simp [swapEdgeNet, confinedb]
  | cons e es ih =>
    obtain ⟨u, v⟩ := e
    intro hE
    have h1 := hE (u, v) List.mem_cons_self
    simp only [swapEdgeNet, confinedb, Bool.and_eq_true]
    exact ⟨swapEdge_confined h1.1 h1.2, ih (fun e he => hE e (List.mem_cons_of_mem _ he))⟩

/-! ## Routing a `cz` along a path stays within the path's vertices -/

theorem routeEdge_confined {A : ℕ → Bool} {n : ℕ} :
    ∀ {p : List ℕ}, (∀ v ∈ p, A v = true) → confinedb A (routeEdge n p) = true := by
  intro p
  rcases p with _ | ⟨v0, _ | ⟨v1, rest⟩⟩
  · intro _; simp [routeEdge, confinedb]
  · intro _; simp [routeEdge, confinedb]
  · intro hp
    have hv0 : A v0 = true := hp v0 (by simp)
    have hv1 : A v1 = true := hp v1 (by simp)
    have hE : ∀ e ∈ pathEdges (v1 :: rest), A e.1 = true ∧ A e.2 = true := by
      intro e he
      obtain ⟨h1, h2⟩ := pathEdges_endpoints_mem he
      exact ⟨hp e.1 (List.mem_cons_of_mem _ h1), hp e.2 (List.mem_cons_of_mem _ h2)⟩
    have hErev : ∀ e ∈ (pathEdges (v1 :: rest)).reverse, A e.1 = true ∧ A e.2 = true :=
      fun e h => hE e (List.mem_reverse.mp h)
    simp only [routeEdge, confinedb, Bool.and_eq_true]
    exact ⟨⟨swapEdgeNet_confined hErev, hv0, hv1⟩, swapEdgeNet_confined hE⟩

/-! ## Policy on the source: routable within `A` (each `cz`'s path lies in `A`) -/

/-- The source is routable within `A`: every gate qubit, and every routed `cz`
gate's `findPath`, lies in `A`. This predicate is decidable, so a client can check
it directly. -/
def routableb (A : ℕ → Bool) : UCom 12 → Bool
  | .seq c₁ c₂ => routableb A c₁ && routableb A c₂
  | .app1 .id _ => true
  | .app1 _ q   => A q
  | .cz a b     => (findPath a b).all A

/-- **Routing preserves confinement.** If the source is routable within `A`, the
routed circuit acts only on `A`. -/
theorem route_hh_confine {A : ℕ → Bool} :
    ∀ {c : UCom 12}, routableb A c = true → confinedb A (route_hh c) = true := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro hpol
    simp only [routableb, Bool.and_eq_true] at hpol
    simp only [route_hh, confinedb, Bool.and_eq_true]
    exact ⟨ih₁ hpol.1, ih₂ hpol.2⟩
  | app1 g q =>
    intro hpol
    cases g <;> simp_all [route_hh, confinedb, routableb]
  | cz a b =>
    intro hpol
    simp only [route_hh, routeCZ_hh]
    apply routeEdge_confined
    intro v hv
    exact (List.all_eq_true.mp hpol) v hv

/-! ## Soundness: confinement to `A` disjoint from `F` ⇒ never touches `F` -/

/-- If `c` is confined to `A`, and `A` is disjoint from the forbidden region `F`,
then `c` touches no qubit in `F`. Every gate is confined to the complement of `F`. -/
theorem confinedb_avoids {A F : ℕ → Bool} {n : ℕ} :
    ∀ {c : UCom n}, confinedb A c = true → (∀ x, A x = true → F x = false) →
      confinedb (fun x => !F x) c = true := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro hc hdis
    simp only [confinedb, Bool.and_eq_true] at hc ⊢
    exact ⟨ih₁ hc.1 hdis, ih₂ hc.2 hdis⟩
  | app1 g q =>
    intro hc hdis
    cases g <;> simp_all [confinedb]
  | cz a b =>
    intro hc hdis
    simp only [confinedb, Bool.and_eq_true] at hc ⊢
    obtain ⟨ha, hb⟩ := hc
    exact ⟨by simp [hdis a ha], by simp [hdis b hb]⟩

/-! ## Headline: routed circuit is correct, hardware-legal, and confined -/

/-- **C3 (security).** Take a source that is well-formed and routable within an
allowed region `A`, disjoint from a forbidden tenant region `F`. Heavy-hex routing
compiles it to a circuit with three properties. (1) The circuit is hardware-legal.
(2) It is equivalent to the source up to a global phase. (3) It is confined to `A`.
So the circuit never acts on any forbidden qubit. Routing creates no secret-`F`
co-location channel. -/
theorem route_hh_confine_correct {A F : ℕ → Bool} {c : UCom 12}
    (h : WF c) (hpol : routableb A c = true) (hdis : ∀ x, A x = true → F x = false) :
    HWF heavyHex (route_hh c)
      ∧ UCom.CongPhase (route_hh c) c
      ∧ confinedb (fun x => !F x) (route_hh c) = true :=
  ⟨route_hh_HWF h, route_hh_congPhase h,
   confinedb_avoids (route_hh_confine hpol) hdis⟩

/-! ## Compile-level confinement: `optimize` preserves confinement

The optimizer only cancels or merges gates on existing qubits, so it cannot expand
the support. We thread confinement through `optimize = ofList ∘ optFix ∘ toList`.
This mirrors the per-gate-predicate machinery of `optimize_HWF`. -/

/-- Per-gate confinement on the flat gate list (identity gates exempt). -/
def GApp.conf1 (A : ℕ → Bool) : GApp → Bool
  | .g1 .id _ => true
  | .g1 _ q   => A q
  | .g2 a b   => A a && A b

theorem conf1_g1_iff {A : ℕ → Bool} (q : ℕ) (g : Gate1) :
    GApp.conf1 A (.g1 g q) = true ↔ (g = .id ∨ A q = true) := by
  cases g <;> simp [GApp.conf1]

/-- Fusion preserves confinement: the fused gate stays on qubit `q`. -/
theorem conf1_fuse {A : ℕ → Bool} {q : ℕ} {g' g'' gf : Gate1}
    (hf : fuse g' g'' = some gf)
    (h' : GApp.conf1 A (.g1 g' q) = true) (h'' : GApp.conf1 A (.g1 g'' q) = true) :
    GApp.conf1 A (.g1 gf q) = true := by
  rw [conf1_g1_iff] at h' h'' ⊢
  rcases h' with rfl | ha
  · rcases h'' with rfl | ha
    · left; simpa [fuse] using hf.symm
    · right; exact ha
  · right; exact ha

theorem confinedb_toUCom {A : ℕ → Bool} {n : ℕ} (a : GApp) :
    confinedb A (a.toUCom (n := n)) = a.conf1 A := by
  cases a with
  | g1 g q => cases g <;> simp [GApp.toUCom, confinedb, GApp.conf1]
  | g2 x y => simp [GApp.toUCom, confinedb, GApp.conf1]

theorem conf_toList {A : ℕ → Bool} {n : ℕ} :
    ∀ {c : UCom n}, confinedb A c = true → ∀ a ∈ c.toList, a.conf1 A = true := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro h a ha
    simp only [confinedb, Bool.and_eq_true] at h
    rw [UCom.toList, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ih₁ h.1 a ha
    · exact ih₂ h.2 a ha
  | app1 gt q =>
    intro h a ha
    rw [UCom.toList, List.mem_singleton] at ha; subst ha
    cases gt <;> simp_all [confinedb, GApp.conf1]
  | cz a b =>
    intro h x hx
    rw [UCom.toList, List.mem_singleton] at hx; subst hx
    simp only [confinedb, Bool.and_eq_true] at h
    simp [GApp.conf1, h.1, h.2]

theorem conf_ofList {A : ℕ → Bool} {n : ℕ} :
    ∀ {l : List GApp}, (∀ a ∈ l, a.conf1 A = true) →
      confinedb A (ofList (n := n) l) = true := by
  intro l
  induction l with
  | nil => intro _; simp [ofList, confinedb]
  | cons a l ih =>
    intro hl
    have ha := hl a List.mem_cons_self
    simp only [ofList, confinedb, Bool.and_eq_true]
    exact ⟨(confinedb_toUCom a).trans ha, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))⟩

theorem optAdj_conf {A : ℕ → Bool} {l : List GApp}
    (hl : ∀ a ∈ l, a.conf1 A = true) : ∀ a ∈ optAdj l, a.conf1 A = true := by
  fun_induction optAdj with
  | case1 => exact hl
  | case2 a => exact hl
  | case3 g' g'' q rest gf hfuse ih =>
    refine ih ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact conf1_fuse hfuse (hl (.g1 g' q) List.mem_cons_self)
        (hl (.g1 g'' q) (List.mem_cons_of_mem _ List.mem_cons_self))
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
      · simpa [GApp.conf1] using hl (.g1 (.rz r₁) q) List.mem_cons_self
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

theorem optFix_conf {A : ℕ → Bool} {l : List GApp}
    (hl : ∀ a ∈ l, a.conf1 A = true) : ∀ a ∈ optFix l, a.conf1 A = true := by
  fun_induction optFix with
  | case1 l _ ih => exact ih (optAdj_conf hl)
  | case2 l _ => exact hl

/-- **`optimize` preserves confinement.** -/
theorem optimize_conf {A : ℕ → Bool} {n : ℕ} {c : UCom n}
    (h : confinedb A c = true) : confinedb A (optimize c) = true :=
  conf_ofList (optFix_conf (conf_toList h))

/-- **C3 at COMPILE level (route + optimize).** This removes the earlier caveat
that stated confinement only before `optimize`. The full compiled circuit is
hardware-legal, equal to the source up to a global phase, and it never touches
the forbidden region. -/
theorem compile_hh_confine_correct {A F : ℕ → Bool} {c : UCom 12}
    (h : WF c) (hpol : routableb A c = true) (hdis : ∀ x, A x = true → F x = false) :
    HWF heavyHex (optimize (route_hh c))
      ∧ UCom.CongPhase (optimize (route_hh c)) c
      ∧ confinedb (fun x => !F x) (optimize (route_hh c)) = true :=
  ⟨routeOpt_hh_HWF h, routeOpt_hh_congPhase h,
   optimize_conf (confinedb_avoids (route_hh_confine hpol) hdis)⟩

/-! ## Mode B: validation of ARBITRARY external transpiler output (decidable, no 2ⁿ)

The security-relevant checks, hardware-legality (`HWF`) and confinement or policy
(`confinedb`), are decidable structural predicates on the compiled circuit. So they
certify the output of any external transpiler, per instance, with no 2ⁿ matrix and
no layout recovery. Functional equivalence is the part that needs `denote`. See the
driver handoff for its scope. A tenant occupies the allowed slot `A = {0..5}`. The
co-tenant, or forbidden, region is `F = {6..11}`. -/

/-- Allowed physical region for a tenant (qubits 0–5 of the heavy-hex ring). -/
def tenantA : ℕ → Bool := fun q => decide (q < 6)
/-- Forbidden / co-tenant region (qubits 6–11). -/
def tenantF : ℕ → Bool := fun q => decide (6 ≤ q ∧ q < 12)

-- A compliant external output is certified hardware-legal AND confined to the tenant slot:
example : HWF heavyHex (.seq (.app1 .x 0) (.cz 0 1)) := by decide
example : confinedb tenantA (.seq (.app1 .x 0) (.cz 0 1) : UCom 12) = true := by decide
-- A violating external output (touches the forbidden co-tenant region) is REJECTED:
example : confinedb tenantA (.cz 0 6 : UCom 12) = false := by decide   -- policy violation caught
example : ¬ HWF heavyHex (.cz 0 6) := by decide                       -- illegal (0,6 not an edge)
-- tenant regions are genuinely disjoint (the policy's A ∩ F = ∅ hypothesis is real):
example : ∀ x, tenantA x = true → tenantF x = false := by
  intro x hx; simp only [tenantA, decide_eq_true_eq] at hx
  simp only [tenantF, decide_eq_false_iff_not]; omega

/-! ## NF-1: one-call security certificate for an externally supplied circuit

`certifySecurity` validates any external transpiler output (a `UCom n`, for example
ingested from OpenQASM through `ofList`). It checks the output against a device `g`
and a forbidden region `F`, in one call. It checks hardware-legality (`HWF`,
decidable) and confinement (`confinedb`). `certifySecurity_sound` gives the
kernel-checked guarantee behind an `accepted` verdict: no 2ⁿ check, no layout
recovery, and it works on arbitrary output. -/

structure CertResult where
  hardwareLegal : Bool
  policyConfined : Bool

/-- The certificate is accepted iff the circuit is hardware-legal AND policy-confined. -/
def CertResult.accepted (r : CertResult) : Bool := r.hardwareLegal && r.policyConfined

/-- One-call security validator over an untrusted external circuit. -/
def certifySecurity {n : ℕ} (g : Coupling n) (F : ℕ → Bool) (ext : UCom n) : CertResult :=
  { hardwareLegal := decide (HWF g ext), policyConfined := confinedb (fun x => !F x) ext }

/-- **Soundness of the validator.** An accepted verdict gives a kernel-checked
guarantee that the external circuit is hardware-legal and touches no forbidden
qubit. -/
theorem certifySecurity_sound {n : ℕ} (g : Coupling n) (F : ℕ → Bool) (ext : UCom n)
    (h : (certifySecurity g F ext).accepted = true) :
    HWF g ext ∧ confinedb (fun x => !F x) ext = true := by
  simp only [CertResult.accepted, certifySecurity, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-! ## NF-3: a genuine degree-3 heavy-hex vertex (beyond the 12-node ring toy model)

`heavyHexFrag : Coupling 4` is a heavy-hex site qubit `0` of degree 3, joined to
qubits `1, 2, 3`. The C₁₂ ring has a maximum degree of 2, so this example shows
the distinguishing heavy-hex feature (flag #4). Tenant partition: the allowed
region is `A = {0,1,2}`, and the forbidden co-tenant region is `F = {3}`. -/

/-- The star with edges `0–1`, `0–2`, `0–3`, built through the generic `EdgeSpec`
construction (`DeviceLib.lean`) instead of three hand-written obligations. -/
def specHeavyHexFrag : EdgeSpec 4 where
  edges := [(0,1), (0,2), (0,3)]
  ordered_all := by decide
  bounded_all := by decide

def heavyHexFrag : Coupling 4 := specHeavyHexFrag.toCoupling

/-- Qubit 0 genuinely has degree 3 (heavy-hex site), unlike the ring's degree-2. -/
example : heavyHexFrag.edge 0 1 = true ∧ heavyHexFrag.edge 0 2 = true
    ∧ heavyHexFrag.edge 0 3 = true := by decide
example : heavyHexFrag.edge 1 2 = false := by decide  -- the three neighbours are not interconnected

def fragF : ℕ → Bool := fun q => decide (q = 3)  -- forbidden co-tenant qubit

-- A compliant external output over the fragment is ACCEPTED (one call):
example : (certifySecurity heavyHexFrag fragF (.seq (.app1 .x 0) (.cz 0 1) : UCom 4)).accepted
    = true := by decide
-- Front-end ingestion path (external circuit as a gate list → `ofList` → certify):
example : (certifySecurity heavyHexFrag fragF (ofList [.g1 .x 0, .g2 0 1])).accepted = true := by
  decide
-- THE multi-tenant threat, CAUGHT: `.cz 0 3` is HARDWARE-LEGAL (0-3 is an edge), yet it
-- touches the forbidden co-tenant qubit 3. The validator rejects it on the policy check:
example : (certifySecurity heavyHexFrag fragF (.cz 0 3 : UCom 4)).hardwareLegal = true := by decide
example : (certifySecurity heavyHexFrag fragF (.cz 0 3 : UCom 4)).accepted = false := by decide

end QpuCompiler
