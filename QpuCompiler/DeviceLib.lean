/-
QpuCompiler/DeviceLib.lean — encode ARBITRARY real device topologies as `Coupling n`.

## Why this file exists

`heavyHex : Coupling 12`, `heronPatch : Coupling 14`, and `heronMarrakesh : Coupling 12`
each spell out their edge relation as an explicit decidable disjunction. That method
works for a dozen qubits, but it fails for a real device. `ibm_marrakesh` has 352 edges
over 156 qubits. A disjunction of that size produces a term that the kernel must
process on every `decide` call.

The fix is to represent the graph as data: a canonical ordered edge list. We
discharge the three `Coupling` obligations once, generically, instead of once per
device. A new device then costs one `EdgeSpec` literal plus two `by decide` list
checks. The certifier runs against it unchanged.

## The representation

Edges are stored canonically: every edge appears exactly once, as `(lo, hi)` with
`lo < hi`. Adjacency is then

    edge a b  :=  (min a b, max a b) ∈ edges

This is symmetric by construction, because `min` and `max` are symmetric in their
arguments. So `edge_symm` needs no case analysis on the device at all. The other two
obligations follow from two finite properties of the list, each checkable by `decide`:

  * `ordered` : every stored pair has `p.1 < p.2`, so there are no self-loops, giving `edge_irrefl`
  * `bounded` : every stored pair has `p.2 < n`, giving `edge_bounds`

The payoff: this file proves `edge_symm`, `edge_irrefl`, and `edge_bounds` once, for
all devices. So the per-device cost is a membership test on a list, not a proof
search over a 352-way disjunction.
-/
import QpuCompiler.Hardware

namespace QpuCompiler

/-- A device topology as canonical edge data. `ordered` and `bounded` are the only
device-specific facts, and both are finite `decide` checks. -/
structure EdgeSpec (n : ℕ) where
  edges       : List (ℕ × ℕ)
  /-- Stated as a single `List.all` Bool computation, not as `∀ p ∈ edges, …`.
  This choice matters at real device sizes. The ∀-over-membership form makes
  `by decide` run an instance search per element. It exhausts `maxRecDepth` at
  about 176 edges. One `List.all` reduces to a straight fold that the kernel
  handles easily. -/
  ordered_all : edges.all (fun p => decide (p.1 < p.2)) = true
  bounded_all : edges.all (fun p => decide (p.2 < n)) = true

namespace EdgeSpec

variable {n : ℕ}

/-- Recover the pointwise form from the Bool fold. -/
theorem ordered (s : EdgeSpec n) : ∀ p ∈ s.edges, p.1 < p.2 := by
  intro p hp
  have h := List.all_eq_true.mp s.ordered_all p hp
  simpa using h

theorem bounded (s : EdgeSpec n) : ∀ p ∈ s.edges, p.2 < n := by
  intro p hp
  have h := List.all_eq_true.mp s.bounded_all p hp
  simpa using h

/-- Adjacency: look the canonical pair up. Symmetric by construction. -/
def rel (s : EdgeSpec n) (a b : ℕ) : Bool := (min a b, max a b) ∈ s.edges

theorem rel_symm (s : EdgeSpec n) (a b : ℕ) : s.rel a b = s.rel b a := by
  simp only [rel, Nat.min_comm a b, Nat.max_comm a b]

theorem rel_irrefl (s : EdgeSpec n) (a : ℕ) : s.rel a a = false := by
  simp only [rel, Nat.min_self, Nat.max_self, decide_eq_false_iff_not]
  intro hmem
  have := s.ordered _ hmem            -- (a, a).1 < (a, a).2, that is, a < a
  exact absurd this (Nat.lt_irrefl a)

theorem rel_bounds (s : EdgeSpec n) (a b : ℕ) (h : s.rel a b = true) : a < n ∧ b < n := by
  simp only [rel, decide_eq_true_eq] at h
  rcases Nat.le_total a b with hab | hab
  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab] at h
    have hb : b < n := s.bounded _ h
    exact ⟨lt_of_le_of_lt hab hb, hb⟩
  · rw [Nat.min_eq_right hab, Nat.max_eq_left hab] at h
    have ha : a < n := s.bounded _ h
    exact ⟨ha, lt_of_le_of_lt hab ha⟩

/-- **The generic construction.** Any well-formed edge list is a `Coupling`. -/
def toCoupling (s : EdgeSpec n) : Coupling n where
  edge        := s.rel
  edge_symm   := s.rel_symm
  edge_irrefl := s.rel_irrefl
  edge_bounds := s.rel_bounds

end EdgeSpec

/-! Canonicalization happens on the producer side, in
`harness/devices/gen_device_corpus.py`
(`sorted({(min(a,b), max(a,b)) for a, b in raw if a != b})`). There is deliberately
no Lean-side `canonEdges`. An unsorted Lean version cannot reproduce the
committed edge lists, so having both risks two normal forms that disagree.
Any `edges` field that is not canonical fails `ordered_all` or `bounded_all`
at build time. -/

end QpuCompiler
