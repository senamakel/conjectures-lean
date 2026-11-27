import Mathlib

/-!
Bridge lemmas for the split-graph case of Written on the Wall II #199.

The Formal Conjectures helpers for largest induced trees are not a dependency of this package.
We use the equivalent Mathlib-level premise `inducedTreeBound`: every induced tree has at most
`k + 2` vertices. The star and double-star trees are given explicitly as hypotheses here, so the
resulting row bounds are independent of any external definition of `largestInducedTreeSize`.
-/

namespace SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The independent-set vertices adjacent to a given clique vertex. -/
def row (G : SimpleGraph V) (I : Finset V) (c : V) : Finset V :=
  I.filter (fun v => G.Adj c v)

/-- The symmetric difference of the rows of two clique vertices. -/
def rowDiff (G : SimpleGraph V) (I : Finset V) (c d : V) : Finset V :=
  (row G I c \ row G I d) ∪ (row G I d \ row G I c)

/-- A Mathlib-level formulation of the bound on the largest induced tree. -/
def inducedTreeBound (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ s : Finset V, (G.induce (s : Set V)).IsTree → s.card ≤ k + 2

/-- The induced star bound gives the size bound on each row. -/
theorem row_card_le (G : SimpleGraph V) (C I : Finset V) (k : ℕ)
    (hdisj : Disjoint C I)
    (hTreeBound : inducedTreeBound G k)
    (hStar : ∀ c ∈ C,
      (G.induce ((insert c (row G I c) : Finset V) : Set V)).IsTree) :
    ∀ c ∈ C, (row G I c).card ≤ k + 1 := by
  classical
  intro c hc
  have hcI : c ∉ I := by
    intro hci
    exact (Finset.disjoint_left.mp hdisj hc hci)
  have hcn : c ∉ row G I c := by
    simp [row, G.irrefl]
  have hbound := hTreeBound (insert c (row G I c)) (hStar c hc)
  rw [Finset.card_insert_of_notMem hcn] at hbound
  omega

/-- The induced double-star bound controls the symmetric difference of every pair of rows. -/
theorem row_symmDiff_card_le (G : SimpleGraph V) (C I : Finset V) (k : ℕ)
    (hdisj : Disjoint C I)
    (hTreeBound : inducedTreeBound G k)
    (hDoubleStar : ∀ c ∈ C, ∀ d ∈ C, c ≠ d →
      (G.induce
        ((insert c (insert d (rowDiff G I c d) : Finset V) : Finset V) : Set V)).IsTree) :
    ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ k := by
  classical
  intro c hc d hd hcd
  have hcI : c ∉ I := by
    intro hci
    exact (Finset.disjoint_left.mp hdisj hc hci)
  have hdI : d ∉ I := by
    intro hdi
    exact (Finset.disjoint_left.mp hdisj hd hdi)
  have hcRow : c ∉ rowDiff G I c d := by
    simp only [rowDiff, Finset.mem_union, Finset.mem_sdiff, row, Finset.mem_filter]
    intro h
    rcases h with h | h
    · exact hcI h.2
    · exact hcI h.2
  have hdRow : d ∉ rowDiff G I c d := by
    simp only [rowDiff, Finset.mem_union, Finset.mem_sdiff, row, Finset.mem_filter]
    intro h
    rcases h with h | h
    · exact hdI h.2
    · exact hdI h.2
  have hcdRow : c ∉ insert d (rowDiff G I c d) := by
    simp [hcd, hcRow]
  have hTree := hTreeBound
    (insert c (insert d (rowDiff G I c d))) (hDoubleStar c hc d hd hcd)
  rw [Finset.card_insert_of_notMem hcdRow, Finset.card_insert_of_notMem hdRow] at hTree
  omega

/-- Both row constraints used by the path construction, packaged together. -/
theorem rows_bounded_of_inducedTreeBound
    (G : SimpleGraph V) (C I : Finset V) (k : ℕ)
    (hdisj : Disjoint C I)
    (hTreeBound : inducedTreeBound G k)
    (hStar : ∀ c ∈ C,
      (G.induce ((insert c (row G I c) : Finset V) : Set V)).IsTree)
    (hDoubleStar : ∀ c ∈ C, ∀ d ∈ C, c ≠ d →
      (G.induce
        ((insert c (insert d (rowDiff G I c d) : Finset V) : Finset V) : Set V)).IsTree) :
    (∀ c ∈ C, (row G I c).card ≤ k + 1) ∧
      (∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ k) := by
  exact ⟨row_card_le G C I k hdisj hTreeBound hStar,
    row_symmDiff_card_le G C I k hdisj hTreeBound hDoubleStar⟩

end SplitGraphTrees

#print axioms SplitGraphTrees.row_card_le
#print axioms SplitGraphTrees.row_symmDiff_card_le
