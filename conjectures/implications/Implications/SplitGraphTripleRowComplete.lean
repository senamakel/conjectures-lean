import Implications.SplitGraphManyOutsiders
import Implications.SplitGraphOneOutsiderRows
import Implications.SplitGraphTripleRowPath

/-!
The central-triple case of the split-graph row formulation holds for every
number of independent vertices outside the triple.
-/

namespace SplitGraphTripleRowComplete

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique row of size three forces a Hamiltonian path under the row and
attachment bounds in the connectivity-two split-graph formulation. -/
theorem hamiltonian_of_triple_row
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (ht : t ∈ C) (hA : (row G I t).card = 3)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  by_cases hzero : (I \ row G I t).card = 0
  · have hsubset : row G I t ⊆ I := Finset.filter_subset _ _
    have hreverse : I ⊆ row G I t :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hzero)
    have hI : row G I t = I := Finset.Subset.antisymm hsubset hreverse
    exact SplitGraphTripleRowPath.hamiltonian_of_split_partition_triple_row_of_rows
      G C I t hC hdisj hpartition ht hI (hI ▸ hA) hdiff hdeg
  by_cases hone : (I \ row G I t).card = 1
  · refine SplitGraphOneOutsiderRows.hamiltonian_of_one_outsider
      G C I t hC hdisj hpartition ht hA hone hrow (fun q hq => ?_) hdeg
    by_cases h : t = q
    · subst q
      simp [rowDiff]
    · exact hdiff t ht q hq h
  · exact SplitGraphManyOutsiders.hamiltonian_of_many_outsiders
      G C I t hC hdisj hpartition ht hA (by omega) hrow hdiff hdeg

end SplitGraphTripleRowComplete

#print axioms SplitGraphTripleRowComplete.hamiltonian_of_triple_row
