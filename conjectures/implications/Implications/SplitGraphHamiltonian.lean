import Implications.SplitGraphSmallRowsSelection
import Implications.SplitGraphSmallRowsOneShared
import Implications.SplitGraphSmallRowsTwo
import Implications.SplitGraphTripleRowComplete

/-! The connectivity-two split-graph case of WOWII 199. -/

namespace SplitGraphHamiltonian

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The row bounds and two clique neighbors for each independent vertex
suffice for a Hamiltonian path in a nonempty split graph. -/
theorem hamiltonian_of_row_bounds
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (huniv : (Finset.univ : Finset V).Nonempty)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  by_cases htriple : ∃ t ∈ C, (row G I t).card = 3
  · obtain ⟨t, ht, hcard⟩ := htriple
    exact SplitGraphTripleRowComplete.hamiltonian_of_triple_row
      G C I t hC hdisj hpartition ht hcard hrow hdiff hdeg
  · have hsmall : ∀ q ∈ C, (row G I q).card ≤ 2 := by
      intro q hq
      have hb := hrow q hq
      have hn : (row G I q).card ≠ 3 := fun h => htriple ⟨q,hq,h⟩
      omega
    obtain ⟨left,right,hlC,hrC,hlAdj,hrAdj,hne,hcap,hbound⟩ :=
      SplitGraphSmallRowsSelection.exists_selected_neighbors G C I hsmall hdiff hdeg
    let S := C.filter (fun q => (I.filter (fun i => left i = q ∨ right i = q)).card = 2)
    have hS : S.card ≤ 3 := hbound
    by_cases h0 : S.card = 0
    · refine SplitGraphSmallRowsPath.hamiltonian_of_split_partition_selected_rows_le_one
        G C I hC hdisj hpartition left right hlC hrC hlAdj hrAdj hne ?_ huniv
      intro q hq
      have hb := hcap q hq
      change (I.filter (fun i => left i = q ∨ right i = q)).card ≤ 2 at hb
      have hn : (I.filter (fun i => left i = q ∨ right i = q)).card ≠ 2 := by
        intro h
        have hmem : q ∈ S := Finset.mem_filter.mpr ⟨hq,h⟩
        rw [Finset.card_eq_zero.mp h0] at hmem
        exact Finset.notMem_empty q hmem
      omega
    by_cases h1 : S.card = 1
    · exact SplitGraphSmallRowsOneShared.hamiltonian_of_unique_double_selected_row
        G C I hC hdisj hpartition left right hlC hrC hlAdj hrAdj hne hcap h1
    by_cases h2 : S.card = 2
    · exact SplitGraphSmallRowsTwo.hamiltonian_of_split_partition_two_double_rows
        G C I hC hdisj hpartition left right hlC hrC hlAdj hrAdj hne hsmall hdiff h2
    · have h3 : S.card = 3 := by omega
      exact SplitGraphSmallRowsThree.hamiltonian_of_split_partition_three_double_rows
        G C I hC hdisj hpartition left right hlC hrC hlAdj hrAdj hne hsmall hdiff h3 huniv

/-- A split graph with at least three vertices, connected after every
single-vertex deletion, and with no induced tree larger than four vertices,
has a Hamiltonian path. -/
theorem hamiltonian_of_two_connected_split
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hdisj : Disjoint C I) (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : ∀ q : V, (G.induce {x | x ≠ q}).Connected)
    (hTree : inducedTreeBound G 2) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨hrow, hdiff⟩ := rows_bounded_of_inducedTreeBound G C I 2 hTree hC hI hdisj
  have hdeg := SplitGraphTwoConnected.two_attachments_of_deletion_connected G C I
    hI hpartition hcard hconn
  refine hamiltonian_of_row_bounds G C I hC hdisj hpartition ?_ hrow hdiff hdeg
  apply Finset.card_pos.mp
  rw [Finset.card_univ]
  omega

end SplitGraphHamiltonian

#print axioms SplitGraphHamiltonian.hamiltonian_of_row_bounds
#print axioms SplitGraphHamiltonian.hamiltonian_of_two_connected_split
