import Implications.C4DegreeEightCap
import Implications.C4PolaritySurvivorBound

/-! Necessary graph conditions for an exhaustive 138-edge search on 42 vertices. -/

namespace C4Extremal42

open Implications.C4PolaritySurvivorBound

/-- Yan's general bound applies to all single deletions of any 42-vertex
four-cycle-free graph. -/
theorem deletion_count_le_132_of_ex41
    (h41 : Ex41C4Bound) (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hfree : C4VertexExtension.C4Free G) (v : Fin 42) :
    inducedDeletionCount G v ≤ 132 := by
  classical
  let S : Set (Fin 42) := {v}ᶜ
  have hcard : Fintype.card S = 41 := by
    change Fintype.card {i : Fin 42 // i ≠ v} = 41
    simp [Fintype.card_subtype_compl]
  have hbound := h41 (G.induce S) hcard (c4Free_induce G hfree S)
  simpa only [inducedDeletionCount, S, SimpleGraph.edgeFinset_card,
    Set.fintypeCard_eq_ncard] using hbound

/-- Given the 41-vertex bound, any 42-vertex graph improving on 137 edges
has exactly 138 edges. It has degrees six through eight, at most four
degree-eight vertices, and 18 to 22 deletions that retain 132 edges. -/
theorem search_constraints_of_edge_count_gt_137
    (h41 : Ex41C4Bound) (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hfree : C4VertexExtension.C4Free G) (hedges : 137 < G.edgeFinset.card) :
    G.edgeFinset.card = 138 ∧
      (∀ v, 6 ≤ G.degree v ∧ G.degree v ≤ 8) ∧
      (Finset.univ.filter fun v => G.degree v = 8).card ≤ 4 ∧
      (let k := (Finset.univ.filter fun v => inducedDeletionCount G v = 132).card
       18 ≤ k ∧ k ≤ 22) := by
  have hdel := deletion_count_le_132_of_ex41 h41 G hfree
  have hupper := simpleGraph_edge_count_le_138 G hdel
  have heq : G.edgeFinset.card = 138 := by omega
  exact ⟨heq, C4DegreeBounds.degree_window_of_extremal_42 G hdel heq hfree,
    C4DegreeEightCap.degree_eight_count_le_four_of_extremal_42 G hdel heq hfree,
    C4DegreeEightCap.count_extremal_deletions_bounds G hdel heq hfree⟩

#print axioms deletion_count_le_132_of_ex41
#print axioms search_constraints_of_edge_count_gt_137

end C4Extremal42
