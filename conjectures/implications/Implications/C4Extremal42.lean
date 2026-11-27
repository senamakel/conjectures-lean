import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The one-vertex counting reduction for `ex(42, C4)`

Given the explicit `ex(41,C4) ≤ 132` input, each of the 42 vertex deletions has at most
132 edges. Counting each edge in its 40 non-endpoint deletions gives `40e ≤ 42·132`.
If `e = 138`, at least one deletion must retain all 132 edges; that vertex has degree six.
-/

namespace C4Extremal42

/-- The actual edge count after taking the induced subgraph off one vertex. -/
noncomputable def inducedDeletionCount (G : SimpleGraph (Fin 42)) (v : Fin 42)
    [DecidableRel G.Adj] : ℕ := by
  classical
  exact (G.induce ({v}ᶜ : Set (Fin 42))).edgeFinset.card

/-- An induced deletion has exactly the original edge count minus the deleted vertex degree. -/
theorem inducedDeletionCount_eq (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (v : Fin 42) :
    inducedDeletionCount G v = G.edgeFinset.card - G.degree v := by
  rw [inducedDeletionCount, SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]

/-- Summing the actual induced deletion sizes counts every original edge 40 times. -/
theorem sum_inducedDeletionCount (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj] :
    (∑ v : Fin 42, inducedDeletionCount G v) = 40 * G.edgeFinset.card := by
  classical
  have hle : ∀ v ∈ (Finset.univ : Finset (Fin 42)), G.degree v ≤ G.edgeFinset.card := by
    intro v hv
    exact SimpleGraph.degree_le_card_edgeFinset G v
  calc
    (∑ v : Fin 42, inducedDeletionCount G v) =
        ∑ v : Fin 42, (G.edgeFinset.card - G.degree v) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact inducedDeletionCount_eq G v
    _ = (∑ _v : Fin 42, G.edgeFinset.card) - ∑ v : Fin 42, G.degree v := by
      rw [Finset.sum_tsub_distrib Finset.univ hle]
    _ = 40 * G.edgeFinset.card := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges G]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; omega

/-- The actual induced 41-vertex bound implies the 42-vertex edge bound. -/
theorem simpleGraph_edge_count_le_138 (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (h41 : ∀ v, inducedDeletionCount G v ≤ 132) : G.edgeFinset.card ≤ 138 := by
  have hsum : (∑ v : Fin 42, inducedDeletionCount G v) ≤ 42 * 132 := by
    calc
      (∑ v : Fin 42, inducedDeletionCount G v) ≤ ∑ _v : Fin 42, 132 :=
        Finset.sum_le_sum fun v _ => h41 v
      _ = 42 * 132 := by simp
  rw [sum_inducedDeletionCount] at hsum
  omega

/-- If the edge count is 138, some induced deletion is an extremal 41-vertex graph,
and the deleted vertex has degree six. -/
theorem simpleGraph_extremal_vertex_degree_six (G : SimpleGraph (Fin 42))
    [DecidableRel G.Adj] (h41 : ∀ v, inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138) :
    ∃ v : Fin 42, G.degree v = 6 ∧ inducedDeletionCount G v = 132 := by
  have hsum := sum_inducedDeletionCount G
  have hexist : ∃ v : Fin 42, inducedDeletionCount G v = 132 := by
    by_contra hn
    have hlt : ∀ v : Fin 42, inducedDeletionCount G v ≤ 131 := by
      intro v
      have hv := h41 v
      by_contra hnot
      have heq : inducedDeletionCount G v = 132 := by omega
      exact hn ⟨v, heq⟩
    have hsmall : (∑ v : Fin 42, inducedDeletionCount G v) ≤ 42 * 131 := by
      calc
        (∑ v : Fin 42, inducedDeletionCount G v) ≤ ∑ _v : Fin 42, 131 :=
          Finset.sum_le_sum fun v _ => hlt v
        _ = 42 * 131 := by simp
    rw [hsum, he] at hsmall
    omega
  obtain ⟨v, hv⟩ := hexist
  refine ⟨v, ?_, hv⟩
  rw [inducedDeletionCount_eq] at hv
  have hdeg : G.degree v ≤ G.edgeFinset.card := by
    exact SimpleGraph.degree_le_card_edgeFinset G v
  omega

/-- A vertex of degree six gives six neighbors with no shared neighbor in its induced deletion,
provided that any two vertices have at most one common neighbor in the original graph. -/
theorem compatible_six_of_degree_six (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hC4 : ∀ u w, u ≠ w → (G.commonNeighbors u w).Subsingleton)
    {v : Fin 42} (hv : G.degree v = 6) :
    ∃ S : Finset (Fin 42), S.card = 6 ∧ v ∉ S ∧
      ∀ u ∈ S, ∀ w ∈ S, u ≠ w → ∀ x, x ≠ v → G.Adj u x → ¬ G.Adj w x := by
  refine ⟨G.neighborFinset v, ?_, ?_, ?_⟩
  · rw [SimpleGraph.card_neighborFinset_eq_degree, hv]
  · simp
  · intro u hu w hw huw x hx hux hwx
    have huv : G.Adj u v := ((G.mem_neighborFinset v u).mp hu).symm
    have hwv : G.Adj w v := ((G.mem_neighborFinset v w).mp hw).symm
    exact hx (hC4 u w huw ⟨hux, hwx⟩ ⟨huv, hwv⟩)

/-- If extremal 41-vertex deletions forbid compatible six-sets, the 42-vertex bound drops to 137. -/
theorem simpleGraph_edge_count_le_137_of_no_compatible_six
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (h41 : ∀ v, inducedDeletionCount G v ≤ 132)
    (hC4 : ∀ u w, u ≠ w → (G.commonNeighbors u w).Subsingleton)
    (hno : ∀ v, inducedDeletionCount G v = 132 →
      ¬ ∃ S : Finset (Fin 42), S.card = 6 ∧ v ∉ S ∧
        ∀ u ∈ S, ∀ w ∈ S, u ≠ w → ∀ x, x ≠ v → G.Adj u x → ¬ G.Adj w x) :
    G.edgeFinset.card ≤ 137 := by
  have hle := simpleGraph_edge_count_le_138 G h41
  by_contra! h
  have he : G.edgeFinset.card = 138 := by omega
  obtain ⟨v, hv, hd⟩ := simpleGraph_extremal_vertex_degree_six G h41 he
  exact hno v hd (compatible_six_of_degree_six G hC4 hv)

#print axioms simpleGraph_edge_count_le_138
#print axioms simpleGraph_extremal_vertex_degree_six
#print axioms simpleGraph_edge_count_le_137_of_no_compatible_six

end C4Extremal42
