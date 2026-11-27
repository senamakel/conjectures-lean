import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# The one-vertex counting reduction for `ex(42, C4)`

The input from `ex(41,C4) ≤ 132` is that each vertex deletion of a C4-free graph has
at most 132 edges. For a simple graph, deleting a vertex removes exactly its degree in
edges. Summing the remaining-edge counts counts every edge 40 times.
-/

namespace C4Extremal42

classical

/-- Edge count left after deleting a vertex. -/
def deletionEdgeCount (G : SimpleGraph (Fin 42)) (v : Fin 42) : ℕ :=
  G.edgeFinset.card - G.degree v

/-- The deletion sum counts each edge once for each of the 40 vertices it does not meet. -/
theorem sum_deletionEdgeCount (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj] :
    (∑ v : Fin 42, deletionEdgeCount G v) = 40 * G.edgeFinset.card := by
  classical
  unfold deletionEdgeCount
  rw [Finset.sum_sub_distrib]
  have hdeg := G.sum_degrees_eq_twice_card_edges
  have hconst : (∑ _v : Fin 42, G.edgeFinset.card) = 42 * G.edgeFinset.card := by simp
  omega

/-- The explicit 41-vertex extremal bound on every deletion implies `ex(42,C4) ≤ 138`.
The hypothesis `h41` is the pointwise form of `ex(41,C4) ≤ 132` for the 42-vertex graph. -/
theorem edge_count_le_138 (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (h41 : ∀ v, deletionEdgeCount G v ≤ 132) : G.edgeFinset.card ≤ 138 := by
  classical
  have hsum : (∑ v : Fin 42, deletionEdgeCount G v) ≤ 42 * 132 := by
    calc
      (∑ v : Fin 42, deletionEdgeCount G v) ≤ ∑ _v : Fin 42, 132 :=
        Finset.sum_le_sum fun v _ => h41 v
      _ = 42 * 132 := by simp
  rw [sum_deletionEdgeCount] at hsum
  omega

/-- A 138-edge graph under the 41-vertex bound has a degree-six vertex whose deletion
leaves exactly 132 edges, an extremal 41-vertex seed. -/
theorem extremal_vertex_degree_six (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (h41 : ∀ v, deletionEdgeCount G v ≤ 132)
    (he : G.edgeFinset.card = 138) :
    ∃ v : Fin 42, G.degree v = 6 ∧ deletionEdgeCount G v = 132 := by
  classical
  have hsum := sum_deletionEdgeCount G
  have hexist : ∃ v : Fin 42, deletionEdgeCount G v = 132 := by
    by_contra hn
    have hlt : ∀ v : Fin 42, deletionEdgeCount G v ≤ 131 := by
      intro v
      have hv := h41 v
      by_contra hnot
      have heq : deletionEdgeCount G v = 132 := by omega
      exact hn ⟨v, heq⟩
    have hsmall : (∑ v : Fin 42, deletionEdgeCount G v) ≤ 42 * 131 := by
      calc
        (∑ v : Fin 42, deletionEdgeCount G v) ≤ ∑ _v : Fin 42, 131 :=
          Finset.sum_le_sum fun v _ => hlt v
        _ = 42 * 131 := by simp
    rw [hsum, he] at hsmall
    omega
  obtain ⟨v, hv⟩ := hexist
  refine ⟨v, ?_, hv⟩
  have hdeg : G.degree v ≤ G.edgeFinset.card := by
    exact SimpleGraph.degree_le_card_edgeFinset G v
  unfold deletionEdgeCount at hv
  omega

#print axioms sum_deletionEdgeCount
#print axioms edge_count_le_138
#print axioms extremal_vertex_degree_six

end C4Extremal42
