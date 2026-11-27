import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The one-vertex counting reduction for `ex(42, C4)`

Given the explicit `ex(41,C4) ≤ 132` input, each of the 42 vertex deletions has at most
132 edges. Counting each edge in its 40 non-endpoint deletions gives `40e ≤ 42·132`.
If `e = 138`, at least one deletion must retain all 132 edges; that vertex has degree six.
-/

namespace C4Extremal42

/-- The actual edge count after taking the induced subgraph off one vertex. -/
noncomputable def inducedDeletionCount (G : SimpleGraph (Fin 42)) (v : Fin 42) : ℕ :=
  (G.induce ({v}ᶜ : Set (Fin 42))).edgeFinset.card

/-- An induced deletion has exactly the original edge count minus the deleted vertex degree. -/
theorem inducedDeletionCount_eq (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (v : Fin 42) :
    inducedDeletionCount G v = G.edgeFinset.card - G.degree v := by
  rw [inducedDeletionCount, SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]


/-- The edge-counting consequence of the 41-vertex extremal bound. `deletionCount v`
records the edges after deleting `v`; `hcount` is the double-counting identity. -/
theorem edge_count_le_138
    (e : ℕ) (deletionCount : Fin 42 → ℕ)
    (hdelete : ∀ v, deletionCount v ≤ 132)
    (hcount : ∑ v : Fin 42, deletionCount v = 40 * e) : e ≤ 138 := by
  have hsum : (∑ v : Fin 42, deletionCount v) ≤ 42 * 132 := by
    calc
      (∑ v : Fin 42, deletionCount v) ≤ ∑ _v : Fin 42, 132 :=
        Finset.sum_le_sum fun v _ => hdelete v
      _ = 42 * 132 := by simp
  rw [hcount] at hsum
  omega

/-- An extremal 138-edge graph has a degree-six deletion retaining 132 edges.
`hcount` is the deletion double-counting identity; `138 - deletionCount v` is the
number of edges incident to `v`. -/
theorem extremal_vertex_degree_six
    (deletionCount : Fin 42 → ℕ)
    (hdelete : ∀ v, deletionCount v ≤ 132)
    (hcount : ∑ v : Fin 42, deletionCount v = 40 * 138) :
    ∃ v : Fin 42, deletionCount v = 132 ∧ 138 - deletionCount v = 6 := by
  by_contra hn
  have hlt : ∀ v : Fin 42, deletionCount v ≤ 131 := by
    intro v
    have hv := hdelete v
    by_contra hnot
    have heq : deletionCount v = 132 := by omega
    exact hn ⟨v, heq, by omega⟩
  have hsum : (∑ v : Fin 42, deletionCount v) ≤ 42 * 131 := by
    calc
      (∑ v : Fin 42, deletionCount v) ≤ ∑ _v : Fin 42, 131 :=
        Finset.sum_le_sum fun v _ => hlt v
      _ = 42 * 131 := by simp
  rw [hcount] at hsum
  omega

#print axioms edge_count_le_138
#print axioms extremal_vertex_degree_six

end C4Extremal42
