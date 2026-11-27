import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# The one-vertex counting reduction for `ex(42, C4)`

The combinatorial input is the explicit bound `ex(41,C4) ≤ 132`: every vertex deletion
from a C4-free 42-vertex graph has at most 132 edges. The lemmas below formalize the
counting step from that input. `deletionCount v` is the edge count after deleting `v`;
counting each edge in all deletions gives `40 * e`.
-/

namespace C4Extremal42

/-- If all 41-vertex deletions have at most 132 edges, the deletion-count identity
implies the 42-vertex graph has at most 138 edges. -/
theorem edge_count_le_138
    (e : ℕ) (deletionCount : Fin 42 → ℕ)
    (hdelete : ∀ v, deletionCount v ≤ 132)
    (hcount : ∑ v : Fin 42, deletionCount v = 40 * e) : e ≤ 138 := by
  have hsum : (∑ v : Fin 42, deletionCount v) ≤ 42 * 132 := by
    calc
      (∑ v : Fin 42, deletionCount v) ≤ ∑ _v : Fin 42, 132 := Finset.sum_le_sum fun v _ => hdelete v
      _ = 42 * 132 := by simp
  rw [hcount] at hsum
  omega

/-- At 138 edges some vertex deletion retains all 132 edges, hence that vertex
has degree six. Here `e - deletionCount v` is the number of edges incident to `v`. -/
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
    have : deletionCount v = 132 := by omega
    exact hn ⟨v, this, by omega⟩
  have hsum : (∑ v : Fin 42, deletionCount v) ≤ 42 * 131 := by
    calc
      (∑ v : Fin 42, deletionCount v) ≤ ∑ _v : Fin 42, 131 := Finset.sum_le_sum fun v _ => hlt v
      _ = 42 * 131 := by simp
  rw [hcount] at hsum
  omega

#print axioms edge_count_le_138
#print axioms extremal_vertex_degree_six

end C4Extremal42
