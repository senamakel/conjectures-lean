import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4VertexExtension
import Implications.C4PolarityDeletion

/-! The order-seven polarity graph in the vertex order of the DIMACS encoder. -/

namespace C4PolarityOrderSeven

/-- The normalized representatives are `(1,a,b)`, then `(0,1,a)`, then
`(0,0,1)`. Within the first group the third coordinate changes fastest. -/
def point (i : Fin 57) : ℕ × ℕ × ℕ :=
  if i.val < 49 then (1, i.val / 7, i.val % 7)
  else if i.val < 56 then (0, 1, i.val - 49)
  else (0, 0, 1)

/-- Orthogonality for the symmetric dot product over `GF(7)`. -/
def orthogonal (i j : Fin 57) : Prop :=
  let a := point i
  let b := point j
  (a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2) % 7 = 0

instance instDecidableOrthogonal : DecidableRel orthogonal := fun i j => by
  unfold orthogonal
  infer_instance

/-- Distinct orthogonal projective points are adjacent. -/
def graph : SimpleGraph (Fin 57) where
  Adj i j := i ≠ j ∧ orthogonal i j
  symm := by
    constructor
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    simpa only [orthogonal, Nat.mul_comm] using h.2
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

instance instDecidableAdj : DecidableRel graph.Adj := fun i j => by
  change Decidable (i ≠ j ∧ orthogonal i j)
  infer_instance

/-- The absolute points are those orthogonal to themselves. -/
def absolute : Finset (Fin 57) := Finset.univ.filter (fun i => orthogonal i i)

theorem absolute_card : absolute.card = 8 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem degree_profile (i : Fin 57) :
    graph.degree i = if i ∈ absolute then 7 else 8 := by
  revert i
  decide

theorem edge_card : graph.edgeFinset.card = 224 := by
  have hsum : (∑ i : Fin 57, graph.degree i) = 448 := by
    simp_rw [degree_profile]
    have hcounts : (∑ i : Fin 57, if i ∈ absolute then 7 else 8) = 448 := by
      decide
    exact hcounts
  rw [graph.sum_degrees_eq_twice_card_edges] at hsum
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem common_neighbor_card_le_one :
    ∀ i j : Fin 57, i ≠ j →
      (graph.neighborFinset i ∩ graph.neighborFinset j).card ≤ 1 := by
  decide

theorem c4_free : C4VertexExtension.C4Free graph := by
  intro i j x y hij hxy hix hjx h
  have hx : x ∈ graph.neighborFinset i ∩ graph.neighborFinset j :=
    Finset.mem_inter.mpr ⟨(graph.mem_neighborFinset i x).mpr hix,
      (graph.mem_neighborFinset j x).mpr hjx⟩
  have hy : y ∈ graph.neighborFinset i ∩ graph.neighborFinset j :=
    Finset.mem_inter.mpr ⟨(graph.mem_neighborFinset i y).mpr h.1,
      (graph.mem_neighborFinset j y).mpr h.2⟩
  exact hxy ((Finset.card_le_one.mp (common_neighbor_card_le_one i j hij)) x hx y hy)

/-- The score used in the SAT encoding reflects the exact edge count after
deleting fifteen vertices from the concrete projective graph. -/
theorem retained_edge_count (D : Finset (Fin 57)) (hD : D.card = 15) :
    Implications.C4PolarityDeletion.inducedEdgeCount graph (Finset.univ \ D) =
      104 + Implications.C4PolarityDeletion.inducedEdgeCount graph D +
        (D ∩ absolute).card := by
  exact Implications.C4PolarityDeletion.retained_edge_count_eq_104_add_deleted_score
    graph absolute D ⟨by decide, absolute_card, edge_card, degree_profile⟩ hD

#print axioms retained_edge_count
#print axioms absolute_card
#print axioms degree_profile
#print axioms edge_card
#print axioms c4_free

end C4PolarityOrderSeven
