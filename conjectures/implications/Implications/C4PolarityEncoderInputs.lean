import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4PolarityCanonical
import Implications.C4PolarityCnfGates
import Implications.C4PolarityDeletion
import Implications.C4DegreeBounds

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! Exact Boolean inputs emitted by `scripts/encode_c4_polarity_42_cnf.py`. -/

namespace Implications.C4PolarityEncoderInputs

open C4PolarityOrderSeven Implications.C4PolarityDeletion

/-- The absolute point indices, in the ascending order used by Python's
`range(57)` scan. -/
def absoluteIndices : List (Fin 57) :=
  (List.finRange 57).filter fun i => decide (orthogonal i i)

/-- Orthogonal pairs with `i < j`, nested first by `i` then by `j`, exactly
as `itertools.combinations(range(57), 2)` enumerates them. -/
def orthogonalPairs : List ((Fin 57) × (Fin 57)) :=
  (List.finRange 57).flatMap fun i =>
    ((List.finRange 57).filter fun j => decide (i < j ∧ orthogonal i j)).map
      fun j => (i, j)

/-- The score inputs: selected absolute points first, then conjunction
indicators for every orthogonal pair in the script's lexicographic order. -/
def scoreInputs (D : Finset (Fin 57)) : List Bool :=
  absoluteIndices.map (fun i => decide (i ∈ D)) ++
    orthogonalPairs.map (fun p => decide (p.1 ∈ D ∧ p.2 ∈ D))

private def orthogonalPairFinset : Finset ((Fin 57) × (Fin 57)) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ orthogonal p.1 p.2

private theorem orthogonalPairs_nodup : orthogonalPairs.Nodup := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  decide

private theorem orthogonalPairs_toFinset : orthogonalPairs.toFinset = orthogonalPairFinset := by
  ext p
  rcases p with ⟨i, j⟩
  simp [orthogonalPairs, orthogonalPairFinset, List.mem_flatMap]

private theorem countP_map_indicator {α : Type*} (l : List α) (P : α → Prop)
    [DecidablePred P] :
    (l.map fun x => decide (P x)).countP id =
      (l.filter fun x => decide (P x)).length := by
  rw [List.countP_map]
  change List.countP (fun x => decide (P x)) l = _
  rw [List.countP_eq_length_filter]

/-- The pair indicators count exactly the edges induced by the deletion set. -/
theorem orthogonal_pair_score_count (D : Finset (Fin 57)) :
    (orthogonalPairs.map (fun p => decide (p.1 ∈ D ∧ p.2 ∈ D))).countP id =
      inducedEdgeCount graph D := by
  classical
  rw [List.countP_map]
  change List.countP (fun p : Fin 57 × Fin 57 => decide (p.1 ∈ D ∧ p.2 ∈ D))
    orthogonalPairs = _
  rw [List.countP_eq_length_filter]
  have hnodup := orthogonalPairs_nodup.filter
    (fun p : Fin 57 × Fin 57 => decide (p.1 ∈ D ∧ p.2 ∈ D))
  rw [← List.toFinset_card_of_nodup hnodup]
  rw [List.toFinset_filter, orthogonalPairs_toFinset]
  let H := graph.induce (D : Set (Fin 57))
  let T := orthogonalPairFinset.filter fun p => p.1 ∈ D ∧ p.2 ∈ D
  change T.card = H.edgeFinset.card
  apply Finset.card_bij (s := T) (t := H.edgeFinset)
    (fun p hp => Sym2.mk ⟨p.1, (Finset.mem_filter.mp hp).2.1⟩
      ⟨p.2, (Finset.mem_filter.mp hp).2.2⟩) ?_ ?_ ?_
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    have horth := (Finset.mem_filter.mp hp').2.2
    change Sym2.mk _ _ ∈ H.edgeFinset
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.induce_adj).2 ⟨ne_of_lt (Finset.mem_filter.mp hp').2.1, horth⟩
  · intro p hp q hq heq
    simp only [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · exact Prod.ext (Subtype.ext_iff.mp heq.1) (Subtype.ext_iff.mp heq.2)
    · have hp12 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hq12 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
      have heq1 : p.1 = q.2 := Subtype.ext_iff.mp heq.1
      have heq2 : p.2 = q.1 := Subtype.ext_iff.mp heq.2
      have hrev : p.2 < p.1 := by
        rw [← heq2, ← heq1] at hq12
        exact hq12
      omega
  · intro e he
    obtain ⟨ab, habeq⟩ := Sym2.mk_surjective e
    rcases ab with ⟨a, b⟩
    have hab : H.Adj a b := by
      rw [← habeq] at he
      have heEdge := SimpleGraph.mem_edgeFinset.mp he
      exact (SimpleGraph.mem_edgeSet H).mp heEdge
    have hne : a.val ≠ b.val := (SimpleGraph.induce_adj.mp hab).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨(a.val, b.val), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ⟨a.property, b.property⟩⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hlt, (SimpleGraph.induce_adj.mp hab).2⟩
      · change Sym2.mk a b = e
        exact habeq
    · have hba : graph.Adj b.val a.val := graph.symm.symm a.val b.val (SimpleGraph.induce_adj.mp hab)
      refine ⟨(b.val, a.val), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ⟨b.property, a.property⟩⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hgt, hba.2⟩
      · change Sym2.mk b a = e
        calc
          Sym2.mk b a = Sym2.mk a b := by
            apply Sym2.eq_iff.mpr
            exact Or.inr ⟨rfl, rfl⟩
          _ = e := by simpa using habeq

/-- The absolute-point indicators count the deleted absolute points. -/
theorem absolute_score_count (D : Finset (Fin 57)) :
    (absoluteIndices.map fun i => decide (i ∈ D)).countP id =
      (D ∩ absolute).card := by
  classical
  rw [countP_map_indicator]
  have hnodup := (List.nodup_finRange 57).filter
    (fun i : Fin 57 => decide (orthogonal i i))
  have hnodupD := hnodup.filter (fun i => decide (i ∈ D))
  have hlen : (absoluteIndices.filter fun i => decide (i ∈ D)).length =
      (absoluteIndices.filter fun i => decide (i ∈ D)).toFinset.card :=
    (List.toFinset_card_of_nodup hnodupD).symm
  have hfset : (absoluteIndices.filter fun i => decide (i ∈ D)).toFinset =
      D ∩ absolute := by
    ext i
    simp [absoluteIndices, absolute, List.toFinset_filter, List.toFinset_finRange]
  rw [hlen, hfset]

/-- The Boolean score list has exactly the deletion score used in the edge
count reduction: induced deleted edges plus deleted absolute points. -/
theorem scoreInputs_count_true (D : Finset (Fin 57)) :
    (scoreInputs D).countP id = inducedEdgeCount graph D + (D ∩ absolute).card := by
  rw [scoreInputs, List.countP_append]
  change (absoluteIndices.map (fun i => decide (i ∈ D))).countP id +
    (orthogonalPairs.map (fun p => decide (p.1 ∈ D ∧ p.2 ∈ D))).countP id = _
  rw [absolute_score_count, orthogonal_pair_score_count]
  omega

end Implications.C4PolarityEncoderInputs

#print axioms Implications.C4PolarityEncoderInputs.scoreInputs_count_true
