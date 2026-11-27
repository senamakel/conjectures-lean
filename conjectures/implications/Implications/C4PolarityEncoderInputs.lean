import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4PolarityCanonical
import Implications.C4PolarityCnfGates
import Implications.C4PolarityDeletion
import Implications.C4DegreeBounds

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
  rfl

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
    have hadj := (Finset.mem_filter.mp hp').2.2
    change Sym2.mk _ _ ∈ H.edgeFinset
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (SimpleGraph.induce_adj).2 hadj
  · intro p hp q hq heq
    simp only [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · exact Prod.ext (Subtype.ext_iff.mp heq.1) (Subtype.ext_iff.mp heq.2)
    · have hlt1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hlt2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
      have hrev : p.2 < p.1 := by simpa using hlt2
      omega
  · intro e he
    have he' := (SimpleGraph.mem_edgeFinset.mp he)
    obtain ⟨a, b, rfl⟩ := Sym2.mk_surjective e
    have hab : H.Adj a b := by simpa [H] using (SimpleGraph.mem_edgeSet.mp he')
    have hne : a.val ≠ b.val := by
      intro h
      apply H.loopless.irrefl a
      simpa [h] using hab
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨(a.val, b.val), ?_, ?_⟩
      · simp [T, orthogonalPairFinset, Finset.mem_filter, hlt, H] at *
        exact ⟨⟨hlt, (SimpleGraph.induce_adj.mp hab)⟩, ⟨a.property, b.property⟩⟩
      · simp [H, SimpleGraph.induce_adj]
    · refine ⟨(b.val, a.val), ?_, ?_⟩
      · have hba : graph.Adj b.val a.val := graph.symm b.val a.val (SimpleGraph.induce_adj.mp hab)
        simp [T, orthogonalPairFinset, Finset.mem_filter, hgt, H] at *
        exact ⟨⟨hgt, hba.2⟩, ⟨b.property, a.property⟩⟩
      · simp [H, Sym2.eq_iff, SimpleGraph.induce_adj, graph.symm]

/-- The absolute-point indicators count the deleted absolute points. -/
theorem absolute_score_count (D : Finset (Fin 57)) :
    (absoluteIndices.map fun i => decide (i ∈ D)).countP id =
      (D ∩ absolute).card := by
  classical
  rw [countP_map_indicator]
  have hnodup := (List.nodup_finRange 57).filter
    (fun i : Fin 57 => decide (orthogonal i i))
  have hfset : (absoluteIndices.filter fun i => decide (i ∈ D)).toFinset =
      D ∩ absolute := by
    ext i
    simp [absoluteIndices, absolute, List.toFinset_filter, List.toFinset_finRange]
  rw [← List.toFinset_card_of_nodup (hnodup.filter fun i => decide (i ∈ D)), hfset]

/-- The Boolean score list has exactly the deletion score used in the edge
count reduction: induced deleted edges plus deleted absolute points. -/
theorem scoreInputs_count_true (D : Finset (Fin 57)) :
    (scoreInputs D).countP id = inducedEdgeCount graph D + (D ∩ absolute).card := by
  rw [scoreInputs, List.countP_append, List.countP_map]
  rw [absolute_score_count, orthogonal_pair_score_count]

end Implications.C4PolarityEncoderInputs

#print axioms Implications.C4PolarityEncoderInputs.scoreInputs_count_true
