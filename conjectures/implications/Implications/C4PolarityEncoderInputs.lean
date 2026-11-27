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

/-- The diagonal score segment has the eight absolute entries in ascending
point index. -/
theorem absoluteIndices_length : absoluteIndices.length = 8 := by
  classical
  have h := List.toFinset_card_of_nodup
    ((List.nodup_finRange 57).filter fun i : Fin 57 => decide (orthogonal i i))
  have hlen : absoluteIndices.length = absolute.card := by
    simpa [absoluteIndices, absolute] using h.symm
  rw [absolute_card] at hlen
  exact hlen

/-- The second score segment contains one entry for each of the 224 graph edges. -/
theorem orthogonalPairs_length : orthogonalPairs.length = 224 := by
  classical
  have h := orthogonal_pair_score_count (Finset.univ : Finset (Fin 57))
  have hlen : orthogonalPairs.length = graph.edgeFinset.card := by
    simpa [List.countP_eq_length_filter, inducedEdgeCount] using h
  rw [C4PolarityOrderSeven.edge_card] at hlen
  exact hlen

/-- The score list has the same 232 inputs as the Python script: eight absolute
indicators followed by 224 lexicographically ordered edge indicators. -/
theorem scoreInputs_length (D : Finset (Fin 57)) : (scoreInputs D).length = 232 := by
  simp [scoreInputs, absoluteIndices_length, orthogonalPairs_length]

/-- The Boolean score list has exactly the deletion score used in the edge
count reduction: induced deleted edges plus deleted absolute points. -/
theorem scoreInputs_count_true (D : Finset (Fin 57)) :
    (scoreInputs D).countP id = inducedEdgeCount graph D + (D ∩ absolute).card := by
  rw [scoreInputs, List.countP_append]
  change (absoluteIndices.map (fun i => decide (i ∈ D))).countP id +
    (orthogonalPairs.map (fun p => decide (p.1 ∈ D ∧ p.2 ∈ D))).countP id = _
  rw [absolute_score_count, orthogonal_pair_score_count]
  omega


/-- The neighbor subsets used for the survivor clauses. A subset of size
`degree(i) - 5` is exactly one of the combinations emitted by Python. -/
def neighborExcesses (i : Fin 57) : Finset (Finset (Fin 57)) :=
  Finset.powersetCard (graph.degree i - 5) (graph.neighborFinset i)

/-- One clause emitted for vertex `i` and a selected neighbor subset. -/
noncomputable def neighborSurvivorClause (D : Finset (Fin 57)) (i : Fin 57)
    (S : Finset (Fin 57)) : List Bool :=
  decide (i ∈ D) :: S.toList.map (fun j => !(decide (j ∈ D)))

private theorem survivor_neighbor_subset_exists (D N S : Finset (Fin 57))
    (hSN : S ⊆ N) (hS : S.card = N.card - 5)
    (hSurvive : 6 ≤ (N \ D).card) : ∃ j ∈ S, j ∉ D := by
  by_contra hn
  have hSD : S ⊆ D := by
    intro j hj
    by_contra hnot
    exact hn ⟨j, hj, hnot⟩
  have hdisj : Disjoint S (N \ D) := by
    apply Finset.disjoint_left.mpr
    intro j hj hjs
    exact (Finset.mem_sdiff.mp hjs).2 (hSD hj)
  have hunion : S ∪ (N \ D) ⊆ N := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjS | hjN
    · exact hSN hjS
    · exact (Finset.mem_sdiff.mp hjN).1
  have hcard : S.card + (N \ D).card ≤ N.card := by
    calc
      _ = (S ∪ (N \ D)).card := by rw [Finset.card_union_of_disjoint hdisj]
      _ ≤ N.card := Finset.card_le_card hunion
  have hNfive : 5 ≤ N.card := by omega
  omega

/-- If the undeleted part of every vertex neighborhood has size at least six,
all neighbor-survivor clauses emitted by the encoder are true. -/
theorem neighbor_survivor_clauses_of_min_degree (D : Finset (Fin 57))
    (hmin : ∀ i, i ∉ D → 6 ≤ (graph.neighborFinset i \ D).card) :
    ∀ i, ∀ S ∈ neighborExcesses i,
      Implications.C4PolarityCnfGates.clauseSat (neighborSurvivorClause D i S) = true := by
  classical
  intro i S hS
  by_cases hi : i ∈ D
  · simp [neighborSurvivorClause, Implications.C4PolarityCnfGates.clauseSat, hi]
  · have hsubset := (Finset.mem_powersetCard.mp hS).1
    have hcard := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨j, hjS, hjD⟩ := survivor_neighbor_subset_exists D
      (graph.neighborFinset i) S hsubset hcard (hmin i hi)
    apply List.any_eq_true.mpr
    refine ⟨true, ?_, rfl⟩
    rw [neighborSurvivorClause, List.mem_cons]
    right
    rw [List.mem_map]
    exact ⟨j, Finset.mem_toList.mpr hjS, by simp [hjD]⟩

/-- The canonical candidate score condition together with minimum degree six
on the retained graph implies every one of the encoder's neighbor clauses. -/
theorem candidate_neighbor_survivor_clauses (D : Finset (Fin 57))
    (_hCand : C4PolarityCanonical.Candidate D)
    (hmin : ∀ i, i ∉ D → 6 ≤ (graph.neighborFinset i \ D).card) :
    ∀ i, ∀ S ∈ neighborExcesses i,
      Implications.C4PolarityCnfGates.clauseSat (neighborSurvivorClause D i S) = true :=
  neighbor_survivor_clauses_of_min_degree D hmin

end Implications.C4PolarityEncoderInputs

#print axioms Implications.C4PolarityEncoderInputs.scoreInputs_count_true
#print axioms Implications.C4PolarityEncoderInputs.neighbor_survivor_clauses_of_min_degree
#print axioms Implications.C4PolarityEncoderInputs.candidate_neighbor_survivor_clauses
