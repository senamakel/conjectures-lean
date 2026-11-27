import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4PolarityCanonical
import Implications.C4PolarityCnfGates
import Implications.C4PolarityEdgeEncoding
import Implications.C4PolarityDeletion

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
  decide

/-- The score list has the same 232 inputs as the Python script: eight absolute
indicators followed by 224 lexicographically ordered edge indicators. -/
theorem scoreInputs_length (D : Finset (Fin 57)) : (scoreInputs D).length = 232 := by
  simp [scoreInputs, absoluteIndices_length, orthogonalPairs_length]

/-- The lexicographic pair sequence follows the nested `i`, then `j`, scan
used by `itertools.combinations`. -/
theorem orthogonalPairs_lex_ordered :
    orthogonalPairs.Pairwise (fun p q => p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2) := by
  decide

/-- The Boolean score list has exactly the deletion score used in the edge
count reduction: induced deleted edges plus deleted absolute points. -/
theorem scoreInputs_count_true (D : Finset (Fin 57)) :
    (scoreInputs D).countP id = inducedEdgeCount graph D + (D ∩ absolute).card := by
  rw [scoreInputs, List.countP_append]
  rw [absolute_score_count, orthogonal_pair_score_count]
  omega


/-- The neighbor subsets used for the survivor clauses. A subset of size
`degree(i) - 5` is exactly one of the combinations emitted by Python. -/
def neighborExcesses (i : Fin 57) : Finset (Finset (Fin 57)) :=
  Finset.powersetCard (graph.degree i - 5) (graph.neighborFinset i)

/-- One clause emitted for vertex `i` and a selected neighbor subset. -/
noncomputable def neighborSurvivorClause (D : Finset (Fin 57)) (i : Fin 57)
    (S : Finset (Fin 57)) : List Bool :=
  decide (i ∈ D) :: (S.sort (· ≤ ·)).map (fun j => !(decide (j ∈ D)))

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
    exact ⟨j, by simpa using hjS, by simp [hjD]⟩

/-- A canonical candidate's Boolean score clears the threshold 34 in the
script, using the exact deleted-edge score identity. -/
theorem candidate_score_at_least_34 (D : Finset (Fin 57))
    (hCand : C4PolarityCanonical.Candidate D) :
    34 ≤ (scoreInputs D).countP id := by
  rw [scoreInputs_count_true]
  have hret := C4PolarityOrderSeven.retained_edge_count D hCand.1
  have hLower := hCand.2
  rw [hret] at hLower
  omega

/-- The 41-vertex edge bound is formulated using set cardinality so it is
independent of the enumeration used for each successive induced graph. -/
def SurvivorDeletionBound (D : Finset (Fin 57)) : Prop :=
  ∀ v : {i // i ∈ (Finset.univ : Finset (Fin 57)) \ D},
    ((graph.induce ((Finset.univ \ D : Finset (Fin 57)) : Set (Fin 57))).induce
      ({v}ᶜ : Set {i // i ∈ (Finset.univ : Finset (Fin 57)) \ D})).edgeSet.ncard ≤ 132

theorem candidate_survivor_min_degree (D : Finset (Fin 57))
    (hCand : C4PolarityCanonical.Candidate D) (hDel : SurvivorDeletionBound D) :
    ∀ i, i ∉ D → 6 ≤ (graph.neighborFinset i \ D).card := by
  classical
  let R : Finset (Fin 57) := Finset.univ \ D
  let H := graph.induce (R : Set (Fin 57))
  have hEdgeN : 138 ≤ H.edgeSet.ncard := by
    simpa only [H, R, inducedEdgeCount, SimpleGraph.edgeFinset_card,
      Set.fintypeCard_eq_ncard] using hCand.2
  have hEdge : 138 ≤ H.edgeFinset.card := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hEdgeN
  intro i hi
  have hiR : i ∈ R := by simp [R, hi]
  let v : R := ⟨i, hiR⟩
  have hDelCount : (H.induce ({v}ᶜ : Set R)).edgeFinset.card ≤ 132 := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hDel v
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet] at hDelCount
  have hdegree : 6 ≤ H.degree v := by omega
  have hneighbors : (H.neighborFinset v).card = (graph.neighborFinset i \ D).card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      have hadj := (H.mem_neighborFinset v x).mp hx
      have hxD : x.val ∉ D := (Finset.mem_sdiff.mp x.property).2
      exact Finset.mem_sdiff.mpr ⟨(graph.mem_neighborFinset i x.val).mpr hadj, hxD⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      obtain ⟨hxN, hxD⟩ := Finset.mem_sdiff.mp hx
      refine ⟨⟨x, by simp [R, hxD]⟩, ?_, rfl⟩
      exact (H.mem_neighborFinset v _).mpr ((graph.mem_neighborFinset i x).mp hxN)
  rw [← hneighbors, H.card_neighborFinset_eq_degree]
  exact hdegree

open C4PolarityEdgeEncoding C4PolarityDimacs

/-- The signed DIMACS clause corresponding to one survivor constraint. -/
noncomputable def neighborDimacsClause (i : Fin 57) (S : Finset (Fin 57)) : List Int :=
  (deletionId i : Int) :: (S.sort (· ≤ ·)).map (fun j => -(deletionId j : Int))

theorem neighborDimacsClause_satisfied (D : Finset (Fin 57))
    (hmin : ∀ i, i ∉ D → 6 ≤ (graph.neighborFinset i \ D).card)
    (a : Nat → Bool) (ha : ∀ j : Fin 57, a (deletionId j) = decide (j ∈ D))
    (i : Fin 57) (S : Finset (Fin 57)) (hS : S ∈ neighborExcesses i) :
    (neighborDimacsClause i S).any (evalLiteral a) = true := by
  have hpos (j : Fin 57) :
      evalLiteral a (deletionId j : Int) = decide (j ∈ D) := by
    have hd : 0 < deletionId j := by unfold deletionId; omega
    simp [evalLiteral, hd, ha]
  have hneg (j : Fin 57) :
      evalLiteral a (-(deletionId j : Int)) = !(decide (j ∈ D)) := by
    have hd : ¬ (deletionId j : Int) < 0 := by omega
    simp [evalLiteral, hd, ha]
  have hmap : (neighborDimacsClause i S).map (evalLiteral a) = neighborSurvivorClause D i S := by
    simp [neighborDimacsClause, neighborSurvivorClause, hpos, hneg, List.map_map,
      Function.comp_def]
  have hsat := neighbor_survivor_clauses_of_min_degree D hmin i S hS
  rw [C4PolarityCnfGates.clauseSat, ← hmap, List.any_map] at hsat
  exact hsat

/-- The signed input literals passed to the score counter are the deletion
bits of the absolute points, followed by all edge output variables. -/
def scoreDimacsInputs : List Int :=
  absoluteIndices.map (fun i => (deletionId i : Int)) ++
    List.ofFn (fun k : Fin orthogonalPairs.length => (edgeId k.val : Int))

theorem scoreDimacsInputs_eval (D : Finset (Fin 57)) (base : Nat → Bool)
    (hbase : ∀ i : Fin 57, base (deletionId i) = decide (i ∈ D)) :
    scoreDimacsInputs.map (evalLiteral (extendEdges base orthogonalPairs)) = scoreInputs D := by
  have hpos (n : Nat) (hn : 0 < n) :
      evalLiteral (extendEdges base orthogonalPairs) (n : Int) =
        extendEdges base orthogonalPairs n := by
    simp [evalLiteral, hn]
  have hd (i : Fin 57) : 0 < deletionId i := by unfold deletionId; omega
  have he (k : Nat) : 0 < edgeId k := by unfold edgeId; omega
  simp only [scoreDimacsInputs, scoreInputs, List.map_append, List.map_map, List.map_ofFn]
  congr 1
  · apply List.map_congr_left
    intro i _
    rw [Function.comp_apply, hpos _ (hd i), extendEdges_at_deletion, hbase]
  · rw [← List.ofFn_getElem_eq_map]
    congr 1
    funext k
    simp only [Function.comp_apply, hpos _ (he k.val), extendEdges_at_edge _ _ _ k.isLt,
      hbase, Bool.decide_and]

end Implications.C4PolarityEncoderInputs

#print axioms Implications.C4PolarityEncoderInputs.orthogonal_pair_score_count
#print axioms Implications.C4PolarityEncoderInputs.absolute_score_count
#print axioms Implications.C4PolarityEncoderInputs.scoreInputs_count_true
#print axioms Implications.C4PolarityEncoderInputs.scoreInputs_length
#print axioms Implications.C4PolarityEncoderInputs.neighbor_survivor_clauses_of_min_degree
#print axioms Implications.C4PolarityEncoderInputs.candidate_score_at_least_34
#print axioms Implications.C4PolarityEncoderInputs.orthogonalPairs_lex_ordered
#print axioms Implications.C4PolarityEncoderInputs.candidate_survivor_min_degree
#print axioms Implications.C4PolarityEncoderInputs.neighborDimacsClause_satisfied
#print axioms Implications.C4PolarityEncoderInputs.scoreDimacsInputs_eval
