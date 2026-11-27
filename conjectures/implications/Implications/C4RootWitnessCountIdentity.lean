import Implications.C4DegreeEightPairWitnesses
import Mathlib.Tactic

namespace C4RootWitnessCountIdentity

open C4DegreeEightCap C4DegreeEightEquality C4DegreeEightMultiplicity

/-- For a non-root vertex, the four degree-eight roots are witnessed by
neighbors in the root union. Shared witnesses count twice and private ones
once. -/
theorem four_root_witness_weighted_count
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {x : Fin 42}
    (hx : x ∉ Finset.univ.filter fun v => G.degree v = 8) :
    let D := Finset.univ.filter fun v => G.degree v = 8
    let U := D.biUnion fun u => G.neighborFinset u
    let m := fun y => (G.neighborFinset y ∩ D).card
    let S := U.filter fun y => m y = 2
    let P := U.filter fun y => m y = 1
    2 * (G.neighborFinset x ∩ S).card + (G.neighborFinset x ∩ P).card = 4 := by
  classical
  dsimp only
  let D := Finset.univ.filter fun v : Fin 42 => G.degree v = 8
  let U := D.biUnion fun u => G.neighborFinset u
  let m := fun y : Fin 42 => (G.neighborFinset y ∩ D).card
  let S := U.filter fun y => m y = 2
  let P := U.filter fun y => m y = 1
  let W := G.neighborFinset x ∩ U
  let T := fun y : Fin 42 => G.neighborFinset y ∩ D
  have hxD : x ∉ D := by simpa [D] using hx
  have hDcard : D.card = 4 := by simpa [D] using h8
  have hwindow := C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4
  have hUroot (y : Fin 42) (hy : y ∈ U) : G.degree y ≠ 8 := by
    intro hy8
    rcases Finset.mem_biUnion.mp hy with ⟨u, huD, hyu⟩
    have hu8 := (Finset.mem_filter.mp huD).2
    have hyuAdj : G.Adj u y := (G.mem_neighborFinset u y).mp hyu
    have hyu' : u ∈ G.neighborFinset y :=
      (G.mem_neighborFinset y u).mpr (G.symm.symm u y hyuAdj)
    have hbound := C4DegreeBounds.neighbor_degree_le_seven_of_degree_eight
      G y (by simp) (fun z => (hwindow z).1) hC4 hy8 hyu'
    omega
  have hmultPos (y : Fin 42) (hy : y ∈ U) : 0 < m y := by
    rcases Finset.mem_biUnion.mp hy with ⟨u, huD, hyu⟩
    have hyuAdj : G.Adj u y := (G.mem_neighborFinset u y).mp hyu
    have huy : u ∈ G.neighborFinset y :=
      (G.mem_neighborFinset y u).mpr (G.symm.symm u y hyuAdj)
    apply Finset.card_pos.mpr
    exact ⟨u, Finset.mem_inter.mpr ⟨huy, huD⟩⟩
  have hmultLe (y : Fin 42) (hy : y ∈ U) : m y ≤ 2 := by
    have hyNot8 := hUroot y hy
    have hymin := (hwindow y).1
    have hymax := (hwindow y).2
    have hydeg : G.degree y = 6 ∨ G.degree y = 7 := by omega
    rcases hydeg with hy6 | hy7
    · exact degree_six_vertex_has_at_most_two_degree_eight_neighbors
        G hDel he hC4 h8 hy6
    · have hle := degree_seven_vertex_has_at_most_one_degree_eight_neighbor
        G hDel he hC4 h8 hy7
      change m y ≤ 1 at hle
      omega
  have hmultCases (y : Fin 42) (hy : y ∈ U) : m y = 1 ∨ m y = 2 := by
    have hpos := hmultPos y hy
    have hle := hmultLe y hy
    omega
  have hTcard (y : Fin 42) : (T y).card = m y := rfl
  have hTdisjoint : (W : Set (Fin 42)).PairwiseDisjoint T := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro u huy huz
    have hyx : G.Adj x y := (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).1
    have hzx : G.Adj x z := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz).1
    have hyu : G.Adj y u := (G.mem_neighborFinset y u).mp (Finset.mem_inter.mp huy).1
    have hzu : G.Adj z u := (G.mem_neighborFinset z u).mp (Finset.mem_inter.mp huz).1
    have huD := (Finset.mem_inter.mp huy).2
    have hxu : x ≠ u := by
      intro heq
      subst u
      exact hxD huD
    apply hC4 hxu hyz hyx hyu.symm
    exact ⟨hzx, hzu.symm⟩
  have hbiUnion : W.biUnion T = D := by
    ext u
    constructor
    · intro hu
      rcases Finset.mem_biUnion.mp hu with ⟨y, hyW, huy⟩
      exact (Finset.mem_inter.mp huy).2
    · intro huD
      have hu8 := (Finset.mem_filter.mp huD).2
      have hcommon : (G.neighborFinset u ∩ G.neighborFinset x).card = 1 :=
        extremal_degree_eight_vertices_have_unique_common_neighbor G hDel he hC4 h8
          u huD x (by intro heq; subst x; exact hxD huD)
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hcommon]; norm_num)
      have hyu : y ∈ G.neighborFinset u := (Finset.mem_inter.mp hy).1
      have hyx : y ∈ G.neighborFinset x := (Finset.mem_inter.mp hy).2
      have hyuAdj : G.Adj u y := (G.mem_neighborFinset u y).mp hyu
      have hyU : y ∈ U := Finset.mem_biUnion.mpr ⟨u, huD, hyu⟩
      have huY : u ∈ G.neighborFinset y :=
        (G.mem_neighborFinset y u).mpr (G.symm.symm u y hyuAdj)
      have huT : u ∈ T y := Finset.mem_inter.mpr ⟨huY, huD⟩
      exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_inter.mpr ⟨hyx, hyU⟩, huT⟩
  have hsum : (∑ y ∈ W, m y) = 4 := by
    calc
      _ = ∑ y ∈ W, (T y).card := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (hTcard y).symm
      _ = (W.biUnion T).card := (Finset.card_biUnion hTdisjoint).symm
      _ = D.card := by rw [hbiUnion]
      _ = 4 := hDcard
  have hsplit : (∑ y ∈ W, m y) =
      2 * (W ∩ S).card + (W ∩ P).card := by
    have hWsplit : W = (W ∩ S) ∪ (W ∩ P) := by
      ext y
      constructor
      · intro hy
        have hyU := (Finset.mem_inter.mp hy).2
        rcases hmultCases y hyU with hm | hm
        · exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_inter.mpr ⟨hy, Finset.mem_filter.mpr ⟨hyU, hm⟩⟩))
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_inter.mpr ⟨hy, Finset.mem_filter.mpr ⟨hyU, hm⟩⟩))
      · intro hy
        rcases Finset.mem_union.mp hy with hyS | hyP
        · exact (Finset.mem_inter.mp hyS).1
        · exact (Finset.mem_inter.mp hyP).1
    have hWdisjoint : Disjoint (W ∩ S) (W ∩ P) := by
      apply Finset.disjoint_left.mpr
      intro y hyS hyP
      have htwo := (Finset.mem_filter.mp (Finset.mem_inter.mp hyS).2).2
      have hone := (Finset.mem_filter.mp (Finset.mem_inter.mp hyP).2).2
      omega
    calc
      _ = ∑ y ∈ (W ∩ S) ∪ (W ∩ P), m y :=
        congrArg (fun t => ∑ y ∈ t, m y) hWsplit
      _ = (∑ y ∈ W ∩ S, m y) + ∑ y ∈ W ∩ P, m y :=
        Finset.sum_union hWdisjoint
      _ = 2 * (W ∩ S).card + (W ∩ P).card := by
        have hsumS : (∑ y ∈ W ∩ S, m y) = 2 * (W ∩ S).card := by
          calc
            _ = ∑ y ∈ W ∩ S, (2 : ℕ) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
            _ = 2 * (W ∩ S).card := by simp [Nat.mul_comm]
        have hsumP : (∑ y ∈ W ∩ P, m y) = (W ∩ P).card := by
          calc
            _ = ∑ y ∈ W ∩ P, (1 : ℕ) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
            _ = (W ∩ P).card := by simp
        rw [hsumS, hsumP]
  have hWSp : W ∩ S = G.neighborFinset x ∩ S := by
    ext y
    simp [W, S]
  have hWPp : W ∩ P = G.neighborFinset x ∩ P := by
    ext y
    simp [W, P]
  rw [hsplit, hWSp, hWPp] at hsum
  exact hsum

end C4RootWitnessCountIdentity

#print axioms C4RootWitnessCountIdentity.four_root_witness_weighted_count

namespace C4RootWitnessCountIdentity

private theorem cross_neighbor_sum_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ x ∈ A, (G.neighborFinset x ∩ B).card) =
      ∑ x ∈ B, (G.neighborFinset x ∩ A).card := by
  classical
  have hfilter (x : V) (T : Finset V) :
      (G.neighborFinset x ∩ T).card = ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
    have hset : G.neighborFinset x ∩ T = T.filter (fun y => G.Adj x y) := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hset, Finset.card_filter]
  simp_rw [hfilter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp [G.adj_comm]

private theorem within_neighbor_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (∑ x ∈ A, (G.neighborFinset x ∩ A).card) =
      2 * Implications.C4PolarityDeletion.inducedEdgeCount G A := by
  classical
  change (∑ x ∈ A, (G.neighborFinset x ∩ A).card) =
    2 * (G.induce (A : Set V)).edgeFinset.card
  rw [← (G.induce (A : Set V)).sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_coe_sort A (fun x => (G.neighborFinset x ∩ A).card)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [SimpleGraph.degree]
  refine Finset.card_bij
    (fun y hy => (⟨y, (Finset.mem_inter.mp hy).2⟩ : {z : V // z ∈ A}))
    (fun y hy => by
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
      exact (SimpleGraph.mem_neighborFinset G x y).mp
        (Finset.mem_inter.mp hy).1)
    (fun _ _ _ _ h => congrArg Subtype.val h)
    (fun y hy => ⟨y.1, Finset.mem_inter.mpr
      ⟨(SimpleGraph.mem_neighborFinset G x y.1).mpr
        ((SimpleGraph.mem_neighborFinset _ x y).mp hy), y.2⟩, rfl⟩)

/-- The local incidence identities imply the global outer-edge count. This
form is independent of how the structural classes were constructed, so the
graph-specific lemmas can feed it directly. -/
theorem outer_edge_count_from_local_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S O : Finset V)
    (hOcard : O.card = 12)
    (hSlocal : ∀ x ∈ S,
      (G.neighborFinset x ∩ O).card = (G.neighborFinset x ∩ S).card)
    (hOlocal : ∀ x ∈ O,
      (G.neighborFinset x ∩ O).card = 3 + (G.neighborFinset x ∩ S).card) :
    Implications.C4PolarityDeletion.inducedEdgeCount G O =
      18 + Implications.C4PolarityDeletion.inducedEdgeCount G S := by
  have hcross := cross_neighbor_sum_comm G S O
  have hsumS : (∑ x ∈ S, (G.neighborFinset x ∩ O).card) =
      2 * Implications.C4PolarityDeletion.inducedEdgeCount G S := by
    calc
      _ = ∑ x ∈ S, (G.neighborFinset x ∩ S).card := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hSlocal x hx
      _ = 2 * Implications.C4PolarityDeletion.inducedEdgeCount G S :=
        within_neighbor_sum_eq G S
  have hsumO : (∑ x ∈ O, (G.neighborFinset x ∩ O).card) =
      36 + 2 * Implications.C4PolarityDeletion.inducedEdgeCount G S := by
    calc
      _ = ∑ x ∈ O, (3 + (G.neighborFinset x ∩ S).card) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hOlocal x hx
      _ = 3 * O.card + ∑ x ∈ O, (G.neighborFinset x ∩ S).card := by
        simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ = 36 + ∑ x ∈ S, (G.neighborFinset x ∩ O).card := by
        rw [hOcard, cross_neighbor_sum_comm]
        norm_num
      _ = 36 + 2 * Implications.C4PolarityDeletion.inducedEdgeCount G S := by
        rw [hsumS]
  have hfinal := within_neighbor_sum_eq G O
  rw [hsumO] at hfinal
  omega

#print axioms outer_edge_count_from_local_counts

end C4RootWitnessCountIdentity
