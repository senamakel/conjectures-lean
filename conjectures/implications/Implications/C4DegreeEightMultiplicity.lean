import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4DegreeEightEquality

/-!
# Multiplicity constraints in the four-degree-eight equality case

When the extremal graph has four vertices of degree eight, the degree-eight
neighborhoods have union size 26. Their 28 incidences with degree-six vertices
are distributed over all 22 degree-six vertices, with multiplicity at most
two. Thus exactly six degree-six vertices have multiplicity two and the other
sixteen have multiplicity one.
-/

namespace C4DegreeEightMultiplicity

open C4DegreeEightCap C4DegreeEightEquality

/-- The union of the degree-eight neighborhoods has exactly 26 vertices in
the extremal four-degree-eight case. -/
theorem degree_eight_neighborhood_union_card_eq_26
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4) :
    let D := Finset.univ.filter fun v => G.degree v = 8
    (D.biUnion fun u => G.neighborFinset u).card = 26 := by
  classical
  dsimp
  let D := Finset.univ.filter fun v : Fin 42 => G.degree v = 8
  let E := Finset.univ.filter fun v : Fin 42 => G.degree v = 7
  let N := fun u : Fin 42 => G.neighborFinset u
  let U := D.biUnion N
  have hmin : ∀ v, 6 ≤ G.degree v := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).1
  have hmax : ∀ v, G.degree v ≤ 8 := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).2
  have hDcard : D.card = 4 := by simpa [D] using h8
  have hEcard : E.card = 16 := by
    exact degree_seven_count_eq_sixteen G hmin hmax he (by simpa [D] using h8)
  have hUnionBound : 17 * D.card ≤ 2 * U.card + D.card ^ 2 := by
    have hbound := twice_union_card_add_square_bound D N
      (fun u hu => (Finset.mem_filter.mp hu).2) (by
        intro u hu v hv huv
        apply Finset.card_le_one.mpr
        intro x hx y hy
        by_contra hxy
        have hux := (G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hx).1
        have hvx := (G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).2
        have huy := (G.mem_neighborFinset u y).mp (Finset.mem_inter.mp hy).1
        have hvy := (G.mem_neighborFinset v y).mp (Finset.mem_inter.mp hy).2
        exact hC4 huv hxy hux hvx ⟨huy, hvy⟩)
    simpa [U] using hbound
  have hDavoid : Disjoint D U := by
    rw [Finset.disjoint_left]
    intro x hxD hxU
    rcases Finset.mem_biUnion.mp hxU with ⟨u, huD, hxu⟩
    have hu8 := (Finset.mem_filter.mp huD).2
    have hx8 := (Finset.mem_filter.mp hxD).2
    have hbound := C4DegreeBounds.neighbor_degree_le_seven_of_degree_eight
      G u (by simp) hmin hC4 hu8 hxu
    omega
  have hWbound : (E ∩ U).card ≤ D.card := by
    have hsub : E ∩ U ⊆ D.biUnion (fun u => G.neighborFinset u ∩ E) := by
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxE, hxU⟩
      rcases Finset.mem_biUnion.mp hxU with ⟨u, huD, hxu⟩
      exact Finset.mem_biUnion.mpr ⟨u, huD, Finset.mem_inter.mpr ⟨hxu, hxE⟩⟩
    calc
      (E ∩ U).card ≤ (D.biUnion fun u => G.neighborFinset u ∩ E).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ D, (G.neighborFinset u ∩ E).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ D, 1 := Finset.sum_le_sum fun u hu =>
        degree_seven_neighbors_card_le_one G hmin hC4 (Finset.mem_filter.mp hu).2
      _ = D.card := by simp
  have hEoutside : (E \ U).card + (E ∩ U).card = E.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : E ∩ U ⊆ E)
    rw [show E \ (E ∩ U) = E \ U by ext x; simp] at h
    exact h
  have houtside : D ∪ (E \ U) ⊆ Finset.univ \ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxD | hxE
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        intro hxU
        exact (Finset.disjoint_left.mp hDavoid) hxD hxU⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hxE).2⟩
  have hcap : D.card + (E \ U).card ≤ 42 - U.card := by
    calc
      _ = (D ∪ (E \ U)).card := by
        symm
        apply Finset.card_union_of_disjoint
        apply Finset.disjoint_left.mpr
        intro x hxD hxE
        have hx8 := (Finset.mem_filter.mp hxD).2
        have hx7 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hxE).1).2
        omega
      _ ≤ (Finset.univ \ U).card := Finset.card_le_card houtside
      _ = 42 - U.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]
        simp
  have hUlower : 26 ≤ U.card := by
    rw [hDcard] at hUnionBound
    norm_num at hUnionBound
    omega
  have hJlower : 12 ≤ (E \ U).card := by omega
  have hUupper : U.card ≤ 26 := by
    rw [hDcard] at hcap
    omega
  change U.card = 26
  omega

/-- Every pair of degree-eight vertices has exactly one common neighbor. -/
theorem degree_eight_pair_has_one_common_neighbor
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {u v : Fin 42} (hu : G.degree u = 8) (_hv : G.degree v = 8) (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 1 := by
  have hmem : u ∈ Finset.univ.filter (fun x => G.degree x = 8) := by simp [hu]
  exact extremal_degree_eight_vertices_have_unique_common_neighbor
    G hDel he hC4 h8 u hmem v huv.symm

/-- Each degree-eight vertex has exactly seven degree-six neighbors in the
four-vertex equality case. -/
theorem degree_eight_vertex_has_seven_degree_six_neighbors
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {u : Fin 42} (hu : G.degree u = 8) :
    (G.neighborFinset u ∩ Finset.univ.filter fun v => G.degree v = 6).card = 7 := by
  classical
  let N := G.neighborFinset u
  let A := Finset.univ.filter fun v : Fin 42 => G.degree v = 6
  let E := Finset.univ.filter fun v : Fin 42 => G.degree v = 7
  have hmin : ∀ v, 6 ≤ G.degree v := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).1
  have hmax : ∀ v, G.degree v ≤ 8 := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).2
  have hNcard : N.card = 8 := by
    simpa [N, G.card_neighborFinset_eq_degree] using hu
  have hseven : (N ∩ E).card = 1 := by
    exact each_degree_eight_vertex_has_one_degree_seven_neighbor G hDel he hC4 h8
      u (by simp [hu])
  have hNsubset : N ⊆ A ∪ E := by
    intro v hv
    have hvAdj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have hvle7 := C4DegreeBounds.neighbor_degree_le_seven_of_degree_eight
      G u (by simp) hmin hC4 hu hv
    have hvmin := hmin v
    simp only [A, E, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hv6 : G.degree v = 6
    · exact Or.inl hv6
    · right
      omega
  have hdisj : Disjoint (N ∩ A) (N ∩ E) := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvE
    have hv6 := (Finset.mem_filter.mp (Finset.mem_inter.mp hvA).2).2
    have hv7 := (Finset.mem_filter.mp (Finset.mem_inter.mp hvE).2).2
    omega
  have hpartition : N = (N ∩ A) ∪ (N ∩ E) := by
    ext v
    constructor
    · intro hvN
      have hvAE := hNsubset hvN
      rcases Finset.mem_union.mp hvAE with hvA | hvE
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hvN, hvA⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hvN, hvE⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvE
      · exact (Finset.mem_inter.mp hvA).1
      · exact (Finset.mem_inter.mp hvE).1
  have hcard : N.card = (N ∩ A).card + (N ∩ E).card := by
    calc
      N.card = (N ∩ A ∪ N ∩ E).card := by rw [← hpartition]
      _ = (N ∩ A).card + (N ∩ E).card := Finset.card_union_of_disjoint hdisj
  rw [hNcard, hseven] at hcard
  have hAcard : (N ∩ A).card = 7 := by omega
  simpa [N, A] using hAcard

/-- In the equality case, every degree-six vertex belongs to the union of
degree-eight neighborhoods. -/
theorem degree_six_vertex_in_degree_eight_union
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {x : Fin 42} (hx : G.degree x = 6) :
    x ∈ (Finset.univ.filter fun v => G.degree v = 8).biUnion
      (fun u => G.neighborFinset u) := by
  classical
  let D := Finset.univ.filter fun v : Fin 42 => G.degree v = 8
  let E := Finset.univ.filter fun v : Fin 42 => G.degree v = 7
  let U := D.biUnion fun u => G.neighborFinset u
  have hmin : ∀ v, 6 ≤ G.degree v := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).1
  have hmax : ∀ v, G.degree v ≤ 8 := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).2
  have hDcard : D.card = 4 := by simpa [D] using h8
  have hEcard : E.card = 16 := by
    exact degree_seven_count_eq_sixteen G hmin hmax he (by simpa [D] using h8)
  have hUcard : U.card = 26 := by
    exact degree_eight_neighborhood_union_card_eq_26 G hDel he hC4 h8
  have hDavoid : Disjoint D U := by
    rw [Finset.disjoint_left]
    intro y hyD hyU
    rcases Finset.mem_biUnion.mp hyU with ⟨u, huD, hyu⟩
    have hu8 := (Finset.mem_filter.mp huD).2
    have hy8 := (Finset.mem_filter.mp hyD).2
    have hyuAdj : G.Adj u y := (G.mem_neighborFinset u y).mp hyu
    have hyu' : u ∈ G.neighborFinset y := (G.mem_neighborFinset y u).mpr (G.symm.symm u y hyuAdj)
    have hbound := C4DegreeBounds.neighbor_degree_le_seven_of_degree_eight
      G y (by simp) hmin hC4 hy8 hyu'
    omega
  have hEbound : (E ∩ U).card ≤ 4 := by
    have hsub : E ∩ U ⊆ D.biUnion (fun u => G.neighborFinset u ∩ E) := by
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hyE, hyU⟩
      rcases Finset.mem_biUnion.mp hyU with ⟨u, huD, hyu⟩
      exact Finset.mem_biUnion.mpr ⟨u, huD, Finset.mem_inter.mpr ⟨hyu, hyE⟩⟩
    calc
      _ ≤ (D.biUnion fun u => G.neighborFinset u ∩ E).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ D, (G.neighborFinset u ∩ E).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ D, 1 := Finset.sum_le_sum fun u hu =>
        degree_seven_neighbors_card_le_one G hmin hC4 (Finset.mem_filter.mp hu).2
      _ = D.card := by simp
      _ = 4 := hDcard
  have hEoutside : (E \ U).card + (E ∩ U).card = E.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : E ∩ U ⊆ E)
    rw [show E \ (E ∩ U) = E \ U by ext y; simp] at h
    exact h
  have hout : D ∪ (E \ U) ⊆ Finset.univ \ U := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyD | hyE
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        intro hyU
        exact (Finset.disjoint_left.mp hDavoid) hyD hyU⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hyE).2⟩
  have hcap : D.card + (E \ U).card ≤ 42 - U.card := by
    calc
      _ = (D ∪ (E \ U)).card := by
        symm
        apply Finset.card_union_of_disjoint
        apply Finset.disjoint_left.mpr
        intro y hyD hyE
        have hy8 := (Finset.mem_filter.mp hyD).2
        have hy7 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hyE).1).2
        omega
      _ ≤ (Finset.univ \ U).card := Finset.card_le_card hout
      _ = 42 - U.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]; simp
  have hEoutside12 : (E \ U).card = 12 := by omega
  have hdisj : Disjoint D (E \ U) := by
    apply Finset.disjoint_left.mpr
    intro y hyD hyE
    have hy8 := (Finset.mem_filter.mp hyD).2
    have hy7 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hyE).1).2
    omega
  have hUnionOutsideCard : (D ∪ (E \ U)).card = 16 := by
    rw [Finset.card_union_of_disjoint hdisj, hDcard, hEoutside12]
  have hcomplementCard : (Finset.univ \ U).card = 16 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]
    simp [hUcard]
  have hcomplement : D ∪ (E \ U) = Finset.univ \ U := by
    apply Finset.eq_of_subset_of_card_le hout
    rw [hcomplementCard, hUnionOutsideCard]
  have hxnotD : x ∉ D := by simp [D, hx]
  have hxnotE : x ∉ E := by simp [E, hx]
  by_contra hxU
  have hxOutside : x ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxU⟩
  rw [← hcomplement] at hxOutside
  rcases Finset.mem_union.mp hxOutside with hxD | hxE
  · exact hxnotD hxD
  · exact hxnotE (Finset.mem_sdiff.mp hxE).1

/-- A degree-six vertex is adjacent to at most two degree-eight vertices in
the four-vertex equality case. -/
theorem degree_six_vertex_has_at_most_two_degree_eight_neighbors
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {x : Fin 42} (hx : G.degree x = 6) :
    (G.neighborFinset x ∩ Finset.univ.filter fun v => G.degree v = 8).card ≤ 2 := by
  classical
  let D := Finset.univ.filter fun v : Fin 42 => G.degree v = 8
  let N := fun u : Fin 42 => G.neighborFinset u
  let U := D.biUnion N
  have hDcard : D.card = 4 := by simpa [D] using h8
  have hUcard : U.card = 26 := degree_eight_neighborhood_union_card_eq_26 G hDel he hC4 h8
  have hPair : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → (N u ∩ N v).card = 1 := by
    intro u hu v hv huv
    exact degree_eight_pair_has_one_common_neighbor G hDel he hC4 h8
      (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 huv
  have hNcard : ∀ u ∈ D, (N u).card = 8 := by
    intro u hu
    simpa [N, G.card_neighborFinset_eq_degree] using (Finset.mem_filter.mp hu).2
  by_contra hnot
  change ¬ (G.neighborFinset x ∩ D).card ≤ 2 at hnot
  have hthree : 3 ≤ (G.neighborFinset x ∩ D).card := Nat.not_le.mp hnot
  obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hthree
  obtain ⟨u, huS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hvCard : (S.erase u).card = 2 := by
    rw [Finset.card_erase_of_mem huS, hScard]
  obtain ⟨v, hvErase⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase u).card)
  have hwCard : ((S.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hvErase, hvCard]
  obtain ⟨w, hwErase⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase u).erase v).card)
  have huS' : u ∈ S := huS
  have hvS' : v ∈ S := (Finset.mem_erase.mp hvErase).2
  have hwS' : w ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hwErase).2).2
  have huv : u ≠ v := (Finset.mem_erase.mp hvErase).1.symm
  have huw : u ≠ w := (Finset.mem_erase.mp (Finset.mem_erase.mp hwErase).2).1.symm
  have hvw : v ≠ w := (Finset.mem_erase.mp hwErase).1.symm
  have huD : u ∈ D := (Finset.mem_inter.mp (hSD huS')).2
  have hvD : v ∈ D := (Finset.mem_inter.mp (hSD hvS')).2
  have hwD : w ∈ D := (Finset.mem_inter.mp (hSD hwS')).2
  have hxN (a : Fin 42) (ha : a ∈ S) : x ∈ N a := by
    have hax : a ∈ G.neighborFinset x := (Finset.mem_inter.mp (hSD ha)).1
    have hAdj : G.Adj x a := (G.mem_neighborFinset x a).mp hax
    have hxa : x ∈ G.neighborFinset a :=
      (G.mem_neighborFinset a x).mpr (G.symm.symm x a hAdj)
    simpa [N] using hxa
  have huCard : (N u).card = 8 := hNcard u huD
  have hvCardN : (N v).card = 8 := hNcard v hvD
  have hwCardN : (N w).card = 8 := hNcard w hwD
  have hUvInter : (N u ∩ N v).card = 1 := hPair u huD v hvD huv
  have hUvUnion : (N u ∪ N v).card = 15 := by
    have hcard := Finset.card_union_add_card_inter (N u) (N v)
    rw [hUvInter, huCard, hvCardN] at hcard
    omega
  have hUwInter : (N u ∩ N w).card = 1 := hPair u huD w hwD huw
  have hVwInter : (N v ∩ N w).card = 1 := hPair v hvD w hwD hvw
  have hWinterUnion : N w ∩ (N u ∪ N v) = {x} := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyw, hyuv⟩
      rcases Finset.mem_union.mp hyuv with hyu | hyv
      · have hyCommon : y ∈ N u ∩ N w := Finset.mem_inter.mpr ⟨hyu, hyw⟩
        have hxCommon : x ∈ N u ∩ N w := Finset.mem_inter.mpr
          ⟨hxN u huS', hxN w hwS'⟩
        have hle : (N u ∩ N w).card ≤ 1 := by omega
        have hEq := Finset.card_le_one.mp hle hyCommon hxCommon
        simpa using hEq.symm
      · have hyCommon : y ∈ N v ∩ N w := Finset.mem_inter.mpr ⟨hyv, hyw⟩
        have hxCommon : x ∈ N v ∩ N w := Finset.mem_inter.mpr
          ⟨hxN v hvS', hxN w hwS'⟩
        have hle : (N v ∩ N w).card ≤ 1 := by omega
        have hEq := Finset.card_le_one.mp hle hyCommon hxCommon
        simpa using hEq.symm
    · intro hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      subst y
      exact Finset.mem_inter.mpr
        ⟨hxN w hwS', Finset.mem_union.mpr (Or.inl (hxN u huS'))⟩
  let U3 := N u ∪ N v ∪ N w
  have hU3card : U3.card = 22 := by
    have hcard := Finset.card_union_add_card_inter (N u ∪ N v) (N w)
    have hinter : (N u ∪ N v) ∩ N w = {x} := by
      rw [Finset.inter_comm]
      exact hWinterUnion
    rw [hinter, hUvUnion, hwCardN] at hcard
    simp [U3]
  have hz : ∃ z ∈ D, z ∉ S := by
    by_contra hnone
    have hDsub : D ⊆ S := by
      intro z hzD
      by_contra hzS
      exact hnone ⟨z, hzD, hzS⟩
    have hDle : D.card ≤ S.card := Finset.card_le_card hDsub
    omega
  obtain ⟨z, hzD, hzS⟩ := hz
  have hzNotU : z ≠ u ∧ z ≠ v ∧ z ≠ w := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; subst z; exact hzS huS'
    · intro h; subst z; exact hzS hvS'
    · intro h; subst z; exact hzS hwS'
  have hzCard : (N z).card = 8 := hNcard z hzD
  have hintersection : (N z ∩ U3).card ≤ 3 := by
    have hsubset : N z ∩ U3 ⊆
        (N z ∩ N u) ∪ (N z ∩ N v) ∪ (N z ∩ N w) := by
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hyz, hy3⟩
      rcases Finset.mem_union.mp hy3 with hyuv | hyw
      · rcases Finset.mem_union.mp hyuv with hyu | hyv
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_inter.mpr ⟨hyz, hyu⟩))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr (Finset.mem_inter.mpr ⟨hyz, hyv⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hyz, hyw⟩))
    have hle : ((N z ∩ N u) ∪ (N z ∩ N v) ∪ (N z ∩ N w)).card ≤ 3 := by
      calc
        _ ≤ ((N z ∩ N u) ∪ (N z ∩ N v)).card + (N z ∩ N w).card :=
          Finset.card_union_le _ _
        _ ≤ (N z ∩ N u).card + (N z ∩ N v).card + (N z ∩ N w).card := by
          have h := Finset.card_union_le (N z ∩ N u) (N z ∩ N v)
          simpa [Nat.add_assoc] using Nat.add_le_add_right h (N z ∩ N w).card
        _ = 3 := by
          rw [hPair z hzD u huD hzNotU.1, hPair z hzD v hvD hzNotU.2.1,
            hPair z hzD w hwD hzNotU.2.2]
          norm_num
    exact (Finset.card_le_card hsubset).trans hle
  have hU4lower : 27 ≤ (U3 ∪ N z).card := by
    have hcard := Finset.card_union_add_card_inter U3 (N z)
    rw [hU3card, hzCard] at hcard
    have hinter : (U3 ∩ N z).card ≤ 3 := by
      simpa [Finset.inter_comm] using hintersection
    omega
  have hsubU : U3 ∪ N z ⊆ U := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy3 | hyz
    · rcases Finset.mem_union.mp hy3 with hyuv | hyw
      · rcases Finset.mem_union.mp hyuv with hyu | hyv
        · exact Finset.mem_biUnion.mpr ⟨u, huD, hyu⟩
        · exact Finset.mem_biUnion.mpr ⟨v, hvD, hyv⟩
      · exact Finset.mem_biUnion.mpr ⟨w, hwD, hyw⟩
    · exact Finset.mem_biUnion.mpr ⟨z, hzD, hyz⟩
  have hU4le : (U3 ∪ N z).card ≤ U.card := Finset.card_le_card hsubU
  omega

end C4DegreeEightMultiplicity

#print axioms C4DegreeEightMultiplicity.degree_eight_neighborhood_union_card_eq_26
#print axioms C4DegreeEightMultiplicity.degree_eight_pair_has_one_common_neighbor
#print axioms C4DegreeEightMultiplicity.degree_eight_vertex_has_seven_degree_six_neighbors
#print axioms C4DegreeEightMultiplicity.degree_six_vertex_in_degree_eight_union
#print axioms C4DegreeEightMultiplicity.degree_six_vertex_has_at_most_two_degree_eight_neighbors
