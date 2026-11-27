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

end C4DegreeEightMultiplicity

#print axioms C4DegreeEightMultiplicity.degree_eight_neighborhood_union_card_eq_26
#print axioms C4DegreeEightMultiplicity.degree_eight_pair_has_one_common_neighbor
#print axioms C4DegreeEightMultiplicity.degree_six_vertex_in_degree_eight_union
