import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4DegreeBounds

/-!
# Equality consequences when four vertices have degree eight

This module records two consequences of the extremal equality case.  The
handshake identity fixes the number of degree-seven vertices at sixteen.  If
each degree-eight vertex has exactly one degree-seven neighbor, then every
other vertex shares a unique common neighbor with it: the disjoint outer
neighborhoods of its eight neighbors exhaust the other 41 vertices.
-/

namespace C4DegreeEightEquality

private theorem twice_union_card_add_square_bound {V : Type*} [Fintype V]
    [DecidableEq V] (S : Finset V) (f : V → Finset V)
    (hcard : ∀ u ∈ S, (f u).card = 8)
    (hinter : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (f u ∩ f v).card ≤ 1) :
    17 * S.card ≤ 2 * (S.biUnion f).card + S.card ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hcarda := hcard a (Finset.mem_insert_self ..)
    have hcardS : ∀ u ∈ S, (f u).card = 8 := by
      intro u hu
      exact hcard u (Finset.mem_insert_of_mem hu)
    have hinterS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (f u ∩ f v).card ≤ 1 := by
      intro u hu v hv huv
      exact hinter u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv
    have hintera : ∀ v ∈ S, (f a ∩ f v).card ≤ 1 := by
      intro v hv
      exact hinter a (Finset.mem_insert_self ..) v (Finset.mem_insert_of_mem hv)
        (by intro h; subst v; exact ha hv)
    let U := S.biUnion f
    have hsub : f a ∩ U ⊆ S.biUnion (fun v => f a ∩ f v) := by
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxa, hxU⟩
      rcases Finset.mem_biUnion.mp hxU with ⟨v, hv, hxv⟩
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_inter.mpr ⟨hxa, hxv⟩⟩
    have hinterCard : (f a ∩ U).card ≤ S.card := by
      calc
        (f a ∩ U).card ≤ (S.biUnion fun v => f a ∩ f v).card := Finset.card_le_card hsub
        _ ≤ ∑ v ∈ S, (f a ∩ f v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum fun v hv => hintera v hv
        _ = S.card := by simp
    have hUnion : (insert a S).biUnion f = f a ∪ U := by
      simp [U, Finset.biUnion_insert]
    have hUnionCard := Finset.card_union_add_card_inter (f a) U
    have hcardInsert : (insert a S).card = S.card + 1 := by simp [ha]
    rw [hcardInsert]
    have hprev := ih hcardS hinterS
    rw [hUnion]
    nlinarith [hcarda, hinterCard, hUnionCard]

private theorem degree_seven_neighbors_card_le_one (G : SimpleGraph (Fin 42))
    [DecidableRel G.Adj] (hmin : ∀ v, 6 ≤ G.degree v)
    (hC4 : C4VertexExtension.C4Free G) {u : Fin 42} (hu : G.degree u = 8) :
    (G.neighborFinset u ∩ Finset.univ.filter fun v => G.degree v = 7).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hxN := (Finset.mem_inter.mp hx).1
  have hyN := (Finset.mem_inter.mp hy).1
  have hx7 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hy7 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  have hsum := C4DegreeBounds.neighbor_degree_excess_le_one_of_degree_eight
    G u (by simp) hmin hC4 hu
  have hsubset : insert x {y} ⊆ G.neighborFinset u := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hxN
    · simp at hz
      subst z
      exact hyN
  have hsumSubset := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun w : Fin 42 => G.degree w - 6) hsubset
    (fun w hw hwo => Nat.zero_le _)
  have htwo : (G.degree x - 6) + (G.degree y - 6) ≤
      ∑ w ∈ G.neighborFinset u, (G.degree w - 6) := by
    simpa [hxy] using hsumSubset
  omega

/-- In a 42-vertex, 138-edge graph with degrees between six and eight, exactly
four degree-eight vertices force exactly sixteen degree-seven vertices. -/
theorem degree_seven_count_eq_sixteen
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hmin : ∀ v, 6 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 8)
    (he : G.edgeFinset.card = 138)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4) :
    (Finset.univ.filter fun v => G.degree v = 7).card = 16 := by
  classical
  let D7 := Finset.univ.filter fun v => G.degree v = 7
  let D8 := Finset.univ.filter fun v => G.degree v = 8
  have hsumDeg : (∑ v : Fin 42, G.degree v) = 276 := by
    rw [G.sum_degrees_eq_twice_card_edges, he]
  have hsumExcess : (∑ v : Fin 42, (G.degree v - 6)) = 24 := by
    have hdecomp : (∑ v : Fin 42, G.degree v) =
        (∑ v : Fin 42, (G.degree v - 6)) + 252 := by
      calc
        _ = ∑ v : Fin 42, ((G.degree v - 6) + 6) := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (Nat.sub_add_cancel (hmin v)).symm
        _ = _ := by simp [Finset.sum_add_distrib]
    omega
  have hclass : (∑ v : Fin 42, (G.degree v - 6)) = D7.card + 2 * D8.card := by
    have hterm : ∀ v, G.degree v - 6 =
        (if G.degree v = 7 then 1 else 0) + (if G.degree v = 8 then 2 else 0) := by
      intro v
      have hlo := hmin v
      have hhi := hmax v
      by_cases h7 : G.degree v = 7 <;> by_cases h8' : G.degree v = 8 <;>
        simp [h7, h8'] <;> omega
    calc
      _ = ∑ v : Fin 42, ((if G.degree v = 7 then 1 else 0) +
          (if G.degree v = 8 then 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hterm v
      _ = D7.card + 2 * D8.card := by
        rw [Finset.sum_add_distrib]
        have h7 : (∑ v : Fin 42, if G.degree v = 7 then 1 else 0) = D7.card := by
          simp [D7]
        have h8' : (∑ v : Fin 42, if G.degree v = 8 then 2 else 0) = 2 * D8.card := by
          calc
            _ = (Finset.univ.filter fun v : Fin 42 => G.degree v = 8).sum (fun _ => 2) := by
              change _ = Finset.sum
                (Finset.univ.filter (fun v : Fin 42 => G.degree v = 8)) (fun _ => (2 : ℕ))
              exact (Finset.sum_filter (s := Finset.univ)
                (fun v : Fin 42 => G.degree v = 8) (fun _ => (2 : ℕ))).symm
            _ = D8.card * 2 := by simp [D8]
            _ = 2 * D8.card := Nat.mul_comm _ _
        rw [h7, h8']
  have h8' : D8.card = 4 := by simpa [D8] using h8
  rw [hclass, h8'] at hsumExcess
  change D7.card = 16
  omega


/-- With four degree-eight vertices in the extremal degree window, every
degree-eight vertex has exactly one degree-seven neighbor. -/
theorem each_degree_eight_vertex_has_one_degree_seven_neighbor
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4) :
    ∀ u ∈ Finset.univ.filter (fun v => G.degree v = 8),
      (G.neighborFinset u ∩ Finset.univ.filter (fun v => G.degree v = 7)).card = 1 := by
  classical
  let D := Finset.univ.filter fun v => G.degree v = 8
  let E := Finset.univ.filter fun v => G.degree v = 7
  let N := fun u : Fin 42 => G.neighborFinset u
  have hmin : ∀ v, 6 ≤ G.degree v := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).1
  have hmax : ∀ v, G.degree v ≤ 8 := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).2
  have hEcard : E.card = 16 := by
    exact degree_seven_count_eq_sixteen G hmin hmax he (by simpa [D] using h8)
  have hDcard : D.card = 4 := by simpa [D] using h8
  let U := D.biUnion N
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
  have hUlower : 26 ≤ U.card := by
    rw [hDcard] at hUnionBound
    norm_num at hUnionBound
    omega
  have hJlower : 12 ≤ (E \ U).card := by omega
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
  have hUeq : U.card = 26 := by omega
  have hJeq : (E \ U).card = 12 := by rw [hDcard, hUeq] at hcap; omega
  have hWcard : (E ∩ U).card = 4 := by
    have h := hEoutside
    rw [hEcard, hJeq] at h
    omega
  have hWsubset : E ∩ U ⊆ D.biUnion (fun u => G.neighborFinset u ∩ E) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxE, hxU⟩
    rcases Finset.mem_biUnion.mp hxU with ⟨u, huD, hxu⟩
    exact Finset.mem_biUnion.mpr ⟨u, huD, Finset.mem_inter.mpr ⟨hxu, hxE⟩⟩
  have hsumCount : (∑ u ∈ D, (G.neighborFinset u ∩ E).card) = 4 := by
    have hle : (∑ u ∈ D, (G.neighborFinset u ∩ E).card) ≤ D.card := by
      calc
        _ ≤ ∑ _u ∈ D, 1 := Finset.sum_le_sum fun u hu =>
          degree_seven_neighbors_card_le_one G hmin hC4 (Finset.mem_filter.mp hu).2
        _ = D.card := by simp
    have hge : 4 ≤ ∑ u ∈ D, (G.neighborFinset u ∩ E).card := by
      calc
        4 = (E ∩ U).card := hWcard.symm
        _ ≤ (D.biUnion fun u => G.neighborFinset u ∩ E).card := Finset.card_le_card hWsubset
        _ ≤ ∑ u ∈ D, (G.neighborFinset u ∩ E).card := Finset.card_biUnion_le
    rw [hDcard] at hle
    omega
  intro u hu
  have huBound := degree_seven_neighbors_card_le_one G hmin hC4 (Finset.mem_filter.mp hu).2
  by_contra hne
  change ¬ (G.neighborFinset u ∩ E).card = 1 at hne
  have huLE : (G.neighborFinset u ∩ E).card ≤ 1 := by simpa [E] using huBound
  have huZero : (G.neighborFinset u ∩ E).card = 0 := by omega
  have hlt : (∑ w ∈ D, (G.neighborFinset w ∩ E).card) < ∑ _w ∈ D, 1 :=
    Finset.sum_lt_sum (fun w hw =>
      degree_seven_neighbors_card_le_one G hmin hC4 (Finset.mem_filter.mp hw).2)
      ⟨u, hu, by simp [huZero]⟩
  have hlt4 : (∑ w ∈ D, (G.neighborFinset w ∩ E).card) < 4 := by
    simpa [hDcard] using hlt
  rw [hsumCount] at hlt4
  omega


/-- Let `v` have degree eight in a 42-vertex C4-free graph with minimum
degree six. If exactly one neighbor of `v` has degree seven, then every other
vertex shares exactly one common neighbor with `v`. -/
theorem every_other_vertex_has_unique_common_neighbor
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hmin : ∀ u, 6 ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G)
    {v : Fin 42} (hv : G.degree v = 8)
    (hseven : (G.neighborFinset v ∩
      Finset.univ.filter fun u => G.degree u = 7).card = 1) :
    ∀ w, w ≠ v → (G.neighborFinset v ∩ G.neighborFinset w).card = 1 := by
  classical
  let S := G.neighborFinset v
  let O := fun u => (G.neighborFinset u).erase v
  let U := S.biUnion O
  have hScard : S.card = 8 := by
    simpa [S, G.card_neighborFinset_eq_degree] using hv
  have hsumExcessLe : (∑ u ∈ S, (G.degree u - 6)) ≤ 1 := by
    simpa [S] using C4DegreeBounds.neighbor_degree_excess_le_one_of_degree_eight
      G v (by simp) hmin hC4 hv
  have hseven_nonempty : (S ∩ Finset.univ.filter fun u => G.degree u = 7).Nonempty := by
    apply Finset.card_pos.mp
    rw [hseven]
    norm_num
  obtain ⟨u₇, hu₇⟩ := hseven_nonempty
  have hu₇S : u₇ ∈ S := (Finset.mem_inter.mp hu₇).1
  have hu₇deg : G.degree u₇ = 7 := (Finset.mem_filter.mp (Finset.mem_inter.mp hu₇).2).2
  have hsumExcessGe : 1 ≤ ∑ u ∈ S, (G.degree u - 6) := by
    have hsingle := Finset.single_le_sum (f := fun u => G.degree u - 6)
      (fun u hu => Nat.zero_le _) hu₇S
    rw [hu₇deg] at hsingle
    simpa using hsingle
  have hsumExcess : (∑ u ∈ S, (G.degree u - 6)) = 1 := by omega
  have hdegreeSum : (∑ u ∈ S, G.degree u) = 49 := by
    calc
      _ = ∑ u ∈ S, ((G.degree u - 6) + 6) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (Nat.sub_add_cancel (hmin u)).symm
      _ = (∑ u ∈ S, (G.degree u - 6)) + S.card * 6 := by
        simp [Finset.sum_add_distrib]
      _ = 49 := by norm_num [hsumExcess, hScard]
  have houterTerm : ∀ u ∈ S, (O u).card = G.degree u - 1 := by
    intro u hu
    have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp hu
    have huv : v ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u v).mpr (G.symm.symm v u hvu)
    change ((G.neighborFinset u).erase v).card = G.degree u - 1
    rw [Finset.card_erase_of_mem huv, G.card_neighborFinset_eq_degree]
  have houterSum : (∑ u ∈ S, (O u).card) = 41 := by
    have hsumId : (∑ u ∈ S, G.degree u) =
        (∑ u ∈ S, (G.degree u - 1)) + S.card := by
      calc
        _ = ∑ u ∈ S, ((G.degree u - 1) + 1) := by
          apply Finset.sum_congr rfl
          intro u hu
          have huMin := hmin u
          omega
        _ = _ := by simp [Finset.sum_add_distrib]
    have houterEq : (∑ u ∈ S, (O u).card) = ∑ u ∈ S, (G.degree u - 1) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact houterTerm u hu
    omega
  have hdisj : (S : Set (Fin 42)).PairwiseDisjoint O := by
    intro u hu w hw huw
    exact C4DegreeBounds.outerNeighbors_disjoint G hC4 hu hw huw
  have hUcard : U.card = 41 := by
    calc
      _ = ∑ u ∈ S, (O u).card := by simpa [U] using Finset.card_biUnion hdisj
      _ = 41 := houterSum
  have hUsubset : U ⊆ Finset.univ.erase v := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨u, hu, hwu⟩
    have hwv : w ≠ v := (Finset.mem_erase.mp hwu).1
    exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ _⟩
  have hEraseCard : (Finset.univ.erase v : Finset (Fin 42)).card = 41 := by simp
  have hMissing : ((Finset.univ.erase v) \ U).card = 0 := by
    rw [Finset.card_sdiff_of_subset hUsubset, hEraseCard, hUcard]
  have hMissingEmpty : (Finset.univ.erase v) \ U = ∅ := Finset.card_eq_zero.mp hMissing
  intro w hwv
  have hwU : w ∈ U := by
    by_contra hnotU
    have hwErase : w ∈ Finset.univ.erase v :=
      Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ _⟩
    have hmem : w ∈ (Finset.univ.erase v) \ U := Finset.mem_sdiff.mpr ⟨hwErase, hnotU⟩
    rw [hMissingEmpty] at hmem
    simp at hmem
  rcases Finset.mem_biUnion.mp hwU with ⟨u, huS, huw⟩
  have huwAdj : G.Adj u w := by
    have := (Finset.mem_erase.mp huw).2
    simpa using this
  have huv : G.Adj v u := (G.mem_neighborFinset v u).mp huS
  have huCommon : u ∈ G.neighborFinset v ∩ G.neighborFinset w := by
    apply Finset.mem_inter.mpr
    refine ⟨huS, ?_⟩
    exact (G.mem_neighborFinset w u).mpr (G.symm.symm u w huwAdj)
  have hcardLe : (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hvx := (G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1
    have hwx := (G.mem_neighborFinset w x).mp (Finset.mem_inter.mp hx).2
    have hvy := (G.mem_neighborFinset v y).mp (Finset.mem_inter.mp hy).1
    have hwy := (G.mem_neighborFinset w y).mp (Finset.mem_inter.mp hy).2
    exact hC4 hwv.symm hxy hvx hwx ⟨hvy, hwy⟩
  have hcardGe : 1 ≤ (G.neighborFinset v ∩ G.neighborFinset w).card :=
    Finset.card_pos.mpr ⟨u, huCommon⟩
  omega

end C4DegreeEightEquality

#print axioms C4DegreeEightEquality.degree_seven_count_eq_sixteen
#print axioms C4DegreeEightEquality.every_other_vertex_has_unique_common_neighbor
