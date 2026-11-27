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
      _ = ∑ u ∈ S, (O u).card := (Finset.card_biUnion hdisj).symm
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
    exact hC4 hwv hxy hvx hwx ⟨hvy, hwy⟩
  have hcardGe : 1 ≤ (G.neighborFinset v ∩ G.neighborFinset w).card :=
    Finset.card_pos.mpr ⟨u, huCommon⟩
  omega

end C4DegreeEightEquality

#print axioms C4DegreeEightEquality.degree_seven_count_eq_sixteen
#print axioms C4DegreeEightEquality.every_other_vertex_has_unique_common_neighbor
