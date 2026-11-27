import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4VertexExtension
import Implications.C4DegreeBounds

/-!
# A degree-eight cap in C4-free graphs

If a 42-vertex C4-free graph has minimum degree six, any eight degree-eight
vertices have neighborhoods whose pairwise intersections have size at most
one.  The union of those neighborhoods therefore has at least 36 vertices.
Since degree-eight vertices are independent, all these neighbors lie among
the other 34 vertices, a contradiction.
-/

namespace C4DegreeEightCap

/-- The union bound for eight-element sets with pairwise intersection at most one. -/
theorem twice_union_card_add_square_bound {V : Type*} [Fintype V]
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

/-- A C4-free graph cannot have eight degree-eight vertices when all degrees
are at least six and the graph has 42 vertices. -/
theorem degree_eight_count_le_seven (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hmin : ∀ v, 6 ≤ G.degree v)
    (hC4 : C4VertexExtension.C4Free G) :
    (Finset.univ.filter fun v => G.degree v = 8).card ≤ 7 := by
  classical
  let D := Finset.univ.filter fun v => G.degree v = 8
  by_contra hnot
  change ¬ D.card ≤ 7 at hnot
  have hD : 8 ≤ D.card := by omega
  obtain ⟨S, hSD, hS⟩ := Finset.exists_subset_card_eq hD
  have hSdeg : ∀ u ∈ S, G.degree u = 8 := by
    intro u hu
    exact (Finset.mem_filter.mp (hSD hu)).2
  have hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
    intro u hu v hv huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hux : G.Adj u x := by simpa using (Finset.mem_inter.mp hx).1
    have hvx : G.Adj v x := by simpa using (Finset.mem_inter.mp hx).2
    have huy : G.Adj u y := by simpa using (Finset.mem_inter.mp hy).1
    have hvy : G.Adj v y := by simpa using (Finset.mem_inter.mp hy).2
    exact hC4 huv hxy hux hvx ⟨huy, hvy⟩
  let N := fun u : Fin 42 => G.neighborFinset u
  have hUnionLower := twice_union_card_add_square_bound S N hSdeg hpair
  have hUnionSize : 36 ≤ (S.biUnion N).card := by
    rw [hS] at hUnionLower
    norm_num at hUnionLower
    omega
  have hnotD : S.biUnion N ⊆ Finset.univ \ D := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨u, hu, hux⟩
    have huD := hSD hu
    have huDeg := (Finset.mem_filter.mp huD).2
    have huxAdj : G.Adj u x := (G.mem_neighborFinset u x).mp hux
    have hxnot : x ∉ D := by
      intro hxD
      have hxDeg := (Finset.mem_filter.mp hxD).2
      have hux' : u ∈ G.neighborFinset x :=
        (G.mem_neighborFinset x u).mpr (G.symm.symm u x huxAdj)
      have hdegreeBound := C4DegreeBounds.neighbor_degree_le_seven_of_degree_eight
        G x (by simp) hmin hC4 hxDeg hux'
      omega
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxnot⟩
  have hUnionUpper : (S.biUnion N).card ≤ 42 - D.card := by
    calc
      _ ≤ (Finset.univ \ D).card := Finset.card_le_card hnotD
      _ = 42 - D.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
        simp [D]
  omega

/-- The `ex(41,C4) ≤ 132` deletion input gives minimum degree six for a
42-vertex, 138-edge graph.  Thus such a C4-free graph has at most seven
degree-eight vertices. -/
theorem degree_eight_count_le_seven_of_extremal_42
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G) :
    (Finset.univ.filter fun v => G.degree v = 8).card ≤ 7 := by
  apply degree_eight_count_le_seven G ?_ hC4
  intro v
  exact (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).1

/-- A degree-eight vertex has at most one degree-seven neighbor. -/
theorem degree_seven_neighbors_card_le_one (G : SimpleGraph (Fin 42))
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
  have hxySum : (G.degree x - 6) + (G.degree y - 6) ≤
      ∑ w ∈ G.neighborFinset u, (G.degree w - 6) := by
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
    simpa [hxy] using hsumSubset
  omega

/-- The degree counts in a 138-edge graph whose degrees lie in the window
from six to eight satisfy the handshake identity. -/
theorem degree_seven_add_twice_degree_eight
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hmin : ∀ v, 6 ≤ G.degree v) (hdeg8 : ∀ v, G.degree v ≤ 8)
    (he : G.edgeFinset.card = 138) :
    (Finset.univ.filter fun v => G.degree v = 7).card +
      2 * (Finset.univ.filter fun v => G.degree v = 8).card = 24 := by
  classical
  let D := Finset.univ.filter fun v => G.degree v = 8
  let E := Finset.univ.filter fun v => G.degree v = 7
  change E.card + 2 * D.card = 24
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
  have hclass : (∑ v : Fin 42, (G.degree v - 6)) = E.card + 2 * D.card := by
    have hterm : ∀ v, G.degree v - 6 =
        (if G.degree v = 7 then 1 else 0) + (if G.degree v = 8 then 2 else 0) := by
      intro v
      have hlow := hmin v
      have hhigh := hdeg8 v
      by_cases h7 : G.degree v = 7 <;> by_cases h8 : G.degree v = 8 <;> simp [h7, h8] <;> omega
    calc
      _ = ∑ v : Fin 42, ((if G.degree v = 7 then 1 else 0) +
          (if G.degree v = 8 then 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hterm v
      _ = E.card + 2 * D.card := by
        rw [Finset.sum_add_distrib]
        have hseven : (∑ v : Fin 42, if G.degree v = 7 then 1 else 0) = E.card := by
          simp [E, Finset.sum_ite_mem_eq]
        have height : (∑ v : Fin 42, if G.degree v = 8 then 2 else 0) = 2 * D.card := by
          calc
            _ = ∑ v ∈ D, (2 : ℕ) := by
              exact (Finset.sum_filter (s := Finset.univ)
                (fun v : Fin 42 => G.degree v = 8) (fun _ => (2 : ℕ))).symm
            _ = D.card * 2 := by simp
            _ = 2 * D.card := Nat.mul_comm _ _
        rw [hseven, height]
  omega

/-- The degree handshake identity and the number of degree-seven vertices
exclude five, six, or seven degree-eight vertices. Combined with the
neighborhood-union bound, the extremal graph has at most four. -/
theorem degree_eight_count_le_four_of_extremal_42
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G) :
    (Finset.univ.filter fun v => G.degree v = 8).card ≤ 4 := by
  classical
  let D := Finset.univ.filter fun v => G.degree v = 8
  let E := Finset.univ.filter fun v => G.degree v = 7
  let N := fun u : Fin 42 => G.neighborFinset u
  have hmin : ∀ v, 6 ≤ G.degree v := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).1
  have hdeg8 : ∀ v, G.degree v ≤ 8 := fun v =>
    (C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4 v).2
  have hk7 := degree_eight_count_le_seven_of_extremal_42 G hDel he hC4
  have hk : D.card ≤ 7 := by simpa [D] using hk7
  by_contra hnot
  change ¬ D.card ≤ 4 at hnot
  have hkLow : 5 ≤ D.card := by omega
  have hkHigh : D.card ≤ 7 := by simpa [D] using hk7
  let U := D.biUnion N
  have hUnionBound : 17 * D.card ≤ 2 * U.card + D.card ^ 2 := by
    have hbound := twice_union_card_add_square_bound D N
      (fun u hu => (Finset.mem_filter.mp hu).2) (by
        intro u hu v hv huv
        have hcommon : (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro x hx y hy
          by_contra hxy
          have hux := by simpa using (Finset.mem_inter.mp hx).1
          have hvx := by simpa using (Finset.mem_inter.mp hx).2
          have huy := by simpa using (Finset.mem_inter.mp hy).1
          have hvy := by simpa using (Finset.mem_inter.mp hy).2
          exact hC4 huv hxy hux hvx ⟨huy, hvy⟩
        exact hcommon)
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
  have houtsideD : D ∪ (E \ U) ⊆ Finset.univ \ U := by
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
      _ ≤ (Finset.univ \ U).card := Finset.card_le_card houtsideD
      _ = 42 - U.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]; simp
  have hEcount : E.card + 2 * D.card = 24 :=
    degree_seven_add_twice_degree_eight G hmin hdeg8 he
  have htarget : D.card ≤ 4 := by
    by_contra hgt
    have hkCases : D.card = 5 ∨ D.card = 6 ∨ D.card = 7 := by omega
    rcases hkCases with hk | hk | hk
    · have hE : E.card = 14 := by omega
      have hlowE : 9 ≤ (E \ U).card := by omega
      rw [hk] at hUnionBound
      norm_num at hUnionBound
      omega
    · have hE : E.card = 12 := by omega
      have hlowE : 6 ≤ (E \ U).card := by omega
      rw [hk] at hUnionBound
      norm_num at hUnionBound
      omega
    · have hE : E.card = 10 := by omega
      have hlowE : 3 ≤ (E \ U).card := by omega
      rw [hk] at hUnionBound
      norm_num at hUnionBound
      omega
  exact hnot htarget

/-- Candidate 138-edge graphs have exactly eighteen plus the degree-eight
count many deletions leaving 132 edges. The deleted vertices are labelled. -/
theorem count_extremal_deletions_eq
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G) :
    (Finset.univ.filter fun v => C4Extremal42.inducedDeletionCount G v = 132).card =
      18 + (Finset.univ.filter fun v => G.degree v = 8).card := by
  classical
  let A := Finset.univ.filter fun v => G.degree v = 6
  let E := Finset.univ.filter fun v => G.degree v = 7
  let D := Finset.univ.filter fun v => G.degree v = 8
  have hwindow := C4DegreeBounds.degree_window_of_extremal_42 G hDel he hC4
  have hcover : (A ∪ E) ∪ D = (Finset.univ : Finset (Fin 42)) := by
    ext v
    have h := hwindow v
    simp [A, E, D]
    omega
  have hAE : Disjoint A E := by
    apply Finset.disjoint_left.mpr
    intro v ha he
    simp [A] at ha
    simp [E] at he
    omega
  have hAED : Disjoint (A ∪ E) D := by
    apply Finset.disjoint_left.mpr
    intro v hAE hD
    simp [A, E] at hAE
    simp [D] at hD
    omega
  have hsize : A.card + E.card + D.card = 42 := by
    rw [← Finset.card_union_of_disjoint hAE, ← Finset.card_union_of_disjoint hAED, hcover]
    simp
  have hhandshake : E.card + 2 * D.card = 24 :=
    degree_seven_add_twice_degree_eight G (fun v => (hwindow v).1)
      (fun v => (hwindow v).2) he
  have hA : (Finset.univ.filter fun v => C4Extremal42.inducedDeletionCount G v = 132) = A := by
    ext v
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [C4Extremal42.inducedDeletionCount_eq, he]
    omega
  rw [hA]
  change A.card = 18 + D.card
  omega

/-- A candidate 138-edge graph has between eighteen and twenty-two labelled
vertex deletions leaving an extremal 41-vertex graph. -/
theorem count_extremal_deletions_bounds
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G) :
    let k := (Finset.univ.filter fun v => C4Extremal42.inducedDeletionCount G v = 132).card
    18 ≤ k ∧ k ≤ 22 := by
  dsimp
  rw [count_extremal_deletions_eq G hDel he hC4]
  have h := degree_eight_count_le_four_of_extremal_42 G hDel he hC4
  omega

end C4DegreeEightCap

#print axioms C4DegreeEightCap.degree_eight_count_le_seven
#print axioms C4DegreeEightCap.degree_eight_count_le_seven_of_extremal_42
#print axioms C4DegreeEightCap.degree_eight_count_le_four_of_extremal_42

#print axioms C4DegreeEightCap.count_extremal_deletions_eq
#print axioms C4DegreeEightCap.count_extremal_deletions_bounds
