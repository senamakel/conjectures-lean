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

end C4DegreeEightCap

#print axioms C4DegreeEightCap.degree_eight_count_le_seven
#print axioms C4DegreeEightCap.degree_eight_count_le_seven_of_extremal_42
