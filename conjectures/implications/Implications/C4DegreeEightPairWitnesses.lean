import Implications.C4DegreeEightMultiplicity
import Mathlib.Data.Finset.Powerset

/-! The six degree-six double neighbors are indexed by the six degree-eight pairs. -/

namespace C4DegreeEightMultiplicity

/-- In the four-degree-eight case, the unique common neighbor of each
distinct degree-eight pair has degree six. -/
theorem degree_eight_pair_has_unique_degree_six_neighbor
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138) (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {u v : Fin 42} (hu : G.degree u = 8) (hv : G.degree v = 8) (huv : u ≠ v) :
    ∃! x, G.degree x = 6 ∧ G.Adj u x ∧ G.Adj v x := by
  classical
  let D := Finset.univ.filter fun y => G.degree y = 8
  let pair := fun x => G.neighborFinset x ∩ D
  let B := Finset.univ.filter fun x => G.degree x = 6 ∧ (pair x).card = 2
  have hBcard : B.card = 6 := count_degree_six_with_two_degree_eight_neighbors G hDel he hC4 h8
  have hcard (x : Fin 42) (hx : x ∈ B) : (pair x).card = 2 :=
    (Finset.mem_filter.mp hx).2.2
  have hadj {x w : Fin 42} (hw : w ∈ pair x) : G.Adj w x :=
    ((G.mem_neighborFinset x w).mp (Finset.mem_inter.mp hw).1).symm
  have hinj : Set.InjOn pair B := by
    intro x hx y _ hxy
    by_contra hne
    have hlarge : 1 < (pair x).card := by rw [hcard x hx]; decide
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
    have hay : a ∈ pair y := hxy ▸ ha
    have hby : b ∈ pair y := hxy ▸ hb
    exact hC4 hab hne (hadj ha) (hadj hb) ⟨hadj hay, hadj hby⟩
  have hsubset : B.image pair ⊆ D.powersetCard 2 := by
    intro pairs hpairs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpairs
    exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hcard x hx⟩
  have himage : B.image pair = D.powersetCard 2 := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_image_of_injOn hinj, hBcard, Finset.card_powersetCard]
    change (Finset.univ.filter fun y => G.degree y = 8).card.choose 2 ≤ 6
    rw [h8]
    decide
  have huvPair : ({u, v} : Finset (Fin 42)) ∈ D.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp [huv]⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [D, hu]
    · rw [Finset.mem_singleton] at hw
      subst w
      simp [D, hv]
  rw [← himage] at huvPair
  obtain ⟨x, hx, hpair⟩ := Finset.mem_image.mp huvPair
  have hux : G.Adj u x := hadj (by rw [hpair]; simp)
  have hvx : G.Adj v x := hadj (by rw [hpair]; simp)
  refine ⟨x, ⟨(Finset.mem_filter.mp hx).2.1, hux, hvx⟩, ?_⟩
  intro y hy
  by_contra hne
  exact hC4 huv hne hy.2.1 hy.2.2 ⟨hux, hvx⟩

/-- No degree-seven vertex meets two degree-eight neighborhoods. -/
theorem degree_seven_vertex_has_at_most_one_degree_eight_neighbor
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138) (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {x : Fin 42} (hx : G.degree x = 7) :
    (G.neighborFinset x ∩ Finset.univ.filter fun v => G.degree v = 8).card ≤ 1 := by
  by_contra! hmany
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hmany
  obtain ⟨huAdj, hu8⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvAdj, hv8⟩ := Finset.mem_inter.mp hv
  obtain ⟨y, ⟨hy6, huy, hvy⟩, _⟩ := degree_eight_pair_has_unique_degree_six_neighbor G hDel he
    hC4 h8 (Finset.mem_filter.mp hu8).2 (Finset.mem_filter.mp hv8).2 huv
  have hne : x ≠ y := by
    intro heq
    rw [heq, hy6] at hx
    omega
  exact hC4 huv hne ((G.mem_neighborFinset x u).mp huAdj).symm
    ((G.mem_neighborFinset x v).mp hvAdj).symm ⟨huy, hvy⟩

/-- The four degree-eight vertices have four distinct degree-seven neighbors in total. -/
theorem degree_eight_vertices_cover_four_degree_seven_neighbors
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138) (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4) :
    ((Finset.univ.filter fun v => G.degree v = 8).biUnion
      (fun u => G.neighborFinset u ∩ Finset.univ.filter fun v => G.degree v = 7)).card = 4 := by
  classical
  let D := Finset.univ.filter fun v => G.degree v = 8
  let T := fun u => G.neighborFinset u ∩ Finset.univ.filter fun v => G.degree v = 7
  change (D.biUnion T).card = 4
  have hdisj : (D : Set (Fin 42)).PairwiseDisjoint T := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨z, ⟨hz6, huz, hvz⟩, _⟩ := degree_eight_pair_has_unique_degree_six_neighbor G hDel he
      hC4 h8 (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 huv
    have hx7 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
    have hxz : x ≠ z := by
      intro heq
      rw [heq, hz6] at hx7
      omega
    exact hC4 huv hxz ((G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hx).1)
      ((G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hy).1) ⟨huz, hvz⟩
  rw [Finset.card_biUnion hdisj]
  calc
    _ = ∑ _u ∈ D, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact C4DegreeEightEquality.each_degree_eight_vertex_has_one_degree_seven_neighbor
        G hDel he hC4 h8 u hu
    _ = 4 := by simp [D, h8]

/-- Each degree-eight vertex has three shared and four private
degree-six neighbors in the four-degree-eight profile. -/
theorem degree_eight_shared_private_degree_six_counts
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138) (hC4 : C4VertexExtension.C4Free G)
    (h8 : (Finset.univ.filter fun v => G.degree v = 8).card = 4)
    {u : Fin 42} (hu : G.degree u = 8) :
    let D := Finset.univ.filter fun v => G.degree v = 8
    let A := G.neighborFinset u ∩ Finset.univ.filter fun v => G.degree v = 6
    (A.filter fun x => (G.neighborFinset x ∩ D).card = 2).card = 3 ∧
      (A.filter fun x => (G.neighborFinset x ∩ D).card = 1).card = 4 := by
  classical
  dsimp only
  let D := Finset.univ.filter fun v => G.degree v = 8
  let A := G.neighborFinset u ∩ Finset.univ.filter fun v => G.degree v = 6
  let P := fun x => G.neighborFinset x ∩ D
  let T := D.erase u
  let B := A.filter fun x => (P x).card = 2
  have huD : u ∈ D := by simp [D, hu]
  have hT : T.card = 3 := by
    change (D.erase u).card = 3
    rw [Finset.card_erase_of_mem huD]
    exact congrArg (· - 1) h8
  have hA : A.card = 7 :=
    degree_eight_vertex_has_seven_degree_six_neighbors G hDel he hC4 h8 hu
  have hpartner (v : T) : ∃ x, G.degree x = 6 ∧ G.Adj u x ∧ G.Adj v.val x := by
    have hv := Finset.mem_erase.mp v.property
    exact (degree_eight_pair_has_unique_degree_six_neighbor G hDel he hC4 h8 hu
      (Finset.mem_filter.mp hv.2).2 hv.1.symm).exists
  choose f hf using hpartner
  have hm {x v : Fin 42} (hadj : G.Adj v x) (hv : v ∈ D) : v ∈ P x :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v).mpr hadj.symm, hv⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    by_contra! hne
    have hv := Finset.mem_erase.mp v.property
    have hw := Finset.mem_erase.mp w.property
    have hval : v.val ≠ w.val := fun eq => hne (Subtype.ext eq)
    have hsub : ({u, v.val, w.val} : Finset (Fin 42)) ⊆ P (f v) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hm (hf v).2.1 huD
      · exact hm (hf v).2.2 hv.2
      · rw [hvw]
        exact hm (hf w).2.2 hw.2
    have hlarge := Finset.card_le_card hsub
    have hcard : ({u, v.val, w.val} : Finset (Fin 42)).card = 3 := by
      simp [hv.1.symm, hw.1.symm, hval]
    rw [hcard] at hlarge
    have hsmall := degree_six_vertex_has_at_most_two_degree_eight_neighbors G hDel he hC4 h8 (hf v).1
    change (P (f v)).card ≤ 2 at hsmall
    omega
  have himage : T.attach.image f = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
      have hv := Finset.mem_erase.mp v.property
      have hsub : ({u, v.val} : Finset (Fin 42)) ⊆ P (f v) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hm (hf v).2.1 huD
        · exact hm (hf v).2.2 hv.2
      have hlarge := Finset.card_le_card hsub
      have hcard : ({u, v.val} : Finset (Fin 42)).card = 2 := by simp [hv.1.symm]
      rw [hcard] at hlarge
      have hsmall := degree_six_vertex_has_at_most_two_degree_eight_neighbors G hDel he hC4 h8 (hf v).1
      change (P (f v)).card ≤ 2 at hsmall
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u _).mpr (hf v).2.1, ?_⟩, by omega⟩
      simp [(hf v).1]
    · intro hx
      have ⟨hxA, hxP⟩ := Finset.mem_filter.mp hx
      have ⟨hux, hx6⟩ := Finset.mem_inter.mp hxA
      have hadj := (G.mem_neighborFinset u x).mp hux
      have hxP' : ((P x).erase u).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem (hm hadj huD), hxP]
        decide
      obtain ⟨v, hv⟩ := hxP'
      obtain ⟨hvu, hvP⟩ := Finset.mem_erase.mp hv
      have hvD := (Finset.mem_inter.mp hvP).2
      let vT : T := ⟨v, Finset.mem_erase.mpr ⟨hvu, hvD⟩⟩
      have hvx := ((G.mem_neighborFinset x v).mp (Finset.mem_inter.mp hvP).1).symm
      have hfx : f vT = x := by
        by_contra! hne
        exact hC4 hvu.symm hne (hf vT).2.1 (hf vT).2.2 ⟨hadj, hvx⟩
      exact Finset.mem_image.mpr ⟨vT, Finset.mem_attach _ _, hfx⟩
  have hB : B.card = 3 := by
    rw [← himage, Finset.card_image_of_injOn hinj.injOn, Finset.card_attach, hT]
  have hsplit : A.filter (fun x => ¬ (P x).card = 2) = A.filter (fun x => (P x).card = 1) := by
    ext x
    simp only [Finset.mem_filter]
    refine and_congr_right fun hx => ?_
    have hx6 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
    have hxhi := degree_six_vertex_has_at_most_two_degree_eight_neighbors G hDel he hC4 h8 hx6
    change (P x).card ≤ 2 at hxhi
    have hxlo : 0 < (P x).card :=
      Finset.card_pos.mpr ⟨u, hm ((G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hx).1) huD⟩
    omega
  have hcount := A.card_filter_add_card_filter_not (fun x => (P x).card = 2)
  rw [hsplit, hA] at hcount
  change B.card + (A.filter fun x => (P x).card = 1).card = 7 at hcount
  change B.card = 3 ∧ (A.filter fun x => (P x).card = 1).card = 4
  exact ⟨hB, by omega⟩

#print axioms degree_eight_shared_private_degree_six_counts
#print axioms degree_eight_pair_has_unique_degree_six_neighbor
#print axioms degree_eight_vertices_cover_four_degree_seven_neighbors
#print axioms degree_seven_vertex_has_at_most_one_degree_eight_neighbor

end C4DegreeEightMultiplicity
