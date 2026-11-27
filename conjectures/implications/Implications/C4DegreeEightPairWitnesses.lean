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

#print axioms degree_eight_pair_has_unique_degree_six_neighbor
#print axioms degree_eight_vertices_cover_four_degree_seven_neighbors
#print axioms degree_seven_vertex_has_at_most_one_degree_eight_neighbor

end C4DegreeEightMultiplicity
