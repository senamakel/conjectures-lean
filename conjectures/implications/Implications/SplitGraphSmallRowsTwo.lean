import Implications.SplitGraphSmallRows
import Implications.SplitGraphSmallRowsPath

/-!
The case with exactly two selected clique rows of size two.
-/

namespace SplitGraphSmallRowsTwo

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem two_rows_intersect_of_symmDiff_card_le_two
    (s t : Finset V) (hs : s.card = 2) (ht : t.card = 2)
    (hd : (s \ t ∪ t \ s).card ≤ 2) : ∃ x, x ∈ s ∧ x ∈ t := by
  classical
  by_contra hn
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      exact False.elim (hn ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)
    · simp
  have hEq : s ∪ t = s \ t ∪ t \ s := by
    rw [← Finset.symmDiff_eq_union hdis, Finset.symmDiff_def]
  have hunion : (s ∪ t).card = 4 := by
    rw [Finset.card_union_of_disjoint hdis, hs, ht]
  have hlarge : (s \ t ∪ t \ s).card = 4 := by rw [← hEq]; exact hunion
  omega

/-- Two size-two rows under the symmetric-difference bound share a label. -/
theorem two_original_rows_intersect
    (G : SimpleGraph V) (I : Finset V) (c d : V)
    (hc : (row G I c).card = 2) (hd : (row G I d).card = 2)
    (hdiff : (rowDiff G I c d).card ≤ 2) :
    ∃ i, i ∈ row G I c ∧ i ∈ row G I d := by
  exact two_rows_intersect_of_symmDiff_card_le_two _ _ hc hd (by simpa [rowDiff] using hdiff)

/-- The common label gives the only two possibilities: equal rows, or one
shared label and one private label on each side. -/
theorem two_original_rows_shape
    (G : SimpleGraph V) (I : Finset V) (c d : V)
    (hc : (row G I c).card = 2) (hd : (row G I d).card = 2)
    (hdiff : (rowDiff G I c d).card ≤ 2) :
    (row G I c = row G I d) ∨
      ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        row G I c = {u, v} ∧ row G I d = {u, w} := by
  classical
  obtain ⟨u, huC, huD⟩ := two_original_rows_intersect G I c d hc hd hdiff
  have hcEraseCard : ((row G I c).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huC, hc]
  have hdEraseCard : ((row G I d).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huD, hd]
  obtain ⟨v, hvErase⟩ := Finset.card_eq_one.mp hcEraseCard
  obtain ⟨w, hwErase⟩ := Finset.card_eq_one.mp hdEraseCard
  have hCeq : row G I c = {u, v} := by
    ext x
    by_cases hxu : x = u
    · subst x
      simp [huC]
    · have hx : x ∈ row G I c ↔ x ∈ (row G I c).erase u := by
        simp [Finset.mem_erase, hxu]
      rw [hx, hvErase]
      simp [hxu]
  have hDeq : row G I d = {u, w} := by
    ext x
    by_cases hxu : x = u
    · subst x
      simp [huD]
    · have hx : x ∈ row G I d ↔ x ∈ (row G I d).erase u := by
        simp [Finset.mem_erase, hxu]
      rw [hx, hwErase]
      simp [hxu]
  have huv : u ≠ v := by
    have hvMem : v ∈ (row G I c).erase u := by rw [hvErase]; simp
    have hvNe : v ≠ u := (Finset.mem_erase.mp hvMem).1
    exact fun h => hvNe h.symm
  have huw : u ≠ w := by
    have hwMem : w ∈ (row G I d).erase u := by rw [hwErase]; simp
    have hwNe : w ≠ u := (Finset.mem_erase.mp hwMem).1
    exact fun h => hwNe h.symm
  by_cases hvw : v = w
  · left
    rw [hCeq, hDeq, hvw]
  · right
    exact ⟨u, v, w, huv, huw, hvw, hCeq, hDeq⟩

/-- In the equal-row case, the two labels and two clique vertices form a
four-cycle. Its ordering `[i,c,j,d]` is a path with one independent endpoint
and one clique endpoint, ready to attach to the remaining blocks. -/
theorem four_cycle_path_block
    (G : SimpleGraph V) (C I : Finset V) (c d i j : V)
    (hdisj : Disjoint C I) (hc : c ∈ C) (hd : d ∈ C)
    (hi : i ∈ I) (hj : j ∈ I) (hcd : c ≠ d) (hij : i ≠ j)
    (hci : G.Adj c i) (hdi : G.Adj d i)
    (hcj : G.Adj c j) (hdj : G.Adj d j) :
    ∃ p : G.Walk i d, p.IsPath ∧ p.support = [i, c, j, d] := by
  have hnodup : ([i, c, j, d] : List V).Nodup := by
    have hic : i ≠ c := by
      intro h
      subst c
      exact (Finset.disjoint_left.mp hdisj) hc hi
    have hid : i ≠ d := by
      intro h
      subst d
      exact (Finset.disjoint_left.mp hdisj) hd hi
    have hcj' : c ≠ j := by
      intro h
      subst j
      exact (Finset.disjoint_left.mp hdisj) hc hj
    have hjd : j ≠ d := by
      intro h
      subst d
      exact (Finset.disjoint_left.mp hdisj) hd hj
    simp [List.nodup_cons, hic, hij, hid, hcj', hcd, hjd]
  have hchain : ([i, c, j, d] : List V).IsChain G.Adj := by
    simp [List.isChain_cons, hci.symm, hcj, hdj.symm]
  let p := SimpleGraph.Walk.ofSupport ([i, c, j, d] : List V) (by simp) hchain
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport (by simp) hchain] using hnodup
  exact ⟨p, hp, SimpleGraph.Walk.support_ofSupport (by simp) hchain⟩

/-- If two selected size-two rows share exactly one label, their incidence
component is the seven-vertex path through both repeated clique centers. -/
theorem one_overlap_path_block
    (G : SimpleGraph V) (C I : Finset V) (e c d f v u w : V)
    (hdisj : Disjoint C I)
    (heC : e ∈ C) (hcC : c ∈ C) (hdC : d ∈ C) (hfC : f ∈ C)
    (hvI : v ∈ I) (huI : u ∈ I) (hwI : w ∈ I)
    (hec : e ≠ c) (hcd : c ≠ d) (hdf : d ≠ f)
    (hef : e ≠ f) (hvw : v ≠ w) (hvu : v ≠ u) (huw : u ≠ w)
    (hev : G.Adj e v) (hvc : G.Adj v c) (hcu : G.Adj c u)
    (hud : G.Adj u d) (hdw : G.Adj d w) (hwf : G.Adj w f) :
    ∃ p : G.Walk e f, p.IsPath ∧ p.support = [e, v, c, u, d, w, f] := by
  have hnodup : ([e, v, c, u, d, w, f] : List V).Nodup := by
    have hcross (x : V) (hxC : x ∈ C) (y : V) (hyI : y ∈ I) : x ≠ y := by
      intro h
      subst y
      exact (Finset.disjoint_left.mp hdisj) hxC hyI
    have hev' : e ≠ v := hcross e heC v hvI
    have hew : e ≠ w := hcross e heC w hwI
    have heu : e ≠ u := hcross e heC u huI
    have hcv : c ≠ v := hcross c hcC v hvI
    have hcw : c ≠ w := hcross c hcC w hwI
    have hcu' : c ≠ u := hcross c hcC u huI
    have hdv : d ≠ v := hcross d hdC v hvI
    have hdu : d ≠ u := hcross d hdC u huI
    have hdw' : d ≠ w := hcross d hdC w hwI
    have hfv : f ≠ v := hcross f hfC v hvI
    have hfu : f ≠ u := hcross f hfC u huI
    have hfw : f ≠ w := hcross f hfC w hwI
    simp [List.nodup_cons, hec, hcd, hdf, hef, hvw, hvu, huw,
      hev', hew, heu, hcv, hcw, hcu', hdv, hdu, hdw', hfv, hfu, hfw]
  have hchain : ([e, v, c, u, d, w, f] : List V).IsChain G.Adj := by
    simp [List.isChain_cons, hev, hvc, hcu, hud, hdw, hwf]
  let p := SimpleGraph.Walk.ofSupport ([e, v, c, u, d, w, f] : List V) (by simp) hchain
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport (by simp) hchain] using hnodup
  exact ⟨p, hp, SimpleGraph.Walk.support_ofSupport (by simp) hchain⟩

end SplitGraphSmallRowsTwo

#print axioms SplitGraphSmallRowsTwo.two_original_rows_intersect
