import Implications.SplitGraphSmallRows
import Implications.SplitGraphSmallRowsPath
import Implications.SplitGraphSmallRowsBlocks
import Implications.SplitGraphSmallRowsThree
import Implications.SplitGraphSmallRowsCompletion

/-!
The case with exactly two selected clique rows of size two.
-/

namespace SplitGraphSmallRowsTwo

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private def selectedRow (I : Finset V) (left right : V → V) (q : V) : Finset V :=
  I.filter (fun i => left i = q ∨ right i = q)

/-- A clique vertex with two selected incidences has exactly those two
independent neighbors in its original row, when original rows have size at
most two. -/
theorem selected_row_eq_original_of_card_two
    (G : SimpleGraph V) (I : Finset V) (left right : V → V) (q : V)
    (hleftAdj : ∀ i ∈ I, G.Adj (left i) i)
    (hrightAdj : ∀ i ∈ I, G.Adj (right i) i)
    (hselected : (selectedRow I left right q).card = 2)
    (hrow : (row G I q).card ≤ 2) :
    selectedRow I left right q = row G I q := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    rcases hi'.2 with heq | heq
    · exact Finset.mem_filter.mpr ⟨hi'.1, heq ▸ hleftAdj i hi'.1⟩
    · exact Finset.mem_filter.mpr ⟨hi'.1, heq ▸ hrightAdj i hi'.1⟩
  · rw [hselected]
    exact hrow

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
    (hcentersNodup : ([e, c, d, f] : List V).Nodup)
    (hvw : v ≠ w) (hvu : v ≠ u) (huw : u ≠ w)
    (hev : G.Adj e v) (hvc : G.Adj v c) (hcu : G.Adj c u)
    (hud : G.Adj u d) (hdw : G.Adj d w) (hwf : G.Adj w f) :
    ∃ p : G.Walk e f, p.IsPath ∧ p.support = [e, v, c, u, d, w, f] := by
  have hnodup : ([e, v, c, u, d, w, f] : List V).Nodup := by
    have hcenters := hcentersNodup
    simp only [List.nodup_cons, List.not_mem_nil, List.mem_cons, List.mem_singleton,
      not_or, not_false_eq_true] at hcenters
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
    simp [List.nodup_cons, hcenters.1.1, hcenters.1.2.1, hcenters.1.2.2,
      hcenters.2.1.1, hcenters.2.1.2, hcenters.2.2,
      hvw, hvu, huw,
      hev', hew, heu, hcv, hcw, hcu', hdv, hdu, hdw', hfv, hfu, hfw,
      hcv.symm, hdv.symm, hfv.symm, hdu.symm, hfu.symm, hfw.symm]
  have hchain : ([e, v, c, u, d, w, f] : List V).IsChain G.Adj := by
    simp [List.isChain_cons, hev, hvc, hcu, hud, hdw, hwf]
  let p := SimpleGraph.Walk.ofSupport ([e, v, c, u, d, w, f] : List V) (by simp) hchain
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport (by simp) hchain] using hnodup
  exact ⟨p, hp, SimpleGraph.Walk.support_ofSupport (by simp) hchain⟩

/-- Under the original row and row-difference bounds, the two selected double
rows are either equal or share exactly one independent vertex. -/
theorem chosen_two_double_rows_have_shape
    (G : SimpleGraph V) (C I : Finset V) (left right : V → V)
    (hleftAdj : ∀ i ∈ I, G.Adj (left i) i)
    (hrightAdj : ∀ i ∈ I, G.Adj (right i) i)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 2)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hcount : (C.filter (fun q => (selectedRow I left right q).card = 2)).card = 2) :
    ∃ c d u v w, c ∈ C ∧ d ∈ C ∧ c ≠ d ∧
      ((selectedRow I left right c = {u,v} ∧ selectedRow I left right d = {u,v}) ∨
       (selectedRow I left right c = {u,v} ∧ selectedRow I left right d = {u,w} ∧
        u ≠ v ∧ u ≠ w ∧ v ≠ w)) := by
  classical
  let S := C.filter (fun q => (selectedRow I left right q).card = 2)
  have hSCard : S.card = 2 := hcount
  obtain ⟨c,d,hcd,hS⟩ := Finset.card_eq_two.mp hSCard
  have hcS : c ∈ S := by rw [hS]; simp
  have hdS : d ∈ S := by rw [hS]; simp [hcd]
  have hcC : c ∈ C := (Finset.mem_filter.mp hcS).1
  have hdC : d ∈ C := (Finset.mem_filter.mp hdS).1
  have hcCard : (selectedRow I left right c).card = 2 := by
    have := (Finset.mem_filter.mp hcS).2
    exact this
  have hdCard : (selectedRow I left right d).card = 2 := by
    have := (Finset.mem_filter.mp hdS).2
    exact this
  have hselectedEqC : selectedRow I left right c = row G I c :=
    selected_row_eq_original_of_card_two G I left right c hleftAdj hrightAdj hcCard (hrow c hcC)
  have hselectedEqD : selectedRow I left right d = row G I d :=
    selected_row_eq_original_of_card_two G I left right d hleftAdj hrightAdj hdCard (hrow d hdC)
  obtain hsame | ⟨u,v,w,huv,huw,hvw,hcRow,hdRow⟩ :=
    two_original_rows_shape G I c d (by rw [← hselectedEqC]; exact hcCard)
      (by rw [← hselectedEqD]; exact hdCard)
      (hdiff c hcC d hdC hcd)
  · have hrowCCard : (row G I c).card = 2 := by rw [← hselectedEqC]; exact hcCard
    obtain ⟨u,v,huv,hrowPair⟩ := Finset.card_eq_two.mp hrowCCard
    refine ⟨c,d,u,v,v,hcC,hdC,hcd,?_⟩
    exact Or.inl ⟨hselectedEqC.trans hrowPair,
      hselectedEqD.trans (hsame.symm.trans hrowPair)⟩
  · refine ⟨c,d,u,v,w,hcC,hdC,hcd,Or.inr ?_⟩
    exact ⟨hselectedEqC.trans hcRow, hselectedEqD.trans hdRow, huv, huw, hvw⟩

/-- Choose the two outer centers in the one-overlap row pattern. -/
theorem outer_endpoints_of_overlapping_rows
    (G : SimpleGraph V) (C I : Finset V) (left right : V → V)
    (c d u v w : V) (hcd : c ≠ d)
    (hrowC : selectedRow I left right c = {u,v})
    (hrowD : selectedRow I left right d = {u,w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hleftC : ∀ i ∈ I, left i ∈ C) (hrightC : ∀ i ∈ I, right i ∈ C)
    (hleftAdj : ∀ i ∈ I, G.Adj (left i) i)
    (hrightAdj : ∀ i ∈ I, G.Adj (right i) i)
    (hneq : ∀ i ∈ I, left i ≠ right i)
    (hrowBound : ∀ q ∈ C, (row G I q).card ≤ 2)
    (hnotDouble : ∀ q ∈ C, q ≠ c → q ≠ d → (selectedRow I left right q).card ≠ 2) :
    ∃ e f, e ∈ C ∧ f ∈ C ∧ e ≠ c ∧ e ≠ d ∧ f ≠ c ∧ f ≠ d ∧ e ≠ f ∧
      G.Adj e v ∧ G.Adj v c ∧ G.Adj c u ∧ G.Adj u d ∧ G.Adj d w ∧ G.Adj w f := by
  classical
  have hvSel : v ∈ selectedRow I left right c := by rw [hrowC]; simp [hvw]
  have hwSel : w ∈ selectedRow I left right d := by rw [hrowD]; simp [hvw.symm]
  have huSel : u ∈ selectedRow I left right c := by rw [hrowC]; simp [huv]
  have hvC : v ∈ I := (Finset.mem_filter.mp hvSel).1
  have hwI : w ∈ I := (Finset.mem_filter.mp hwSel).1
  have huI : u ∈ I := (Finset.mem_filter.mp huSel).1
  have hvAtC : left v = c ∨ right v = c := by
    exact (Finset.mem_filter.mp hvSel).2
  have hwAtD : left w = d ∨ right w = d := by
    exact (Finset.mem_filter.mp hwSel).2
  let e := if left v = c then right v else left v
  let f := if left w = d then right w else left w
  have hev : (left v = c ∧ e = right v) ∨ (right v = c ∧ e = left v) := by
    dsimp [e]
    split
    · intro h
      exact Or.inl ⟨h, rfl⟩
    · intro h
      exact Or.inr ⟨hvAtC.resolve_left h, rfl⟩
  have hfw : (left w = d ∧ f = right w) ∨ (right w = d ∧ f = left w) := by
    dsimp [f]
    split
    · intro h
      exact Or.inl ⟨h, rfl⟩
    · intro h
      exact Or.inr ⟨hwAtD.resolve_left h, rfl⟩
  have heC : e ∈ C := by
    rcases hev with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hrightC v hvC
    · exact hleftC v hvC
  have hfC : f ∈ C := by
    rcases hfw with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hrightC w hwI
    · exact hleftC w hwI
  have heNeC : e ≠ c := by
    rcases hev with ⟨hl, he⟩ | ⟨hr, he⟩
    · intro h
      subst e
      exact hneq v hvC (hl.trans he.symm)
    · intro h
      subst e
      exact hneq v hvC (he.trans hr)
  have hfNeD : f ≠ d := by
    rcases hfw with ⟨hl, hf⟩ | ⟨hr, hf⟩
    · intro h
      subst f
      exact hneq w hwI (hl.trans hf.symm)
    · intro h
      subst f
      exact hneq w hwI (hf.trans hr)
  have heNeD : e ≠ d := by
    intro h
    have hvD : v ∈ selectedRow I left right d := by
      rcases hev with ⟨hl, he⟩ | ⟨hr, he⟩
      · exact Finset.mem_filter.mpr ⟨hvC, Or.inr (by simpa [e, hl] using h)⟩
      · exact Finset.mem_filter.mpr ⟨hvC, Or.inl (by simpa [e, hr] using h)⟩
    rw [hrowD] at hvD
    simp [huv, hvw, hvD] at hvD
  have hfNeC : f ≠ c := by
    intro h
    have hwC : w ∈ selectedRow I left right c := by
      rcases hfw with ⟨hl, hf⟩ | ⟨hr, hf⟩
      · exact Finset.mem_filter.mpr ⟨hwI, Or.inr (by simpa [f, hl] using h)⟩
      · exact Finset.mem_filter.mpr ⟨hwI, Or.inl (by simpa [f, hr] using h)⟩
    rw [hrowC] at hwC
    simp [huv, hvw.symm, hwC] at hwC
  have hselAt (q i : V) (hi : i ∈ selectedRow I left right q) : G.Adj q i := by
    have hi' := Finset.mem_filter.mp hi
    rcases hi'.2 with heq | heq
    · exact heq ▸ hleftAdj i hi'.1
    · exact heq ▸ hrightAdj i hi'.1
  have hcu : G.Adj c u := hselAt c u (by rw [hrowC]; simp [huv])
  have hud : G.Adj u d := (hselAt d u (by rw [hrowD]; simp [huw])).symm
  have hcv : G.Adj v c := (hselAt c v (by rw [hrowC]; simp [hvw])).symm
  have hdw : G.Adj d w := hselAt d w (by rw [hrowD]; simp [hvw.symm])
  have hevAdj : G.Adj e v := by
    rcases hev with ⟨_, he⟩ | ⟨_, he⟩
    · rw [he]
      exact (hselAt c v (by rw [hrowC]; simp [hvw])).symm
    · rw [he]
      exact hleftAdj v hvC
  have hwfAdj : G.Adj w f := by
    rcases hfw with ⟨_, hf⟩ | ⟨_, hf⟩
    · rw [hf]
      exact (hselAt d w (by rw [hrowD]; simp [hvw.symm])).symm
    · rw [hf]
      exact hleftAdj w hwI
  have heNeF : e ≠ f := by
    intro hef
    have hvE : v ∈ selectedRow I left right e := by
      rcases hev with ⟨_, he⟩ | ⟨_, he⟩
      · rw [he, ← hef]
        exact Finset.mem_filter.mpr ⟨hvC, Or.inr rfl⟩
      · rw [he, ← hef]
        exact Finset.mem_filter.mpr ⟨hvC, Or.inl rfl⟩
    have hwE : w ∈ selectedRow I left right e := by
      rcases hfw with ⟨_, hf⟩ | ⟨_, hf⟩
      · rw [hf, ← hef]
        exact Finset.mem_filter.mpr ⟨hwI, Or.inr rfl⟩
      · rw [hf, ← hef]
        exact Finset.mem_filter.mpr ⟨hwI, Or.inl rfl⟩
    have hpair : ({v,w} : Finset V) ⊆ selectedRow I left right e := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hvE
      · exact hwE
    have hpairCard : ({v,w} : Finset V).card = 2 := by simp [hvw]
    have hle : (selectedRow I left right e).card ≤ 2 := by
      apply Finset.card_le_card
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      rcases hi'.2 with heq | heq
      · exact Finset.mem_filter.mpr ⟨hi'.1, heq ▸ hleftAdj i hi'.1⟩
      · exact Finset.mem_filter.mpr ⟨hi'.1, heq ▸ hrightAdj i hi'.1⟩
      exact hrowBound e heC
    have hcard : (selectedRow I left right e).card = 2 := by
      have := Finset.card_le_card hpair
      omega
    exact hnotDouble e heC heNeC heNeD hcard
  exact ⟨e,f,heC,hfC,heNeC,heNeD,hfNeC,hfNeD,heNeF,
    hevAdj,hcv,hcu,hud,hdw,hwfAdj⟩


end SplitGraphSmallRowsTwo

#print axioms SplitGraphSmallRowsTwo.two_original_rows_intersect
#print axioms SplitGraphSmallRowsTwo.selected_row_eq_original_of_card_two
#print axioms SplitGraphSmallRowsTwo.two_original_rows_shape
#print axioms SplitGraphSmallRowsTwo.four_cycle_path_block
#print axioms SplitGraphSmallRowsTwo.one_overlap_path_block
