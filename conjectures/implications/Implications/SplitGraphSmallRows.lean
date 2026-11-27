import Implications.SplitGraphTrees

/-!
Finite set-family lemmas for the connectivity-two, small-row split-graph case.
-/

namespace SplitGraphSmallRows

open SplitGraphTrees

private theorem twoRows_intersect_of_symmDiff_card_le_two
    {α : Type*} [DecidableEq α] (s t : Finset α)
    (hs : s.card = 2) (ht : t.card = 2)
    (hd : (s \ t ∪ t \ s).card ≤ 2) :
    ∃ x, x ∈ s ∧ x ∈ t := by
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
  have : (s \ t ∪ t \ s).card = 4 := by rw [← hEq]; exact hunion
  omega

/-- A pairwise-intersecting family of two-element rows either has a common
vertex or is supported on at most three vertices. -/
theorem pairwise_intersecting_two_sets
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hne : F.Nonempty)
    (hcard : ∀ A ∈ F, A.card = 2)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∃ x, x ∈ A ∧ x ∈ B) :
    (∃ x, ∀ A ∈ F, x ∈ A) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ A ∈ F, A ⊆ {a, b, c} := by
  classical
  obtain ⟨A, hA⟩ := hne
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp (hcard A hA)
  by_cases ha : ∀ T ∈ F, a ∈ T
  · exact Or.inl ⟨a, ha⟩
  by_cases hb : ∀ T ∈ F, b ∈ T
  · exact Or.inl ⟨b, hb⟩
  · push Not at ha hb
    obtain ⟨B, hB, haB⟩ := ha
    obtain ⟨D, hD, hbD⟩ := hb
    have hABne : A ≠ B := by
      intro he
      subst B
      exact haB (by simpa [hAeq])
    obtain ⟨x, hxA, hxB⟩ := hint A hA B hB hABne
    have hx : x = b := by
      have hx' : x = a ∨ x = b := by rw [hAeq] at hxA; simpa using hxA
      rcases hx' with h | h
      · subst x
        exact (haB hxB).elim
      · exact h
    subst x
    rcases Finset.card_eq_two.mp (hcard B hB) with ⟨u, v, huv, hBeq⟩
    have hbu : b = u ∨ b = v := by rw [hBeq] at hxB; simpa using hxB
    have hchoose : ∃ c, b ≠ c ∧ B = {b, c} := by
      rcases hbu with h | h
      · refine ⟨v, ?_, ?_⟩
        · intro hcv
          subst v
          exact huv h.symm
        · subst u
          exact hBeq
      · refine ⟨u, ?_, ?_⟩
        · intro hcu
          subst u
          exact huv h
        · subst v
          simpa [Finset.pair_comm] using hBeq
    obtain ⟨c, hbc, hBeq'⟩ := hchoose
    have hca : c ≠ a := by
      intro h
      apply haB
      rw [hBeq']
      simp [h]
    have hABne' : A ≠ D := by
      intro he
      subst D
      exact hbD (by simpa [hAeq])
    obtain ⟨y, hyA, hyD⟩ := hint A hA D hD hABne'
    have hy : y = a := by
      have hy' : y = a ∨ y = b := by rw [hAeq] at hyA; simpa using hyA
      rcases hy' with h | h
      · exact h
      · subst y
        exact (hbD hyD).elim
    subst y
    have hDneB : D ≠ B := by
      intro he
      subst D
      exact hbD (by rw [hBeq']; simp [hab])
    obtain ⟨z, hzD, hzB⟩ := hint D hD B hB hDneB
    have hzc : z = c := by
      have hz' : z = b ∨ z = c := by rw [hBeq'] at hzB; simpa using hzB
      rcases hz' with h | h
      · subst z
        exact (hbD hzD).elim
      · exact h
    have hcD : c ∈ D := hzc ▸ hzD
    have haD : a ∈ D := by simpa using hyD
    have hDsub : D ⊆ {a, c} := by
      intro q hq
      by_cases hqa : q = a
      · simp [hqa]
      by_cases hqc : q = c
      · simp [hqc]
      have hthree : ({a, c, q} : Finset α) ⊆ D := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact haD
        · exact hcD
        · exact hq
      have haq : a ≠ q := by intro h; exact hqa h.symm
      have hcq : c ≠ q := by intro h; exact hqc h.symm
      have hcardThree : ({a, c, q} : Finset α).card = 3 := by
        simp [hca.symm, hcq, haq]
      have := Finset.card_le_card hthree
      rw [hcard D hD] at this
      omega
    have hDeq : D = {a, c} := by
      apply Finset.eq_of_subset_of_card_le hDsub
      rw [hcard D hD]
      simp [hca.symm]
    have htriple : ({a, b, c} : Finset α).card = 3 := by simp [hab, hca.symm, hbc]
    have hnotTriple : ∀ q, ¬ (q ∈ A ∧ q ∈ B ∧ q ∈ D) := by
      intro q hq
      rw [hAeq, hBeq', hDeq] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with ⟨ha | hb, hb' | hc, ha' | hc'⟩ <;>
        simp_all [hab, hca.symm, hbc]
    refine Or.inr ⟨a, b, c, hab, hca.symm, hbc, ?_⟩
    intro T hT
    by_contra hsub
    obtain ⟨z, hzT, hzOut⟩ := Finset.not_subset.mp hsub
    have hzA : z ∉ A := by
      intro hz
      have : z = a ∨ z = b := by rw [hAeq] at hz; simpa using hz
      rcases this with h | h
      · subst z; exact hzOut (by simp)
      · subst z; exact hzOut (by simp)
    have hzB : z ∉ B := by
      intro hz
      have : z = b ∨ z = c := by rw [hBeq'] at hz; simpa using hz
      rcases this with h | h
      · subst z; exact hzOut (by simp)
      · subst z; exact hzOut (by simp)
    have hzD : z ∉ D := by
      intro hz
      have : z = a ∨ z = c := by rw [hDeq] at hz; simpa using hz
      rcases this with h | h
      · subst z; exact hzOut (by simp)
      · subst z; exact hzOut (by simp)
    have hTAne : T ≠ A := by intro he; subst T; exact hzA hzT
    have hTBne : T ≠ B := by intro he; subst T; exact hzB hzT
    have hTDne : T ≠ D := by intro he; subst T; exact hzD hzT
    obtain ⟨xA, hxAT, hxAA⟩ := hint T hT A hA hTAne
    obtain ⟨xB, hxBT, hxBB⟩ := hint T hT B hB hTBne
    obtain ⟨xD, hxDT, hxDD⟩ := hint T hT D hD hTDne
    rcases Finset.card_eq_two.mp (hcard T hT) with ⟨x, y, hxy, hTeq⟩
    have hzy : z = x ∨ z = y := by rw [hTeq] at hzT; simpa using hzT
    rcases hzy with hzX | hzY
    · subst z
      have hwA : y ∈ A := by
        rcases hint T hT A hA hTAne with ⟨q, hqT, hqA⟩
        rw [hTeq] at hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
        rcases hqT with hq | hq
        · subst q; exact (hzA hqA).elim
        · exact hq ▸ hqA
      have hwB : y ∈ B := by
        rcases hint T hT B hB hTBne with ⟨q, hqT, hqB⟩
        rw [hTeq] at hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
        rcases hqT with hq | hq
        · subst q; exact (hzB hqB).elim
        · exact hq ▸ hqB
      have hwD : y ∈ D := by
        rcases hint T hT D hD hTDne with ⟨q, hqT, hqD⟩
        rw [hTeq] at hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
        rcases hqT with hq | hq
        · subst q; exact (hzD hqD).elim
        · exact hq ▸ hqD
      exact hnotTriple y ⟨hwA, hwB, hwD⟩
    · subst z
      have hwA : x ∈ A := by
        rcases hint T hT A hA hTAne with ⟨q, hqT, hqA⟩
        rw [hTeq] at hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
        rcases hqT with hq | hq
        · exact hq ▸ hqA
        · subst q; exact (hzA hqA).elim
      have hwB : x ∈ B := by
        rcases hint T hT B hB hTBne with ⟨q, hqT, hqB⟩
        rw [hTeq] at hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
        rcases hqT with hq | hq
        · exact hq ▸ hqB
        · subst q; exact (hzB hqB).elim
      have hwD : x ∈ D := by
        rcases hint T hT D hD hTDne with ⟨q, hqT, hqD⟩
        rw [hTeq] at hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
        rcases hqT with hq | hq
        · exact hq ▸ hqD
        · subst q; exact (hzD hqD).elim
      exact hnotTriple x ⟨hwA, hwB, hwD⟩

/-- Without a common center, there are at most three distinct two-element sets. -/
theorem card_le_three_of_no_common_center
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hne : F.Nonempty)
    (hcard : ∀ A ∈ F, A.card = 2)
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∃ x, x ∈ A ∧ x ∈ B)
    (hno : ¬ ∃ x, ∀ A ∈ F, x ∈ A) : F.card ≤ 3 := by
  obtain hcenter | htriangle := pairwise_intersecting_two_sets F hne hcard hint
  · exact (hno hcenter).elim
  · obtain ⟨a, b, c, hab, hac, hbc, hsub⟩ := htriangle
    let S : Finset α := {a, b, c}
    have hsubset : F ⊆ S.powersetCard 2 := by
      intro A hA
      exact Finset.mem_powersetCard.mpr ⟨by simpa [S] using hsub A hA, hcard A hA⟩
    have hle := Finset.card_le_card hsubset
    rw [Finset.card_powersetCard, show S.card = 3 by simp [S, hab, hac, hbc]] at hle
    exact hle

/-- If every label is selected at exactly two clique vertices, at most three
clique vertices can have a selected row of size two. -/
theorem selected_two_rows_card_le_three
    {C I : Type*} [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq I]
    (clique : Finset C) (indep : Finset I) (r : C → Finset I)
    (hsub : ∀ c ∈ clique, r c ⊆ indep)
    (_hrow : ∀ c ∈ clique, (r c).card ≤ 2)
    (hdiff : ∀ c ∈ clique, ∀ d ∈ clique, c ≠ d →
      (r c \ r d ∪ r d \ r c).card ≤ 2)
    (hdegree : ∀ i ∈ indep, (clique.filter (fun c => i ∈ r c)).card = 2) :
    (clique.filter (fun c => (r c).card = 2)).card ≤ 3 := by
  classical
  let F := clique.filter (fun c => (r c).card = 2)
  have hFcard (c : C) (hc : c ∈ F) : (r c).card = 2 :=
    (Finset.mem_filter.mp hc).2
  have hinter (c : C) (hc : c ∈ F) (d : C) (hd : d ∈ F) (hcd : c ≠ d) :
      ∃ i, i ∈ r c ∧ i ∈ r d :=
    twoRows_intersect_of_symmDiff_card_le_two (r c) (r d)
      (hFcard c hc) (hFcard d hd) (hdiff c (Finset.mem_filter.mp hc).1
        d (Finset.mem_filter.mp hd).1 hcd)
  by_cases hdup : ∃ c ∈ F, ∃ d ∈ F, c ≠ d ∧ r c = r d
  · obtain ⟨c, hc, d, hd, hcd, hrows⟩ := hdup
    have hFsub : F ⊆ {c, d} := by
      intro e he
      by_cases hce : c = e
      · simp [hce]
      by_cases hde : e = d
      · simp [hde]
      obtain ⟨i, hic, hie⟩ := hinter c hc e he hce
      have hiI : i ∈ indep := hsub c (Finset.mem_filter.mp hc).1 hic
      have htriple : ({c, d, e} : Finset C) ⊆ clique.filter (fun q => i ∈ r q) := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, hic⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, by simpa [hrows] using hic⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, hie⟩
      have hthree : ({c, d, e} : Finset C).card = 3 := by
        simp [hcd, hce, hde.symm]
      have hle := Finset.card_le_card htriple
      rw [hdegree i hiI, hthree] at hle
      omega
    have hle := Finset.card_le_card hFsub
    change F.card ≤ 3
    exact hle.trans (by simp [hcd])
  · have hinj : Set.InjOn r F := by
      intro c hc d hd hrows
      by_contra hcd
      exact hdup ⟨c, hc, d, hd, hcd, hrows⟩
    by_cases hFempty : F = ∅
    · simp [F, hFempty]
    · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
      let R := F.image r
      have hRne : R.Nonempty := by
        obtain ⟨c, hc⟩ := hFne
        exact ⟨r c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
      have hRcard : ∀ A ∈ R, A.card = 2 := by
        intro A hA
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
        exact hFcard c hc
      have hRint : ∀ A ∈ R, ∀ B ∈ R, A ≠ B → ∃ i, i ∈ A ∧ i ∈ B := by
        intro A hA B hB hAB
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB
        have hcd : c ≠ d := by
          intro heq
          apply hAB
          rw [heq]
        exact hinter c hc d hd hcd
      obtain hcenter | htriangle := pairwise_intersecting_two_sets R hRne hRcard hRint
      · have hxI : ∃ i ∈ indep, ∀ c ∈ F, i ∈ r c := by
          obtain ⟨i, hi⟩ := hcenter
          have hsome : ∃ c ∈ F, i ∈ r c := by
            obtain ⟨c, hc⟩ := hFne
            exact ⟨c, hc, hi (r c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)⟩
          obtain ⟨c, hc, hci⟩ := hsome
          have hiI := hsub c (Finset.mem_filter.mp hc).1 hci
          exact ⟨i, hiI, fun d hd => hi (r d) (Finset.mem_image.mpr ⟨d, hd, rfl⟩)⟩
        obtain ⟨i, hiI, hcenter⟩ := hxI
        have hFsub : F ⊆ clique.filter (fun c => i ∈ r c) := by
          intro c hc
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, hcenter c hc⟩
        have hle := Finset.card_le_card hFsub
        rw [hdegree i hiI] at hle
        change F.card ≤ 3
        omega
      · obtain ⟨a, b, c, hab, hac, hbc, hsubset⟩ := htriangle
        have hRsub : R ⊆ ({a, b, c} : Finset I).powersetCard 2 := by
          intro A hA
          exact Finset.mem_powersetCard.mpr ⟨hsubset A hA, hRcard A hA⟩
        have hRle : R.card ≤ 3 := by
          have hle := Finset.card_le_card hRsub
          rw [Finset.card_powersetCard,
            show ({a, b, c} : Finset I).card = 3 by simp [hab, hac, hbc]] at hle
          exact hle
        have hcardEq : R.card = F.card := Finset.card_image_of_injOn hinj
        change F.card ≤ 3
        rw [← hcardEq]
        exact hRle

/-! The exact family statement applied to clique rows. -/
theorem clique_rows_two_set_structure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C I : Finset V)
    (_hrow : ∀ c ∈ C, (row G I c).card ≤ 2)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ 2)
    (hRows : ∃ c ∈ C, (row G I c).card = 2) :
    (∃ x, ∀ c ∈ C, (row G I c).card = 2 → x ∈ row G I c) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ d ∈ C, (row G I d).card = 2 → row G I d ⊆ {a, b, c} := by
  classical
  let R := (C.image (row G I)).filter (fun s => s.card = 2)
  have hRne : R.Nonempty := by
    obtain ⟨d, hdC, hdrow⟩ := hRows
    exact ⟨row G I d, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, hdC, rfl⟩, hdrow⟩⟩
  have hRcard : ∀ A ∈ R, A.card = 2 := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2
  have hRint : ∀ A ∈ R, ∀ B ∈ R, A ≠ B → ∃ x, x ∈ A ∧ x ∈ B := by
    intro A hA B hB hne
    obtain ⟨d, hdC, hAeq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA).1
    obtain ⟨e, heC, hBeq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hB).1
    subst A B
    by_cases hde : d = e
    · subst e
      exact (hne rfl).elim
    · have hbound := hdiff d hdC e heC hde
      exact twoRows_intersect_of_symmDiff_card_le_two
        (row G I d) (row G I e)
        ((Finset.mem_filter.mp hA).2)
        ((Finset.mem_filter.mp hB).2)
        (by simpa [rowDiff] using hbound)
  obtain hcenter | htriangle := pairwise_intersecting_two_sets R hRne hRcard hRint
  · left
    obtain ⟨x, hx⟩ := hcenter
    refine ⟨x, ?_⟩
    intro d hdC hdrow
    exact hx (row G I d) (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, hdC, rfl⟩, hdrow⟩)
  · right
    obtain ⟨a, b, c, hab, hac, hbc, hsubset⟩ := htriangle
    refine ⟨a, b, c, hab, hac, hbc, ?_⟩
    intro d hdC hdrow
    exact hsubset (row G I d) (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, hdC, rfl⟩, hdrow⟩)

end SplitGraphSmallRows

#print axioms SplitGraphSmallRows.pairwise_intersecting_two_sets
#print axioms SplitGraphSmallRows.card_le_three_of_no_common_center
#print axioms SplitGraphSmallRows.clique_rows_two_set_structure
