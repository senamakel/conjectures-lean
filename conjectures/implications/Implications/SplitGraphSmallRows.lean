import Implications.SplitGraphTrees

/-!
Finite set-family lemmas for the connectivity-two, small-row split-graph case.
-/

namespace SplitGraphSmallRows

private theorem twoRows_intersect_of_symmDiff_card_le_two
    {α : Type*} [DecidableEq α] (s t : Finset α)
    (hs : s.card = 2) (ht : t.card = 2)
    (hd : (s \ t ∪ t \ s).card ≤ 2) :
    ∃ x, x ∈ s ∧ x ∈ t := by
  classical
  by_contra hn
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact hn ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
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

/-! The exact family statement applied to clique rows. -/
theorem clique_rows_two_set_structure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C I : Finset V)
    (hrow : ∀ c ∈ C, (row G I c).card ≤ 2)
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
#print axioms SplitGraphSmallRows.clique_rows_two_set_structure
