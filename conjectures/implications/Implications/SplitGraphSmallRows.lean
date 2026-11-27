import Mathlib

/-!
Finite set-family lemmas for the connectivity-two, small-row split-graph case.
-/

namespace SplitGraphSmallRows

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
        · simpa [h] using hBeq
      · refine ⟨u, ?_, ?_⟩
        · intro hcu
          subst u
          exact huv h
        · simpa [Finset.insert_comm] using hBeq
    obtain ⟨c, hbc, hBeq'⟩ := hchoose
    have hca : c ≠ a := by
      intro h
      apply haB
      rw [hBeq'] at hxB
      simp [h, hxB]
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
      have hcardThree : ({a, c, q} : Finset α).card = 3 := by simp [hca, hqa, hqc]
      have := Finset.card_le_card hthree
      rw [hcard D hD] at this
      omega
    have hDeq : D = {a, c} := by
      apply Finset.eq_of_subset_of_card_le hDsub
      simp [hca, hcard D hD]
    have htriple : ({a, b, c} : Finset α).card = 3 := by simp [hab, hca, hbc]
    have hnotTriple : ∀ q, ¬ (q ∈ A ∧ q ∈ B ∧ q ∈ D) := by
      intro q hq
      rw [hAeq, hBeq', hDeq] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with ⟨(rfl | rfl), (rfl | rfl), (rfl | rfl)⟩ <;> simp_all
    refine Or.inr ⟨a, b, c, hab, hca, hbc, ?_⟩
    intro T hT
    by_contra hsub
    obtain ⟨z, hzT, hzOut⟩ := Finset.exists_of_not_subset hsub
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
    have hyMem (q : α) (hqT : q ∈ T) (hqz : q ≠ z) : q = (if z = x then y else x) := by
      rw [hTeq] at hqT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
      rcases hqT with h | h
      · exact (hqz h).elim
      · exact h
    have hother : z = x → xA = y := by
      intro hzX
      have hxAnz : xA ≠ z := by intro h; subst xA; exact hzA hxAA
      have : xA = x ∨ xA = y := by rw [hTeq] at hxAT; simpa using hxAT
      rcases this with h | h
      · exact (hxAnz (h.trans hzX)).elim
      · exact h
    have hother' : z = y → xA = x := by
      intro hzY
      have hxAnz : xA ≠ z := by intro h; subst xA; exact hzA hxAA
      have : xA = x ∨ xA = y := by rw [hTeq] at hxAT; simpa using hxAT
      rcases this with h | h
      · exact h
      · exact (hxAnz (h.trans hzY)).elim
    have hxA' : xA = y ∨ xA = x := by rcases hzy with h | h; exact Or.inl (hother h); exact Or.inr (hother' h)
    have hyA : (if z = x then y else x) ∈ A := by
      rcases hzy with h | h
      · simpa [h] using (hxA' ▸ hxAA)
      · simpa [h] using (hxA' ▸ hxAA)
    have hyB : (if z = x then y else x) ∈ B := by
      have hxBnz : xB ≠ z := by intro h; subst xB; exact hzB hxBB
      have hxBmem : xB = x ∨ xB = y := by rw [hTeq] at hxBT; simpa using hxBT
      rcases hzy with h | h
      · have hxy' : xB = y := by rcases hxBmem with h' | h' <;> [exact (hxBnz (h'.trans h)).elim; exact h']
        simpa [h] using hxy' ▸ hxBB
      · have hxy' : xB = x := by rcases hxBmem with h' | h' <;> [exact h'; exact (hxBnz (h'.trans h)).elim]
        simpa [h] using hxy' ▸ hxBB
    have hyD : (if z = x then y else x) ∈ D := by
      have hxDnz : xD ≠ z := by intro h; subst xD; exact hzD hxDD
      have hxDmem : xD = x ∨ xD = y := by rw [hTeq] at hxDT; simpa using hxDT
      rcases hzy with h | h
      · have hxy' : xD = y := by rcases hxDmem with h' | h' <;> [exact (hxDnz (h'.trans h)).elim; exact h']
        simpa [h] using hxy' ▸ hxDD
      · have hxy' : xD = x := by rcases hxDmem with h' | h' <;> [exact h'; exact (hxDnz (h'.trans h)).elim]
        simpa [h] using hxy' ▸ hxDD
    exact hnotTriple _ ⟨hyA, hyB, hyD⟩

end SplitGraphSmallRows
