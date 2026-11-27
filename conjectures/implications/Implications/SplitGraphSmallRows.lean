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
    (hint : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).Nonempty) :
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
  · push_neg at ha hb
    obtain ⟨B, hB, haB⟩ := ha
    obtain ⟨D, hD, hbD⟩ := hb
    have hAB : (A ∩ B).Nonempty := by
      apply hint A hA B hB
      intro he
      subst B
      exact haB (by simpa [hAeq])
    obtain ⟨x, hxA, hxB⟩ := hAB
    have hx : x = b := by
      have hx' : x = a ∨ x = b := by
        rw [hAeq] at hxA
        simpa using hxA
      rcases hx' with h | h
      · subst x
        exact (haB hxB).elim
      · exact h
    subst x
    have hBpair := Finset.card_eq_two.mp (hcard B hB)
    rcases hBpair with ⟨u, v, huv, hBeq⟩
    have hbu : b = u ∨ b = v := by
      rw [hBeq] at hxB
      simpa using hxB
    obtain ⟨c, hcne, hBeq'⟩ := by
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
    have hca : c ≠ a := by
      intro h
      apply haB
      rw [hBeq'] at hxB
      simp [h, hxB]
    have hBAne : b ∈ B := by rw [hBeq']; simp
    have hAc : a ∉ B := haB
    have hAD : (A ∩ D).Nonempty := by
      apply hint A hA D hD
      intro he
      subst D
      exact hbD (by simpa [hAeq])
    obtain ⟨y, hyA, hyD⟩ := hAD
    have hy : y = a := by
      have hy' : y = a ∨ y = b := by rw [hAeq] at hyA; simpa using hyA
      rcases hy' with h | h
      · exact h
      · subst y
        exact (hbD hyD).elim
    subst y
    rcases Finset.card_eq_two.mp (hcard D hD) with ⟨uD, vD, huvD, hDeq⟩
    have had : a = uD ∨ a = vD := by rw [hDeq] at hyD; simpa using hyD
    have hDsubset : D ⊆ {a, c} := by
      rw [hDeq]
      rcases had with h | h
      · subst uD
        have hvB : vD = c := by
          have hvMem : vD ∈ B := by rw [hBeq']; simp [Finset.mem_insert, huv]
          have hvNotb : vD ≠ b := by
            intro he
            subst vD
            exact huvD rfl
          have : vD = c := by
            rw [hBeq'] at hxB
            have hvB' : vD ∈ insert b {c} := by simpa [hBeq'] using hvMem
            simpa [hvNotb] using hvB'
          exact this
        rw [hvB]
        simp [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
      · subst vD
        have huB : uD = c := by
          have huMem : uD ∈ B := by rw [hBeq']; simp [Finset.mem_insert, huv]
          have huNotb : uD ≠ b := by
            intro he
            subst uD
            exact huvD rfl
          have huB' : uD ∈ insert b {c} := by simpa [hBeq'] using huMem
          simpa [huNotb] using huB'
        rw [huB]
        simp [Finset.insert_comm, Finset.insert_left_comm, Finset.insert_assoc]
    have ha_notB : a ∉ B := haB
    have hb_notD : b ∉ D := hbD
    have htriple : ({a, b, c} : Finset α).card = 3 := by simp [hab, hca, hcne]
    refine Or.inr ⟨a, b, c, hab, hca, hcne, ?_⟩
    intro T hT
    by_contra hsub
    obtain ⟨z, hzT, hzOut⟩ := Finset.exists_of_not_subset hsub
    have hzA : z ∉ A := by
      intro hz
      have : z = a ∨ z = b := by rw [hAeq] at hz; simpa using hz
      rcases this with h | h
      · subst z
        exact hzOut (by simp)
      · subst z
        exact hzOut (by simp)
    have hzB : z ∉ B := by
      intro hz
      have hz' : z = b ∨ z = c := by rw [hBeq']; simpa using hz
      rcases hz' with h | h
      · subst z; exact hzOut (by simp)
      · subst z; exact hzOut (by simp)
    have hzD : z ∉ D := by
      intro hz
      have hz' : z = a ∨ z = c := by
        have := hDsubset hz
        simpa using this
      rcases hz' with h | h
      · subst z; exact hzOut (by simp)
      · subst z; exact hzOut (by simp)
    have hTA := hint T hT A hA (by
      intro he
      subst T
      exact hzA hzT)
    have hTB := hint T hT B hB (by
      intro he
      subst T
      exact hzB hzT)
    have hTD := hint T hT D hD (by
      intro he
      subst T
      exact hzD hzT)
    obtain ⟨xA, hxAT, hxAA⟩ := hTA
    obtain ⟨xB, hxBT, hxBB⟩ := hTB
    obtain ⟨xD, hxDT, hxDD⟩ := hTD
    have hTle : T.card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro x hx y hy
      by_contra hxy
      have hxne : x ≠ z := by intro h; subst x; exact hzA hxAA
      have hyne : y ≠ z := by intro h; subst y; exact hzA hxAA
      have hxother : x ∈ T.erase z := by simp [Finset.mem_erase, hxne, hx]
      have hyother : y ∈ T.erase z := by simp [Finset.mem_erase, hyne, hy]
      have hTsub : T ⊆ insert z (T.erase z) := by intro q hq; by_cases hqz : q = z <;> simp [hqz, hq]
      have hzy : z ∈ T := by
        have hcardT := hcard T hT
        have hzT' := hzT
        have hnonz : T.erase z = ∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro q hq
          have hqT : q ∈ T := (Finset.mem_erase.mp hq).2
          have hqz : q ≠ z := (Finset.mem_erase.mp hq).1
          have hqne : q ≠ z := hqz
          have : ({z, q} : Finset α).card ≤ T.card := Finset.card_le_card (by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact hzT
            · exact hqT)
          simp [hqne] at this
          omega
        have : T.card = 1 := by
          have := Finset.card_erase_add_one (s := T) (a := z)
          by_cases hmem : z ∈ T
          · simpa [hmem, hnonz] using this
          · have hempty : T.erase z = T := Finset.erase_eq_of_not_mem hmem
            rw [hempty] at hnonz
            simp at hnonz
            exact (Finset.not_mem_empty z hnonz).elim
        have := hcard T hT
        omega
      have hzT' : z ∈ T := hzy
      have hxnot : x ≠ z := by intro h; subst x; exact hzA hxAA
      have hynot : y ≠ z := by intro h; subst y; exact hzA hxAA
      have hcardpair : ({x, y} : Finset α).card = 2 := by simp [hxy]
      have hpairSub : ({x, y} : Finset α) ⊆ T := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hx
        · exact hy
      have : 2 ≤ T.card := by rw [← hcardpair]; exact Finset.card_le_card hpairSub
      omega
    have hcardT := hcard T hT
    omega

end SplitGraphSmallRows
