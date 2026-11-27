import Implications.WilfGlobalSwap
import Implications.WilfMarked
import Implications.WilfEquivalence

/-! The effect of simultaneous position swaps on occurrences in marked windows. -/

namespace Implications.WilfPatternSwap

open WilfMarked WilfGlobalSwap

private def atOffset {n : ℕ} (s : ℕ) (hs : s + 7 < n) (i : Fin 8) : Fin n :=
  ⟨s + i.val, by have := i.isLt; omega⟩

private theorem swaps_nonfirst {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    {s : ℕ} (hs : s ∈ marks) (i : Fin 8) (hi : i ≠ 0) :
    swapIndex marks hb hd (atOffset s (hb s hs) i) =
      atOffset s (hb s hs) (windowSwap i) := by
  apply Fin.ext
  have hi' : 0 < i.val := by
    by_contra! h
    exact hi (Fin.ext (by omega))
  have hi8 := i.isLt
  by_cases h3 : i = 3
  · subst i
    rw [swapIndex_val_left _ _ _ _ ⟨s, hs, rfl⟩]
    rfl
  by_cases h5 : i = 5
  · subst i
    rw [swapIndex_val_right _ _ _ _ ⟨s, hs, rfl⟩]
    simp [atOffset, windowSwap]
    omega
  have hleft : ¬ IsLeft marks (atOffset s (hb s hs) i) := by
    rintro ⟨t, ht, he⟩
    change s + i.val = t + 3 at he
    rcases lt_trichotomy t s with h | rfl | h
    · have := hd t ht s hs h
      omega
    · exact h3 (Fin.ext (by omega))
    · have := hd s hs t ht h
      omega
  have hright : ¬ IsRight marks (atOffset s (hb s hs) i) := by
    rintro ⟨t, ht, he⟩
    change s + i.val = t + 5 at he
    rcases lt_trichotomy t s with h | rfl | h
    · have := hd t ht s hs h
      omega
    · exact h5 (Fin.ext (by omega))
    · have := hd s hs t ht h
      omega
  rw [swapIndex_val_other _ _ _ _ hleft hright]
  simp [windowSwap, h3, h5]

private theorem swaps_first_lt_second {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8) (hp : p = sigma ∨ p = tau)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) {s : ℕ} (hs : s ∈ marks) :
    π (swapIndex marks hb hd (atOffset s (hb s hs) 0)) <
      π (atOffset s (hb s hs) 2) := by
  have hleft : ¬ IsLeft marks (atOffset s (hb s hs) 0) := by
    rintro ⟨t, ht, he⟩
    change s + 0 = t + 3 at he
    have hts : t < s := by omega
    have := hd t ht s hs hts
    omega
  by_cases hright : IsRight marks (atOffset s (hb s hs) 0)
  · obtain ⟨t, ht, he⟩ := hright
    change s + 0 = t + 5 at he
    have hw₀ : swapIndex marks hb hd (atOffset s (hb s hs) 0) =
        atOffset t (hb t ht) 3 := by
      apply Fin.ext
      rw [swapIndex_val_right _ _ _ _ ⟨t, ht, he⟩]
      change (s + 0) - 2 = t + 3
      omega
    have hw₂ : atOffset s (hb s hs) 2 = atOffset t (hb t ht) 7 := by
      apply Fin.ext
      change s + 2 = t + 7
      omega
    rw [hw₀, hw₂]
    obtain ⟨_, hpattern⟩ := hπ t ht
    exact (hpattern 3 7).mpr (by rcases hp with rfl | rfl <;> decide)
  · have hw₀ : swapIndex marks hb hd (atOffset s (hb s hs) 0) =
        atOffset s (hb s hs) 0 := Fin.ext (swapIndex_val_other _ _ _ _ hleft hright)
    rw [hw₀]
    obtain ⟨_, hpattern⟩ := hπ s hs
    exact (hpattern 0 2).mpr (by rcases hp with rfl | rfl <;> decide)

end Implications.WilfPatternSwap
