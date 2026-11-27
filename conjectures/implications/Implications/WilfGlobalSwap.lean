import Mathlib

/-!
# Global position swap for separated marked windows

For each marked start `s`, exchange the ambient positions `s + 3` and `s + 5`.
The spacing hypothesis makes these transpositions pairwise disjoint.
-/

namespace Implications.WilfGlobalSwap

variable {n : Nat}

/-- The simultaneous exchange of positions `s+3` and `s+5` for every marked start. -/
noncomputable def swapIndex (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n) : Fin n → Fin n := by
  classical
  intro i
  by_cases hleft : ∃ s, s ∈ marks ∧ i.val = s + 3
  · let s := Classical.choose hleft
    have hs : s ∈ marks ∧ i.val = s + 3 := Classical.choose_spec hleft
    exact ⟨s + 5, by have := hbounded s hs.1; omega⟩
  · by_cases hright : ∃ s, s ∈ marks ∧ i.val = s + 5
    · let s := Classical.choose hright
      have hs : s ∈ marks ∧ i.val = s + 5 := Classical.choose_spec hright
      exact ⟨s + 3, by have := hbounded s hs.1; omega⟩
    · exact i

theorem swapIndex_involutive (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) :
    Function.Involutive (swapIndex marks hbounded) := by
  classical
  intro i
  apply Fin.ext
  simp only [swapIndex]
  split
  · rename_i hleft
    let s := Classical.choose hleft
    have hs : s ∈ marks ∧ i.val = s + 3 := Classical.choose_spec hleft
    simp only [dif_pos hleft]
    have hnext : ∃ t, t ∈ marks ∧ (⟨s + 5, by have := hbounded s hs.1; omega⟩ : Fin n).val = t + 5 :=
      ⟨s, hs.1, rfl⟩
    simp only [dif_neg (show ¬ ∃ t, t ∈ marks ∧ (⟨s + 5, by have := hbounded s hs.1; omega⟩ : Fin n).val = t + 3 from by
      rintro ⟨t, ht, heq⟩
      have hst : s < t ∨ t < s ∨ t = s := by omega
      rcases hst with hst | hts | rfl
      · have := hsep s hs.1 t ht hst
        omega
      · have := hsep t ht s hs.1 hts
        omega
      · omega]), dif_pos hnext]
    simp [s, hs.2]
  · rename_i hleft
    simp only [dif_neg hleft]
    split
    · rename_i hright
      let s := Classical.choose hright
      have hs : s ∈ marks ∧ i.val = s + 5 := Classical.choose_spec hright
      simp only [dif_pos hright]
      have hnext : ∃ t, t ∈ marks ∧ (⟨s + 3, by have := hbounded s hs.1; omega⟩ : Fin n).val = t + 3 :=
        ⟨s, hs.1, rfl⟩
      have hnot : ¬ ∃ t, t ∈ marks ∧ (⟨s + 3, by have := hbounded s hs.1; omega⟩ : Fin n).val = t + 5 := by
        rintro ⟨t, ht, heq⟩
        have hst : s < t ∨ t < s ∨ t = s := by omega
        rcases hst with hst | hts | rfl
        · have := hsep s hs.1 t ht hst
          omega
        · have := hsep t ht s hs.1 hts
          omega
        · omega
      simp only [dif_pos hnext, dif_neg hnot]
      simp [s, hs.2]
    · rename_i hright
      simp only [dif_neg hright]
      rfl

end Implications.WilfGlobalSwap
