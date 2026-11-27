import Mathlib

/-! The simultaneous position transposition for separated marked windows. -/

namespace Implications.WilfGlobalSwap

variable {n : Nat}

/-- A position is the left endpoint of one of the marked transpositions. -/
def IsLeft (marks : Finset Nat) (i : Fin n) : Prop :=
  ∃ s, s ∈ marks ∧ i.val = s + 3

/-- A position is the right endpoint of one of the marked transpositions. -/
def IsRight (marks : Finset Nat) (i : Fin n) : Prop :=
  ∃ s, s ∈ marks ∧ i.val = s + 5

private theorem no_left_right (marks : Finset Nat)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) : ¬ (IsLeft marks i ∧ IsRight marks i) := by
  rintro ⟨⟨s, hs, hsi⟩, ⟨t, ht, hti⟩⟩
  have hst : s < t ∨ t < s ∨ s = t := by omega
  rcases hst with hst | hts | rfl
  · have := hsep s hs t ht hst
    omega
  · have := hsep t ht s hs hts
    omega
  · omega

/-- Exchange positions `s + 3` and `s + 5` for all separated marked starts. -/
noncomputable def swapIndex (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) : Fin n → Fin n := by
  classical
  intro i
  by_cases hleft : IsLeft marks i
  · have hout : i.val + 2 < n := by
      rcases hleft with ⟨s, hs, hsi⟩
      have := hbounded s hs
      omega
    exact ⟨i.val + 2, hout⟩
  · by_cases hright : IsRight marks i
    · have hout : i.val - 2 < n := by omega
      exact ⟨i.val - 2, hout⟩
    · exact i

theorem swapIndex_val_left (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hi : IsLeft marks i) :
    (swapIndex marks hbounded hsep i).val = i.val + 2 := by
  simp [swapIndex, hi]

theorem swapIndex_val_right (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hi : IsRight marks i) :
    (swapIndex marks hbounded hsep i).val = i.val - 2 := by
  have hright := hi
  have hnot : ¬ IsLeft marks i := by
    intro hleft
    exact no_left_right marks hsep i ⟨hleft, hright⟩
  simp [swapIndex, hnot, hright]

theorem swapIndex_val_other (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hleft : ¬ IsLeft marks i) (hright : ¬ IsRight marks i) :
    (swapIndex marks hbounded hsep i).val = i.val := by
  simp [swapIndex, hleft, hright]

theorem swapIndex_involutive (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) :
    Function.Involutive (swapIndex marks hbounded hsep) := by
  classical
  intro i
  apply Fin.ext
  by_cases hleft : IsLeft marks i
  · have hright : IsRight marks (swapIndex marks hbounded hsep i) := by
      have hleft0 := hleft
      obtain ⟨s, hs, hsi⟩ := hleft
      refine ⟨s, hs, ?_⟩
      have hv := swapIndex_val_left marks hbounded hsep i hleft0
      simpa [hv] using hsi
    have hnot : ¬ IsLeft marks (swapIndex marks hbounded hsep i) := by
      intro h
      exact no_left_right marks hsep _ ⟨h, hright⟩
    have hval := swapIndex_val_right marks hbounded hsep _ hright
    rw [hval, swapIndex_val_left marks hbounded hsep i hleft]
    obtain ⟨s, hs, hsi⟩ := hleft
    omega
  · by_cases hright : IsRight marks i
    · have hleft' : IsLeft marks (swapIndex marks hbounded hsep i) := by
        have hright0 := hright
        obtain ⟨s, hs, hsi⟩ := hright
        refine ⟨s, hs, ?_⟩
        have hv := swapIndex_val_right marks hbounded hsep i hright0
        rw [hv]
        omega
      have hnot : ¬ IsRight marks (swapIndex marks hbounded hsep i) := by
        intro h
        exact no_left_right marks hsep _ ⟨hleft', h⟩
      have hval := swapIndex_val_left marks hbounded hsep _ hleft'
      rw [hval, swapIndex_val_right marks hbounded hsep i hright]
      obtain ⟨s, hs, hsi⟩ := hright
      omega
    · have hnot' : ¬ IsRight marks (swapIndex marks hbounded hsep i) := by
        simpa [swapIndex, hleft, hright]
      have hnotL' : ¬ IsLeft marks (swapIndex marks hbounded hsep i) := by
        intro hh
        have hv := swapIndex_val_other marks hbounded hsep i hleft hright
        obtain ⟨s, hs, hsi⟩ := hh
        rw [hv] at hsi
        exact hleft ⟨s, hs, hsi⟩
      have hval := swapIndex_val_other marks hbounded hsep i hleft hright
      rw [swapIndex_val_other marks hbounded hsep _ hnotL' hnot', hval]

end Implications.WilfGlobalSwap
