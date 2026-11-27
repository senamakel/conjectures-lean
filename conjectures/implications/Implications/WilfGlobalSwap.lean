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

private theorem left_to_right (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hi : IsLeft marks i) :
    IsRight marks (swapIndex marks hbounded hsep i) := by
  have hleft := hi
  obtain ⟨s, hs, hsi⟩ := hi
  refine ⟨s, hs, ?_⟩
  simp [swapIndex, hleft, hsi]

private theorem right_to_left (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hi : IsRight marks i) :
    IsLeft marks (swapIndex marks hbounded hsep i) := by
  have hright := hi
  obtain ⟨s, hs, hsi⟩ := hi
  have hnot : ¬ IsLeft marks i := by
    intro hleft
    exact no_left_right marks hsep i ⟨hleft, hright⟩
  refine ⟨s, hs, ?_⟩
  simp [swapIndex, hnot, hright, hsi]

theorem swapIndex_involutive (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) :
    Function.Involutive (swapIndex marks hbounded hsep) := by
  classical
  intro i
  apply Fin.ext
  by_cases hleft : IsLeft marks i
  · have hright := left_to_right marks hbounded hsep i hleft
    have hnot : ¬ IsLeft marks (swapIndex marks hbounded hsep i) := by
      intro h
      exact no_left_right marks hsep _ ⟨h, hright⟩
    simp only [swapIndex, dif_pos hleft, dif_neg hnot, Fin.val_mk]
    obtain ⟨s, hs, hsi⟩ := hleft
    omega
  · by_cases hright : IsRight marks i
    · have hleft' := right_to_left marks hbounded hsep i hright
      have hnot : ¬ IsRight marks (swapIndex marks hbounded hsep i) := by
        intro h
        exact no_left_right marks hsep _ ⟨hleft', h⟩
      simp only [swapIndex, dif_neg hleft, dif_pos hright, dif_pos hleft', dif_neg hnot,
        Fin.val_mk]
      obtain ⟨s, hs, hsi⟩ := hright
      omega
    · have hnot' : ¬ IsRight marks (swapIndex marks hbounded hsep i) := by
        simpa [swapIndex, hleft, hright]
      simp [swapIndex, hleft, hright, hnot']

end Implications.WilfGlobalSwap
