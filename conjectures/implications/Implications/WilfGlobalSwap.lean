import Mathlib

/-! The simultaneous position transposition for separated marked windows. -/

namespace Implications.WilfGlobalSwap

variable {n : Nat}

/-- The left endpoint is at zero-based offset three or four. -/
abbrev LeftOffset := {i : Nat // 3 ≤ i ∧ i < 5}

def fourthOffset : LeftOffset := ⟨3, by decide⟩
def fifthOffset : LeftOffset := ⟨4, by decide⟩


/-- A position is the left endpoint of one of the marked transpositions. -/
def IsLeftAt (left : LeftOffset) (marks : Finset Nat) (i : Fin n) : Prop :=
  ∃ s, s ∈ marks ∧ i.val = s + left.val

/-- A position is the right endpoint of one of the marked transpositions. -/
def IsRight (marks : Finset Nat) (i : Fin n) : Prop :=
  ∃ s, s ∈ marks ∧ i.val = s + 5

private theorem no_left_right (left : LeftOffset) (marks : Finset Nat)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) : ¬ (IsLeftAt left marks i ∧ IsRight marks i) := by
  have hl := left.property
  rintro ⟨⟨s, hs, hsi⟩, ⟨t, ht, hti⟩⟩
  have hst : s < t ∨ t < s ∨ s = t := by omega
  rcases hst with hst | hts | rfl
  · have := hsep s hs t ht hst
    omega
  · have := hsep t ht s hs hts
    omega
  · omega

/-- Exchange positions `s + left` and `s + 5` for all separated marked starts. -/
noncomputable def swapIndexAt (left : LeftOffset) (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) : Fin n → Fin n := by
  classical
  have hl := left.property
  intro i
  by_cases hleft : IsLeftAt left marks i
  · have hout : i.val + (5 - left.val) < n := by
      rcases hleft with ⟨s, hs, hsi⟩
      have := hbounded s hs
      omega
    exact ⟨i.val + (5 - left.val), hout⟩
  · by_cases hright : IsRight marks i
    · have hout : i.val - (5 - left.val) < n := by omega
      exact ⟨i.val - (5 - left.val), hout⟩
    · exact i

theorem swapIndexAt_val_left (left : LeftOffset) (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hi : IsLeftAt left marks i) :
    (swapIndexAt left marks hbounded hsep i).val = i.val + (5 - left.val) := by
  simp [swapIndexAt, hi]

theorem swapIndexAt_val_right (left : LeftOffset) (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hi : IsRight marks i) :
    (swapIndexAt left marks hbounded hsep i).val = i.val - (5 - left.val) := by
  have hright := hi
  have hnot : ¬ IsLeftAt left marks i := by
    intro hleft
    exact no_left_right left marks hsep i ⟨hleft, hright⟩
  simp [swapIndexAt, hnot, hright]

theorem swapIndexAt_val_other (left : LeftOffset) (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (i : Fin n) (hleft : ¬ IsLeftAt left marks i) (hright : ¬ IsRight marks i) :
    (swapIndexAt left marks hbounded hsep i).val = i.val := by
  simp [swapIndexAt, hleft, hright]

theorem swapIndexAt_involutive (left : LeftOffset) (marks : Finset Nat)
    (hbounded : ∀ s ∈ marks, s + 7 < n)
    (hsep : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) :
    Function.Involutive (swapIndexAt left marks hbounded hsep) := by
  classical
  have hl := left.property
  intro i
  apply Fin.ext
  by_cases hleft : IsLeftAt left marks i
  · have hright : IsRight marks (swapIndexAt left marks hbounded hsep i) := by
      have hleft0 := hleft
      obtain ⟨s, hs, hsi⟩ := hleft
      refine ⟨s, hs, ?_⟩
      have hv := swapIndexAt_val_left left marks hbounded hsep i hleft0
      rw [hv]
      omega
    have hnot : ¬ IsLeftAt left marks (swapIndexAt left marks hbounded hsep i) := by
      intro h
      exact no_left_right left marks hsep _ ⟨h, hright⟩
    have hval := swapIndexAt_val_right left marks hbounded hsep _ hright
    rw [hval, swapIndexAt_val_left left marks hbounded hsep i hleft]
    obtain ⟨s, hs, hsi⟩ := hleft
    omega
  · by_cases hright : IsRight marks i
    · have hleft' : IsLeftAt left marks (swapIndexAt left marks hbounded hsep i) := by
        have hright0 := hright
        obtain ⟨s, hs, hsi⟩ := hright
        refine ⟨s, hs, ?_⟩
        have hv := swapIndexAt_val_right left marks hbounded hsep i hright0
        rw [hv]
        omega
      have hnot : ¬ IsRight marks (swapIndexAt left marks hbounded hsep i) := by
        intro h
        exact no_left_right left marks hsep _ ⟨hleft', h⟩
      have hval := swapIndexAt_val_left left marks hbounded hsep _ hleft'
      rw [hval, swapIndexAt_val_right left marks hbounded hsep i hright]
      obtain ⟨s, hs, hsi⟩ := hright
      omega
    · have hnot' : ¬ IsRight marks (swapIndexAt left marks hbounded hsep i) := by
        simpa [swapIndexAt, hleft, hright]
      have hnotL' : ¬ IsLeftAt left marks (swapIndexAt left marks hbounded hsep i) := by
        intro hh
        have hv := swapIndexAt_val_other left marks hbounded hsep i hleft hright
        obtain ⟨s, hs, hsi⟩ := hh
        rw [hv] at hsi
        exact hleft ⟨s, hs, hsi⟩
      have hval := swapIndexAt_val_other left marks hbounded hsep i hleft hright
      rw [swapIndexAt_val_other left marks hbounded hsep _ hnotL' hnot', hval]

abbrev IsLeft := @IsLeftAt n fourthOffset
noncomputable abbrev swapIndex := @swapIndexAt n fourthOffset
abbrev swapIndex_val_left := @swapIndexAt_val_left n fourthOffset
abbrev swapIndex_val_right := @swapIndexAt_val_right n fourthOffset
abbrev swapIndex_val_other := @swapIndexAt_val_other n fourthOffset
abbrev swapIndex_involutive := @swapIndexAt_involutive n fourthOffset

end Implications.WilfGlobalSwap
