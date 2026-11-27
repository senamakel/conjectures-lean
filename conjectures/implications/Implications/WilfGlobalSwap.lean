import Mathlib

/-! A transposition of two positions in an ambient finite permutation. -/

namespace Implications.WilfGlobalSwap

/-- Exchange positions `s + 3` and `s + 5`, fixing every other position. -/
def swapIndex {n : Nat} (s : Nat) (hs : s + 7 < n) : Fin n → Fin n := fun i =>
  if i.val = s + 3 then ⟨s + 5, by omega⟩
  else if i.val = s + 5 then ⟨s + 3, by omega⟩
  else i

theorem swapIndex_involutive {n : Nat} (s : Nat) (hs : s + 7 < n) :
    Function.Involutive (swapIndex s hs) := by
  intro i
  apply Fin.ext
  simp only [swapIndex]
  by_cases h₁ : i.val = s + 3
  · simp [h₁]
  · by_cases h₂ : i.val = s + 5
    · simp [h₁, h₂]
    · simp [h₁, h₂]

@[simp] theorem swapIndex_left {n : Nat} (s : Nat) (hs : s + 7 < n) :
    (swapIndex s hs ⟨s + 3, by omega⟩ : Fin n) = ⟨s + 5, by omega⟩ := by
  apply Fin.ext
  simp [swapIndex]

@[simp] theorem swapIndex_right {n : Nat} (s : Nat) (hs : s + 7 < n) :
    (swapIndex s hs ⟨s + 5, by omega⟩ : Fin n) = ⟨s + 3, by omega⟩ := by
  apply Fin.ext
  simp [swapIndex]

end Implications.WilfGlobalSwap
