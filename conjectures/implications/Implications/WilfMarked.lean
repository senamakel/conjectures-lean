import Mathlib

/-!
# Marked-window bijection for the patterns 16237485 and 16247385

The input is a permutation of an arbitrary finite interval, together with a set of
marked starting positions.  `ContainsAt` records classical pattern containment by
preservation of all pairwise comparisons in the window.
-/

namespace WilfMarked

/-- The two length-eight patterns, encoded by their ranks. -/
def sigma : Fin 8 → Fin 8 := ![0, 5, 1, 2, 6, 3, 7, 4]
def tau : Fin 8 → Fin 8 := ![0, 5, 1, 3, 6, 2, 7, 4]

/-- The adjacent transposition of the fourth and sixth positions. -/
def windowSwap (i : Fin 8) : Fin 8 :=
  if i = 3 then 5 else if i = 5 then 3 else i

theorem windowSwap_involutive : Function.Involutive windowSwap := by
  intro i
  fin_cases i <;> rfl

theorem windowSwap_sigma : sigma ∘ windowSwap = tau := by
  funext i
  fin_cases i <;> rfl

theorem windowSwap_tau : tau ∘ windowSwap = sigma := by
  funext i
  fin_cases i <;> rfl

/-- A window at `s` is the indicated pattern when its values have the same
strict-order comparisons as the pattern. The bound is expressed on the final
index, so this works for any finite ambient permutation. -/
def ContainsAt {n : Nat} (π : Equiv.Perm (Fin n)) (s : Nat)
    (p : Fin 8 → Fin 8) : Prop :=
  ∃ h : s + 7 < n, ∀ i j : Fin 8,
    (π ⟨s + i.val, by
      have hi : i.val ≤ 7 := Nat.le_of_lt_succ i.isLt
      omega⟩ < π ⟨s + j.val, by
      have hj : j.val ≤ 7 := Nat.le_of_lt_succ j.isLt
      omega⟩) ↔ p i < p j

end WilfMarked

namespace WilfMarked

#print axioms windowSwap_involutive
#print axioms windowSwap_sigma
#print axioms windowSwap_tau

end WilfMarked
