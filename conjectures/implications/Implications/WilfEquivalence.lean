import Mathlib

/-!
# Marked occurrences and exact occurrence sets

This file isolates the finite counting bridge used for super-strong Wilf
-equivalence. A bijection preserving any prescribed collection of occurrences
proves equality of all superset counts; Boolean-lattice inversion then recovers
equality for permutations with an exact occurrence set.
-/

namespace WilfEquivalence

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The set of starts at which `x` has the designated occurrence. -/
def occurrenceSet (occurs : α → X → Prop) [DecidablePred (fun a => occurs a x)]
    (x : X) : Finset α :=
  Finset.univ.filter (fun a => occurs a x)

/-- A marked set `M` is present among the occurrences of `x`. -/
def HasMarkedOccurrences (occurs : α → X → Prop) (M : Finset α) (x : X) : Prop :=
  ∀ a ∈ M, occurs a x

/-- The exact set of occurrence starts of `x` is `M`. -/
def HasExactOccurrences (occurs : α → X → Prop) (M : Finset α) (x : X) : Prop :=
  occurrenceSet occurs x = M

end WilfEquivalence
