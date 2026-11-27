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
def occurrenceSet (occurs : α → X → Prop) (x : X)
    [DecidablePred (fun a => occurs a x)] : Finset α :=
  Finset.univ.filter (fun a => occurs a x)

/-- A marked set `M` is present among the occurrences of `x`. -/
def HasMarkedOccurrences (occurs : α → X → Prop) (M : Finset α) (x : X) : Prop :=
  ∀ a ∈ M, occurs a x

/-- The exact set of occurrence starts of `x` is `M`. -/
def HasExactOccurrences (occurs : α → X → Prop) (M : Finset α) (x : X)
    [DecidablePred (fun a => occurs a x)] : Prop :=
  occurrenceSet occurs x = M

end WilfEquivalence

namespace WilfEquivalence

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A bijection for each prescribed marked set gives equal counts for all
permutations containing that set of occurrences. -/
theorem marked_card_eq_of_equiv
    (occX : α → X → Prop) (occY : α → Y → Prop)
    (h : ∀ M : Finset α,
      {x : X // HasMarkedOccurrences occX M x} ≃
        {y : Y // HasMarkedOccurrences occY M y})
    (M : Finset α) :
    Fintype.card {x : X // HasMarkedOccurrences occX M x} =
      Fintype.card {y : Y // HasMarkedOccurrences occY M y} := by
  exact Fintype.card_congr (h M)

end WilfEquivalence
