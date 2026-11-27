import Implications.WilfCounts

/-!
# From marked-occurrence bijections to exact occurrence sets

A bijection for every prescribed collection of starts gives equality of all
upper-cone counts. Finite Boolean-lattice inversion then gives equality for
permutations with each exact set of occurrence starts.
-/

namespace Implications.WilfEquivalence

open WilfCounts

variable {α X Y : Type*} [Fintype α] [DecidableEq α]
variable [Fintype X] [Fintype Y]

/-- A bijection between the objects satisfying any given marked set of
occurrences induces equal marked counts. -/
theorem markedCount_eq_of_markedEquiv
    (occX : X → Finset α) (occY : Y → Finset α)
    (h : ∀ marks : Finset α,
      {x : X // marks ⊆ occX x} ≃ {y : Y // marks ⊆ occY y})
    (marks : Finset α) :
    markedCount occX marks = markedCount occY marks := by
  classical
  unfold markedCount
  simpa only [Finset.card_eq_card_subtype] using Fintype.card_congr (h marks)

/-- Marked-occurrence bijections imply super-strong equivalence: every exact
occurrence set has the same number of objects on both sides. -/
theorem exactCount_eq_of_markedEquiv
    (occX : X → Finset α) (occY : Y → Finset α)
    (h : ∀ marks : Finset α,
      {x : X // marks ⊆ occX x} ≃ {y : Y // marks ⊆ occY y})
    (exactStarts : Finset α) :
    exactCount occX exactStarts = exactCount occY exactStarts := by
  apply exactCount_eq_of_markedCount_eq occX occY
  intro marks
  exact markedCount_eq_of_markedEquiv occX occY h marks

end Implications.WilfEquivalence
