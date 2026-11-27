import Mathlib

/-! Rank comparisons for the two-window swap of 23157684 and 23167584. -/

namespace Implications.WilfTwoWindowOrder

def pattern23157684 : Fin 8 → Fin 8 := ![1, 2, 0, 4, 6, 5, 7, 3]

def pattern23167584 : Fin 8 → Fin 8 := ![1, 2, 0, 5, 6, 4, 7, 3]

/-- Position of an offset in the thirteen-place union of two windows. -/
def position (start : Fin 6) (offset : Fin 8) : Fin 13 :=
  ⟨start.val + offset.val, by have := start.isLt; have := offset.isLt; omega⟩

/-- The strict order constraints imposed by one occurrence. -/
def WindowOrder {α : Type*} [LT α] (p : Fin 8 → Fin 8) (f : Fin 13 → α)
    (start : Fin 6) : Prop :=
  ∀ i j : Fin 8, p i < p j → f (position start i) < f (position start j)

/-- In two copies of 23157684 at shift five, moving offset three to the second
window's first position preserves its comparisons with all other entries. -/
theorem replacement_order_23157684 {α : Type*} [Preorder α] (f : Fin 13 → α)
    (hfirst : WindowOrder pattern23157684 f 0) (hsecond : WindowOrder pattern23157684 f 5)
    (j : Fin 8) (hj : j ≠ 0) :
    f 3 < f (position 5 j) ↔ pattern23157684 0 < pattern23157684 j := by
  have haf : f 3 < f 5 := hfirst 3 5 (by decide)
  fin_cases j
  · exact (hj rfl).elim
  · exact iff_of_true (hfirst 3 6 (by decide)) (by decide)
  · exact iff_of_false (not_lt_of_gt (hfirst 7 3 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 0 3 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 0 4 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 0 5 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 0 6 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 0 7 (by decide))) (by decide)

/-- The reverse swap uses the shared position six as its comparison witness. -/
theorem replacement_order_23167584 {α : Type*} [Preorder α] (f : Fin 13 → α)
    (hfirst : WindowOrder pattern23167584 f 0) (hsecond : WindowOrder pattern23167584 f 5)
    (j : Fin 8) (hj : j ≠ 0) :
    f 3 < f (position 5 j) ↔ pattern23167584 0 < pattern23167584 j := by
  have haf : f 3 < f 6 := hfirst 3 6 (by decide)
  fin_cases j
  · exact (hj rfl).elim
  · exact iff_of_true haf (by decide)
  · exact iff_of_false (not_lt_of_gt (hfirst 7 3 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 1 3 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 1 4 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 1 5 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 1 6 (by decide))) (by decide)
  · exact iff_of_true (haf.trans (hsecond 1 7 (by decide))) (by decide)

#print axioms replacement_order_23157684
#print axioms replacement_order_23167584

end Implications.WilfTwoWindowOrder
