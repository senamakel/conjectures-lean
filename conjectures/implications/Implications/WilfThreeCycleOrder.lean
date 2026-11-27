import Implications.WilfTwoWindowOrder

/-! The critical right-overlap comparisons for the cycle in 23145786 and 25134786. -/

namespace Implications.WilfThreeCycleOrder

open WilfTwoWindowOrder

def pattern23145786 : Fin 8 → Fin 8 := ![1, 2, 0, 3, 4, 6, 7, 5]

def pattern25134786 : Fin 8 → Fin 8 := ![1, 4, 0, 2, 3, 6, 7, 5]

/-- Source offsets after moving ranks at positions two, four and five. -/
def cycle : Equiv.Perm (Fin 8) :=
  (Equiv.swap 1 3).trans (Equiv.swap 3 4)

/-- The later window moves its offset one, replacing offset six in the first
window. Other positions of the first window use its own source offsets. -/
def overlapImage (m : Equiv.Perm (Fin 8)) (i : Fin 8) : Fin 13 :=
  if i = 6 then position 5 (m 1) else position 0 (m i)

private theorem less_iff_rank_lt {α : Type*} [Preorder α] {p : Fin 8 → Fin 8}
    (hinj : Function.Injective p) {f : Fin 13 → α} (hf : WindowOrder p f 0)
    (i j : Fin 8) : f (position 0 i) < f (position 0 j) ↔ p i < p j := by
  refine ⟨fun h => ?_, hf i j⟩
  rcases lt_trichotomy (p i) (p j) with hlt | heq | hgt
  · exact hlt
  · have hij := hinj heq
    subst j
    exact (lt_irrefl _ h).elim
  · exact (not_lt_of_gt (hf j i hgt) h).elim

/-- If the right overlap replaces the greatest entry with a value at least
as large as the second greatest, all central rank comparisons are preserved. -/
theorem overlap_cycle_order {α : Type*} [Preorder α]
    (p : Fin 8 → Fin 8) (m : Equiv.Perm (Fin 8)) (hinj : Function.Injective p)
    (hfix : m 6 = 6) (hmax : ∀ i : Fin 8, i ≠ 6 → p i < p 6)
    (hsecond : ∀ i : Fin 8, i ≠ 6 → i ≠ 5 → p i < p 5)
    (hcross : p 0 < p (m 1)) (f : Fin 13 → α)
    (hfirst : WindowOrder p f 0) (hnext : WindowOrder p f 5) (i j : Fin 8) :
    f (overlapImage m i) < f (overlapImage m j) ↔ p (m i) < p (m j) := by
  have hreplacement : f (position 0 5) < f (position 5 (m 1)) := hnext 0 (m 1) hcross
  have hne6 (k : Fin 8) (hk : k ≠ 6) : m k ≠ 6 := fun he => hk (m.injective (he.trans hfix.symm))
  have hlt (k : Fin 8) (hk : k ≠ 6) :
      f (position 0 (m k)) < f (position 5 (m 1)) := by
    by_cases h5 : m k = 5
    · simpa [h5] using hreplacement
    · exact (hfirst _ _ (hsecond _ (hne6 k hk) h5)).trans hreplacement
  by_cases hi : i = 6
  · subst i
    by_cases hj : j = 6
    · subst j; simp
    · simp only [overlapImage, if_pos rfl, if_neg hj, hfix]
      exact iff_of_false (not_lt_of_gt (hlt j hj)) (not_lt_of_gt (hmax _ (hne6 j hj)))
  · by_cases hj : j = 6
    · subst j
      simp only [overlapImage, if_neg hi, if_pos rfl, hfix]
      exact iff_of_true (hlt i hi) (hmax _ (hne6 i hi))
    · simp only [overlapImage, if_neg hi, if_neg hj]
      exact less_iff_rank_lt hinj hfirst (m i) (m j)

/-- The two-window comparison certificate in the forward direction. -/
theorem overlap_order_23145786_25134786 {α : Type*} [Preorder α] (f : Fin 13 → α)
    (hf : WindowOrder pattern23145786 f 0) (hn : WindowOrder pattern23145786 f 5) (i j : Fin 8) :
    f (overlapImage cycle i) < f (overlapImage cycle j) ↔
      pattern25134786 i < pattern25134786 j := by
  have hp : pattern23145786 ∘ cycle = pattern25134786 := by funext k; fin_cases k <;> rfl
  rw [← hp]
  exact overlap_cycle_order pattern23145786 cycle (by decide) (by decide)
    (by decide) (by decide) (by decide) f hf hn i j

/-- The two-window comparison certificate for the inverse cycle. -/
theorem overlap_order_25134786_23145786 {α : Type*} [Preorder α] (f : Fin 13 → α)
    (hf : WindowOrder pattern25134786 f 0) (hn : WindowOrder pattern25134786 f 5) (i j : Fin 8) :
    f (overlapImage cycle.symm i) < f (overlapImage cycle.symm j) ↔
      pattern23145786 i < pattern23145786 j := by
  have hp : pattern25134786 ∘ cycle.symm = pattern23145786 := by funext k; fin_cases k <;> rfl
  rw [← hp]
  exact overlap_cycle_order pattern25134786 cycle.symm (by decide) (by decide)
    (by decide) (by decide) (by decide) f hf hn i j

#print axioms overlap_order_23145786_25134786
#print axioms overlap_order_25134786_23145786

end Implications.WilfThreeCycleOrder
