import Mathlib

/-!
# Catlin's graph `C₅[K₃]` and its chromatic number

The lexicographic product of the 5-cycle with the triangle: vertices `(i, a) : Fin 5 × Fin 3`,
with `(i, a) ~ (j, b)` when `i = j` and `a ≠ b`, or when `j = i ± 1` in `ℤ/5`. Column `i` is the
set of vertices with first coordinate `i`.

Every three vertices contain an adjacent pair (independence number 2), so a colour class has at
most two vertices and a proper colouring needs at least `⌈15/2⌉ = 8` colours.
-/

open SimpleGraph

namespace HajosCatlin

/-- Adjacency in `C₅[K₃]`. -/
def catlinAdj (x y : Fin 5 × Fin 3) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ y.1 = x.1 + 1 ∨ x.1 = y.1 + 1

instance : DecidableRel catlinAdj := fun x y => by unfold catlinAdj; infer_instance

private lemma fin5_ne_succ : ∀ i : Fin 5, i ≠ i + 1 := by decide

/-- Catlin's graph `C₅[K₃]`. -/
def catlin : SimpleGraph (Fin 5 × Fin 3) where
  Adj := catlinAdj
  symm := by
    refine ⟨fun x y h => ?_⟩
    unfold catlinAdj at *
    rcases h with ⟨h1, h2⟩ | h | h
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    refine ⟨fun x h => ?_⟩
    unfold catlinAdj at h
    rcases h with ⟨_, h⟩ | h | h
    · exact h rfl
    · exact fin5_ne_succ _ h.symm
    · exact fin5_ne_succ _ h

instance : DecidableRel catlin.Adj := inferInstanceAs (DecidableRel catlinAdj)

/-- Among any three distinct vertices of `C₅[K₃]` two are adjacent. -/
theorem catlin_indep_three : ∀ x y z : Fin 5 × Fin 3, x ≠ y → x ≠ z → y ≠ z →
    catlin.Adj x y ∨ catlin.Adj x z ∨ catlin.Adj y z := by
  decide

/-- `χ(C₅[K₃]) ≥ 8`. -/
theorem eight_le_chromaticNumber : (8 : ℕ∞) ≤ catlin.chromaticNumber := by
  by_contra hlt
  push Not at hlt
  have h7 : catlin.chromaticNumber ≤ (7 : ℕ) := by
    have : catlin.chromaticNumber < (7 : ℕ∞) + 1 := hlt
    exact Order.le_of_lt_add_one this
  obtain ⟨C⟩ := chromaticNumber_le_iff_colorable.mp h7
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := C) (n := 2)
    (by simp)
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  rcases catlin_indep_three x y z hxy hxz hyz with h | h | h
  · exact C.valid h (hx.trans hy.symm)
  · exact C.valid h (hx.trans hz.symm)
  · exact C.valid h (hy.trans hz.symm)

end HajosCatlin
