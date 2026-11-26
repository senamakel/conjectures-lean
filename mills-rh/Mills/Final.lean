import Mills.Main
import Mills.Cubes

/-! # Mills' constant under RH alone (tier C) -/

namespace Mills

/-- **Mills' constant under RH** (Caldwell–Cheng 2005): the formal-conjectures statement
`Mills.lower_bound_of_RH`, with Mathlib's `RiemannHypothesis`. -/
theorem lower_bound_of_RH : LowerBoundOfRH :=
  lowerBoundOfRH_of_primeBetweenCubes (x₀ := 10 ^ 9) (by norm_num) primeBetweenCubes_of_RH

/-- The enclosure in the form of the formal-conjectures statement, spelled out. -/
theorem mills_bounds_of_RH (hRH : RiemannHypothesis) {A : ℝ} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 :=
  lower_bound_of_RH hRH hA

end Mills
