import CooksonHills.OfPiExponent
import OAI.NumberTheory.PiExponent.Main

/-!
# The Cookson Hills series converges

The headline theorem. Its statement is `FlintCooksonHills.cookson_hills_series_converges` of
formal-conjectures (`FormalConjectures/Wikipedia/FlintCooksonHills.lean`, commit `9097e2f`),
word for word. The proof discharges `PiEventualLowerBound` with the vendored
`OAI.PiExponent.pi_eventual_lower_bound` (OpenAI's Lean proof that `μ(π) = 2`).
-/

namespace FlintCooksonHills

/-- **The Flint Hills series converges.** formal-conjectures
`FlintCooksonHills.flint_hills_series_converges`, word for word. -/
theorem flint_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.sin (n + 1)^2))) :=
  flint_hills_of_piEventualLowerBound OAI.PiExponent.pi_eventual_lower_bound

/-- **The Cookson Hills series converges.** formal-conjectures
`FlintCooksonHills.cookson_hills_series_converges`, word for word. -/
theorem cookson_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.cos (n + 1)^2))) :=
  cookson_hills_of_piEventualLowerBound OAI.PiExponent.pi_eventual_lower_bound

end FlintCooksonHills
