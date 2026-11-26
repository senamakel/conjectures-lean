import Robin.Defs

/-!
# Robin's inequality in the range `5040 < n ≤ exp(e^{30})` (the statement)

Morrill and Platt (*Robin's inequality for 20-free integers*, Integers 21 (2021), A28;
arXiv:1809.10813, Theorem 13) verified Robin's inequality unconditionally for all
`5040 < n ≤ 10^{10^{13.11485}}`, extending Briggs (Experiment. Math. 15 (2006)), who checked
every colossally abundant number up to `10^{10^{10}}`. Since `e^{30} < 1.07·10^{13}`,
`log n ≤ e^{30}` gives `n ≤ 10^{4.64·10^{12}}`, well inside that range.

This file only states the range as the proposition `RobinVerifiedRange`. The analytic theorems
(`Robin/Main.lean`) take it as an explicit hypothesis; `Robin.robin_verified_range`
(`Robin/Verified.lean`) proves it by the verified computation in `Robin/Compute/`. Nothing here
is proved by `sorry`.
-/

namespace Robin

open ArithmeticFunction Real
open scoped ArithmeticFunction.sigma

/-- Robin's inequality on the range verified by computation: `5040 < n` with `log n ≤ e^{30}`. -/
def RobinVerifiedRange : Prop :=
  ∀ n : ℕ, 5040 < n → Real.log n ≤ Real.exp 30 →
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

end Robin
