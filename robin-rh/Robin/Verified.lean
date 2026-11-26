import Robin.Main
import Robin.Lagarias
import Robin.Compute.Range

/-!
# Robin's and Lagarias's inequalities from RH, with the finite range proved

`Robin.robin_verified_range : RobinVerifiedRange` is proved by the verified computation in
`Robin/Compute/` (no hypotheses; standard axioms plus the documented `native_decide`s).
-/

namespace Robin

/-- Robin's inequality for `5040 < n`, `log n ≤ e^{30}`, unconditionally. -/
theorem robin_verified_range : RobinVerifiedRange := Compute.robinVerifiedRange_proved

/-- **Robin's theorem** (1984): RH implies `σ(n) < e^γ n log log n` for every `n > 5040`. -/
theorem robin_of_RH (hRH : RiemannHypothesis) : RobinStatement :=
  robin_of_RH_of_verified hRH robin_verified_range

/-- **Lagarias's inequality** under RH: `σ(n) ≤ H_n + exp(H_n) log H_n` for every `n ≥ 1`. -/
theorem lagarias_of_RH (hRH : RiemannHypothesis) : LagariasStatement :=
  lagarias_of_RH_of_verified hRH robin_verified_range

end Robin
