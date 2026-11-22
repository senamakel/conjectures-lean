import Robin.Defs

/-!
# An upper bound for `σ(n)/n` with a free exponent

For every `ε > 0`, `σ(n)/n ≤ n^ε ∏_p max_k (1 + p⁻¹ + ⋯ + p⁻ᵏ) p^{−kε}`
(multiplicativity; this is the bound attained by colossally abundant numbers).
With `ε = ε(x) = log(1+1/x)/log x` only primes `p ≤ x` contribute, and the local maximum is
at most `c_p − ε log p − min(1/p², ε log p)`.
-/

namespace Robin

open ArithmeticFunction Real
open scoped ArithmeticFunction.sigma

theorem log_sigma_div_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 3 ≤ x) :
    Real.log ((σ 1 n : ℝ) / n) ≤
      epsR x * Real.log n + primeSum (fun p => cp p - epsR x * Real.log p) x - gainSum x := by
  sorry

end Robin
