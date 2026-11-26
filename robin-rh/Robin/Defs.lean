import Mathlib

/-!
# Shared definitions for the proof of Robin's theorem

* `psi1 t = Σ_{n ≤ t} Λ(n) (t − n) = ∫₀ᵗ ψ`, the integrated Chebyshev function;
* `cp p = −log(1 − 1/p)`, the local factor of Mertens' product;
* `primeSum f x = Σ_{p ≤ x, p prime} f p`;
* `epsR x = log(1 + 1/x) / log x`, the exponent used to bound `σ(n)/n` when `log n = x`;
* `gainSum x = Σ_{p ≤ x} min(1/p², ε log p)`;
* `wM t = (1 + log t)/(t² log² t) = −(d/dt) 1/(t log t)`, the Mertens weight.
-/

namespace Robin

open ArithmeticFunction Real

/-- `Ψ₁(t) = Σ_{n ≤ t} Λ(n)(t − n)`. -/
noncomputable def psi1 (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * (t - n)

/-- `c_p = −log(1 − 1/p)`. -/
noncomputable def cp (p : ℕ) : ℝ := -Real.log (1 - 1 / (p : ℝ))

/-- `Σ_{p ≤ x} f(p)` over primes. -/
noncomputable def primeSum (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Iic ⌊x⌋₊ with p.Prime, f p

/-- The exponent `ε(x) = log(1 + 1/x)/log x`. -/
noncomputable def epsR (x : ℝ) : ℝ := Real.log (1 + 1 / x) / Real.log x

/-- The gain `Σ_{p ≤ x} min(1/p², ε(x) log p)` coming from the prime-power structure. -/
noncomputable def gainSum (x : ℝ) : ℝ :=
  primeSum (fun p => min (1 / (p : ℝ) ^ 2) (epsR x * Real.log p)) x

/-- Mertens weight `w(t) = (1 + log t)/(t² log² t)`. -/
noncomputable def wM (t : ℝ) : ℝ := (1 + Real.log t) / (t ^ 2 * Real.log t ^ 2)

end Robin
