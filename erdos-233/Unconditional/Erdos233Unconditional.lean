import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Erdos233

/-!
# Selberg's bound for Erdős 233, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.

This is `erdos_233.variants.upper_bound` of formal-conjectures (`Σ_{n<N} d_n² ≪ N log⁴ N`),
not the open conjecture `erdos_233` (`≪ N log² N`).
-/

theorem erdos_233_upper_bound : Erdos233.Erdos233UpperBoundStatement :=
  Erdos233.erdos_233_upper_bound_of_RH riemannHypothesis

#print axioms erdos_233_upper_bound

/-- Selberg 1943 (existence form): almost all intervals `(x, x + h(x)]` with
`h(x) / log² x → ∞` contain a prime, given the riemann-hypothesis repository's RH. -/
theorem selberg_almost_all : Erdos233.SelbergAlmostAllStatement :=
  Erdos233.selberg_almost_all_of_RH riemannHypothesis

/-- Selberg 1943 (asymptotic form): `π(x + h) − π(x) ~ h / log x` for almost all `x ∈ [X, 2X]`,
whenever `h(x)/log² x → ∞` and `h(x) = o(x)`, given the riemann-hypothesis repository's RH. -/
theorem selberg_asymptotic : Erdos233.SelbergAsymptoticStatement :=
  Erdos233.selberg_asymptotic_of_RH riemannHypothesis

/-- The smoothed form of Selberg's asymptotic. -/
theorem smoothed_selberg_asymptotic : Erdos233.SmoothedSelbergStatement :=
  Erdos233.smoothed_asymptotic_of_RH riemannHypothesis

/-- Large gaps: `Σ_{X ≤ p_n < 2X, d_n ≥ h} d_n ≪ X log² X / h`. -/
theorem large_gaps : ∃ C X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
    ∀ h : ℝ, 256 * (Real.log (5 * x) ^ 2 / Real.log 2) ≤ h → h ≤ 2 * x →
    ∑ n ∈ (Erdos233.block x).filter (fun n => h ≤ primeGap n), (primeGap n : ℝ)
      ≤ C * x * Real.log x ^ 2 / h :=
  Erdos233.large_gaps_of_RH riemannHypothesis

#print axioms selberg_almost_all
#print axioms selberg_asymptotic
#print axioms smoothed_selberg_asymptotic
#print axioms large_gaps
