import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Cramer

/-!
# Cramér's prime-gap theorem, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem cramer_primeInShortInterval : Cramer.PrimeInShortInterval 2 :=
  Cramer.primeInShortInterval_of_RH riemannHypothesis

theorem cramer_primeGapExplicit : Cramer.PrimeGapExplicit 2 :=
  Cramer.primeGapExplicit_of_RH riemannHypothesis

theorem cramer_gapBound : Cramer.CramerGapBound :=
  Cramer.cramer_of_RH riemannHypothesis

/-- Cramér (1922), dyadic form: `∫_X^{2X} (ψ(x) − x)² dx = O(X²)`. -/
theorem cramer_dyadicMeanSquare : Cramer.CramerDyadicMeanSquare :=
  Cramer.dyadicMeanSquare_of_RH riemannHypothesis

/-- Cramér (1922): `∫_1^X (ψ(x) − x)² dx = O(X²)`. -/
theorem cramer_meanSquare : Cramer.CramerMeanSquare :=
  Cramer.meanSquare_of_RH riemannHypothesis

/-- `∫_1^X ((ψ(x) − x)/x)² dx = O(log X)`. -/
theorem cramer_logMeanSquare : Cramer.CramerLogMeanSquare :=
  Cramer.logMeanSquare_of_RH riemannHypothesis

/-- Cramér (1922): `∫_1^X ((ψ(x) − x)/x)² dx ∼ (Σ_ρ m_ρ/|ρ|²) log X`. -/
theorem cramer_logMeanSquareAsymptotic : Cramer.CramerLogMeanSquareAsymptotic :=
  Cramer.logMeanSquareAsymptotic_of_RH riemannHypothesis

/-- Under the certified RH: every `(x, x + (3/2)√x log x]`, `x ≥ 2`, contains a prime. -/
theorem cramer_primeInShortInterval_three_halves : Cramer.PrimeInShortInterval (3 / 2) :=
  Cramer.primeInShortInterval_three_halves_of_RH riemannHypothesis

/-- `p_{n+1} − p_n ≤ (3/2)√p_n log p_n` for every `n`. -/
theorem cramer_primeGapExplicit_three_halves : Cramer.PrimeGapExplicit (3 / 2) :=
  Cramer.primeGapExplicit_three_halves_of_RH riemannHypothesis

/-- Every closed interval `[x, x + (3/2)√x log x]`, `x ≥ 2`, contains a prime. -/
theorem cramer_primeInClosedInterval_three_halves : Cramer.PrimeInClosedInterval 2 (3 / 2) :=
  Cramer.primeInClosedInterval_three_halves_of_RH riemannHypothesis

/-- Under the certified RH: every `(x, x + (107/100)√x log x]`, `x ≥ 2`, contains a prime. -/
theorem cramer_primeInShortInterval_107 : Cramer.PrimeInShortInterval (107 / 100) :=
  Cramer.primeInShortInterval_107_of_RH riemannHypothesis

/-- `p_{n+1} − p_n ≤ (107/100)√p_n log p_n` for every `n`. -/
theorem cramer_primeGapExplicit_107 : Cramer.PrimeGapExplicit (107 / 100) :=
  Cramer.primeGapExplicit_107_of_RH riemannHypothesis

/-- Every closed interval `[x, x + (107/100)√x log x]`, `x ≥ 2`, contains a prime. -/
theorem cramer_primeInClosedInterval_107 : Cramer.PrimeInClosedInterval 2 (107 / 100) :=
  Cramer.primeInClosedInterval_107_of_RH riemannHypothesis

#print axioms cramer_primeInShortInterval
#print axioms cramer_primeGapExplicit
#print axioms cramer_gapBound
#print axioms cramer_dyadicMeanSquare
#print axioms cramer_meanSquare
#print axioms cramer_logMeanSquare
#print axioms cramer_logMeanSquareAsymptotic
#print axioms cramer_primeInShortInterval_three_halves
#print axioms cramer_primeGapExplicit_three_halves
#print axioms cramer_primeInClosedInterval_three_halves
#print axioms cramer_primeInShortInterval_107
#print axioms cramer_primeGapExplicit_107
#print axioms cramer_primeInClosedInterval_107
