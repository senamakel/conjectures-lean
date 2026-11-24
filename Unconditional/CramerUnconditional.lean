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

#print axioms cramer_primeInShortInterval
#print axioms cramer_primeGapExplicit
#print axioms cramer_gapBound
#print axioms cramer_dyadicMeanSquare
#print axioms cramer_meanSquare
#print axioms cramer_logMeanSquare
