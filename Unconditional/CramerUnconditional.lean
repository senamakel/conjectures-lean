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

#print axioms cramer_primeInShortInterval
#print axioms cramer_primeGapExplicit
#print axioms cramer_gapBound
