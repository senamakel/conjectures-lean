import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import GoldbachAverage

/-!
# The average number of Goldbach representations, with RH supplied by riemann-hypothesis

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem goldbach_average_sharp : GoldbachAverage.GoldbachAverageSharp 4000 :=
  GoldbachAverage.goldbachAverageSharp_of_RH riemannHypothesis

theorem goldbach_average : GoldbachAverage.GoldbachAverageBound :=
  GoldbachAverage.goldbachAverage_of_RH riemannHypothesis

/-- Fujii (1991): `|Σ_{n ≤ x} G(n) − x²/2| ≤ C x^{3/2}` for large `x`. -/
theorem fujii_bound : GoldbachAverage.FujiiBound :=
  GoldbachAverage.fujii_of_RH riemannHypothesis

/-- Fujii (1991): `Σ_{n ≤ x} G(n) = x²/2 + O(x^{3/2})`. -/
theorem fujii : GoldbachAverage.FujiiStatement :=
  GoldbachAverage.fujiiStatement_of_RH riemannHypothesis

#print axioms goldbach_average_sharp
#print axioms goldbach_average
#print axioms fujii_bound
#print axioms fujii
