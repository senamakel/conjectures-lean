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

#print axioms goldbach_average_sharp
#print axioms goldbach_average
