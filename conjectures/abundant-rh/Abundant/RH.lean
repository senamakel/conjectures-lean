import Abundant.SolePlanat
import Abundant.Extremely
import Abundant.Extraordinary
import Nicolas.Main

/-!
# The RH layer

Each theorem takes `RiemannHypothesis` and obtains Nicolas' inequality from nicolas-rh's
`Nicolas.nicolas_of_RH`. Robin's inequality is taken as robin-rh's fixed statement
`Robin.RobinStatement`: robin-rh's `Robin.robin_of_RH` needs its verified-range sieve (about 54
core-hours to build), so `Unconditional/` supplies it from `robin_unconditional` instead.
-/

namespace Abundant

/-- **Solé–Planat** (2011, Theorem 1): under RH, `Ψ(N_n)/(N_n log log N_n) > e^γ/ζ(2)` for
every `n ≥ 3`. -/
theorem solePlanat_of_RH (hRH : RiemannHypothesis) : SolePlanatStatement :=
  solePlanat_of_nicolas (Nicolas.nicolas_of_RH hRH)

/-- **Nazardonyavi–Yakubovich** (2014, Theorem 2.4): under RH (with Robin's inequality, itself
a consequence of RH), there are infinitely many extremely abundant numbers. -/
theorem extremelyAbundantInfinite_of_RH (hRH : RiemannHypothesis) (hR : Robin.RobinStatement) :
    ExtremelyAbundantInfinite :=
  extremelyAbundantInfinite_of_robin_of_nicolas hR (Nicolas.nicolas_of_RH hRH)

/-- **Caveney–Nicolas–Sondow** (2011, Theorem 5): under RH (with Robin's inequality, itself a
consequence of RH), `4` is the only extraordinary number. -/
theorem fourOnlyExtraordinary_of_RH (hRH : RiemannHypothesis) (hR : Robin.RobinStatement) :
    FourOnlyExtraordinary :=
  fourOnlyExtraordinary_of_robin_of_nicolas hR (Nicolas.nicolas_of_RH hRH)

end Abundant
