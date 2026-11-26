import SunA243164.Analytic
import SunA243164.Compute

/-!
# Sun's Conjecture 3.25 (A243164) from GRH and the sieve numerics

`sunA243164_of_GRH_of_numerics` takes GRH for Dirichlet L-functions and the purely numerical
statement `SieveNumerics (10^8)` as explicit hypotheses. The finite range `P < 10^8` is proved
(`Compute.verifiedBelow_10_8`, 20 `native_decide` chunks with a proved-sound checker).
`SieveNumerics (10^8)` is a real-number inequality with no L-function in it; proving it is the
remaining step (`docs/PLAN.md`).
-/

namespace SunA243164

theorem sunA243164_of_GRH_of_numerics (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hnum : SieveNumerics 100000000) : SunA243164Statement :=
  sunA243164_of_goodFrom_of_verified (goodFrom_of_GRH hGRH (by norm_num) hnum)
    Compute.verifiedBelow_10_8

end SunA243164

#print axioms SunA243164.sunA243164_of_GRH_of_numerics
