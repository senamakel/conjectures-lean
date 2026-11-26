import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import SunA243164

/-!
# Sun's Conjecture 3.25 with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
GRH is discharged in one line. The numerical input `SieveNumerics (10^8)` is still an explicit
hypothesis (it is not yet proved in Lean; see `docs/PLAN.md`).
-/

theorem sunA243164_of_numerics (hnum : SunA243164.SieveNumerics 100000000) :
    SunA243164.SunA243164Statement :=
  SunA243164.sunA243164_of_GRH_of_numerics LFunction_ne_zero_of_half_lt_re hnum

#print axioms sunA243164_of_numerics
