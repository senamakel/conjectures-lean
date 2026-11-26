import Weinberger.Large
import Weinberger.Compute

/-!
# Euler's 65 idoneal numbers are all of them, under GRH
-/

namespace Weinberger

open Idoneal Erdos985

/-- Under GRH for Dirichlet L-functions, every idoneal number is one of Euler's 65
(the formal-conjectures statement `idoneal_numbers_completeness`). -/
theorem idoneal_completeness_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    IdonealCompletenessStatement := by
  intro n hn
  by_cases hlt : n < 10 ^ 8
  · exact mem_known_of_isIdoneal_of_lt hn hlt
  · exact absurd hn (not_isIdoneal_of_GRH hGRH (not_lt.mp hlt))

/-- Under GRH, the idoneal numbers are exactly Euler's 65. -/
theorem isIdoneal_iff_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (n : ℕ) :
    IsIdoneal n ↔ n ∈ knownIdonealNumbers :=
  ⟨idoneal_completeness_of_GRH hGRH n, knownIdonealNumbers_are_idoneal n⟩

end Weinberger
