import Erdos985.Indicator
import Erdos985.Numerics
import Erdos985.Compute
import Erdos985.Analytic.ExplicitFormula

namespace Erdos985

/-!
# Erdős Problem 985 from GRH for Dirichlet L-functions
-/

open ArithmeticFunction Real

theorem erdos_985_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Erdos985Statement := by
  intro p hp hp2
  by_cases hlt : p < 10 ^ 8
  · exact small_primes_have_prime_primitive_root p hp hp2 hlt
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have hno : ∀ q, q.Prime → q < p → orderOf (q : ZMod p) ≠ p - 1 :=
    fun q hq hqp => hcon q hq hqp
  have hp1 : 1 ≤ p := hp.one_lt.le
  have key := principal_le_of_no_prime_primitive_root p hp2 p le_rfl
    (bachC p p * √p * Real.log p) (fun χ hχ => Analytic.bach_nonprincipal_of_GRH hGRH p χ hχ p hp1) hno
  have hprin := bach_principal hGRH p hp1
  have hbig := bach_inequality_large p hp (not_lt.mp hlt)
  have := (abs_le.mp hprin).1
  linarith

end Erdos985
