import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Weinberger.Main
import Weinberger.ClassNumber.Main

/-!
# Euler's idoneal numbers are complete, with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem idoneal_completeness : Idoneal.IdonealCompletenessStatement :=
  Weinberger.idoneal_completeness_of_GRH LFunction_ne_zero_of_half_lt_re

theorem isIdoneal_iff (n : ℕ) : Idoneal.IsIdoneal n ↔ n ∈ Idoneal.knownIdonealNumbers :=
  Weinberger.isIdoneal_iff_of_GRH LFunction_ne_zero_of_half_lt_re n

#print axioms idoneal_completeness
#print axioms isIdoneal_iff

/-- Class number one for imaginary quadratic fields, given the two cited inputs
`ClassNumberOneNorms` and `HeegnerClassNumberOne` (tier U + H). -/
theorem starkHeegner_of_cited (hPS : Weinberger.ClassNumberOneNorms)
    (hH : Weinberger.HeegnerClassNumberOne) : ClassNumberProblem.StarkHeegnerStatement :=
  Weinberger.ClassNumber.starkHeegner_of_GRH LFunction_ne_zero_of_half_lt_re hPS hH

#print axioms starkHeegner_of_cited
