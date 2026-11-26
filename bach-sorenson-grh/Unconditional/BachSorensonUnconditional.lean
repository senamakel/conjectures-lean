import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import BachSorenson.Main
import BachSorenson.Two.Main

/-!
# The Bach–Sorenson bound (constants `2` and `7/2`), with GRH supplied by the riemann-hypothesis
# repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem bachSorenson_unconditional : BachSorenson.BachSorensonBound (7 / 2) :=
  BachSorenson.bachSorenson_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms bachSorenson_unconditional

/-- Bach–Sorenson's theorem with their constant: the least prime `p ≡ a (mod q)` is below
`2 (q log q)²` for every `q ≥ 2` and every `a` coprime to `q`. -/
theorem bachSorenson_two_unconditional : BachSorenson.BachSorensonBound 2 :=
  BachSorenson.bachSorenson_two_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms bachSorenson_two_unconditional
