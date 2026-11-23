import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Miller.GRH

/-!
# Miller's test is deterministic, with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem miller_unconditional : Miller.MillerStatement (21 / 5) :=
  Miller.miller_of_GRH LFunction_ne_zero_of_half_lt_re

theorem millerTestGRH_iff_prime_unconditional {n : ℕ} (hn : Odd n) (h1 : 1 < n) :
    Miller.millerTestGRH n = true ↔ n.Prime :=
  Miller.millerTestGRH_iff_prime LFunction_ne_zero_of_half_lt_re hn h1

#print axioms miller_unconditional
#print axioms millerTestGRH_iff_prime_unconditional
