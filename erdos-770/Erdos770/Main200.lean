import Erdos770.Core
import Erdos770.Numerics200
import Erdos770.Main
import Erdos770.Statement2

/-!
# Erdős 770 (iii) from Bach's subgroup bound with constant 2

`explicitBound200_of_bach`: `BachSubgroupBound 2` gives `h n ≤ max (P n) ⌈200 (log n)²⌉` for
every `n ≥ 2`. The proof is that of `explicitBound_of_bach` with `c = 2` in place of `21/5`:
if `r ≤ n^10` then `M < 2 log² r ≤ 200 log² n ≤ K`; otherwise `K^j ≤ n^10 < r` and
`(π K).choose j ≤ n` is contradicted by `numeric200`. In general `BachSubgroupBound c` yields the
constant `100 c` in the first case, so `420 = 100 · 21/5` and `200 = 100 · 2`.
-/

namespace Erdos770

theorem explicitBound200_of_bach (hB : Ankeny.BachSubgroupBound 2) : ExplicitBound200 := by
  intro n hn
  set K := ⌈200 * Real.log n ^ 2⌉₊ with hK_def
  set M := max (P n) K with hM_def
  have hlog2 : (0.69 : ℝ) < Real.log n := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hK3 : 2 < K := by
    rw [hK_def, Nat.lt_ceil]
    push_cast
    nlinarith
  have hKM : K ≤ M := le_max_right _ _
  apply h_le_of_gcd (by omega)
  by_contra hg
  obtain ⟨r, hr, hMr, hr2, hdvd⟩ := exists_bad_prime (by omega) (by omega) hg
  have hlt := lt_of_bach hB (by omega) hr hMr (le_max_left _ _) hdvd
  by_cases hsmall : r ≤ n ^ 10
  · have hlogr : Real.log r ≤ 10 * Real.log n := by
      have := Real.log_le_log (by exact_mod_cast hr.pos : (0 : ℝ) < r)
        (by exact_mod_cast hsmall : (r : ℝ) ≤ ((n ^ 10 : ℕ) : ℝ))
      rw [Nat.cast_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr.one_lt.le)
    have h1 : 2 * Real.log r ^ 2 ≤ 200 * Real.log n ^ 2 := by nlinarith
    have h2 : 200 * Real.log n ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
    have h3 : (K : ℝ) ≤ M := by exact_mod_cast hKM
    linarith
  · push Not at hsmall
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have : n = 2 := by omega
      subst this
      norm_num at hr2 hsmall
      omega
    · obtain ⟨j, hj1, hj2⟩ := numeric200 hn3
      rw [← hK_def] at hj1 hj2
      have := choose_le_of_bad (by omega) hr hdvd K j hKM (lt_of_le_of_lt hj1 hsmall)
      omega

theorem erdos_770_iii_of_bach200 (hB : Ankeny.BachSubgroupBound 2) : Erdos770Part3 :=
  erdos_770_iii_of_explicit (explicitBound200_of_bach hB)

end Erdos770
