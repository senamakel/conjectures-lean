import Erdos770.Core
import Erdos770.Numerics

/-!
# Erdős 770 (iii) from Bach's subgroup bound

* `explicitBound_of_bach`: `BachSubgroupBound (21/5)` gives
  `h n ≤ max (P n) ⌈420 (log n)²⌉` for every `n ≥ 2`.
* `erdos_770_iii_of_explicit`: any explicit bound of this shape gives `Erdos770Part3`.
* `erdos_770_iii_of_bach`: the two together.

The proof: if `h n > M := max (P n) K`, `K = ⌈420 log² n⌉`, some prime `r > M` divides
`iⁿ - 1` for `2 ≤ i ≤ M` (`exists_bad_prime`). Bach gives `M < (21/5) log² r`. If `r ≤ n^10`
this is `M < 420 log² n ≤ K`, impossible. If `r > n^10 ≥ K^j`, `choose_le_of_bad` gives
`(π K).choose j ≤ n`, against `numeric`. For `n = 2`, `r ≤ 2² - 1 < 2^10`.
-/

open Filter

namespace Erdos770

theorem explicitBound_of_bach (hB : Ankeny.BachSubgroupBound (21 / 5)) :
    ExplicitBound 420 2 := by
  intro n hn
  set K := ⌈420 * Real.log n ^ 2⌉₊ with hK_def
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
    have h1 : (21 / 5) * Real.log r ^ 2 ≤ 420 * Real.log n ^ 2 := by nlinarith
    have h2 : 420 * Real.log n ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
    have h3 : (K : ℝ) ≤ M := by exact_mod_cast hKM
    linarith
  · push Not at hsmall
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have : n = 2 := by omega
      subst this
      norm_num at hr2 hsmall
      omega
    · obtain ⟨j, hj1, hj2⟩ := numeric hn3
      rw [← hK_def] at hj1 hj2
      have := choose_le_of_bad (by omega) hr hdvd K j hKM (lt_of_le_of_lt hj1 hsmall)
      omega

/-- Any bound `h n ≤ max (P n) ⌈C log² n⌉` for large `n` gives part (iii). -/
theorem erdos_770_iii_of_explicit {C : ℝ} {n₀ : ℕ} (hE : ExplicitBound C n₀) :
    Erdos770Part3 := by
  intro ε hε
  have hO := isLittleO_log_rpow_rpow_atTop 2 hε
  set c : ℝ := 1 / (2 * (|C| + 1)) with hc_def
  have hc0 : 0 < c := by positivity
  have hCc : |C| * c < 1 / 2 := by
    rw [hc_def]
    rw [show |C| * (1 / (2 * (|C| + 1))) = |C| / (|C| + 1) / 2 by field_simp]
    have : |C| / (|C| + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  have hreal : ∀ᶠ x : ℝ in atTop, C * Real.log x ^ 2 + 1 < x ^ ε := by
    filter_upwards [hO.bound hc0, (tendsto_rpow_atTop hε).eventually_ge_atTop 2,
      eventually_gt_atTop 0] with x hx h2 hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ ε),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      abs_of_nonneg (by positivity)] at hx
    have h1 : C * Real.log x ^ 2 ≤ |C| * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h2' : |C| * Real.log x ^ 2 ≤ |C| * (c * x ^ ε) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg C)
    have h3 : |C| * (c * x ^ ε) = (|C| * c) * x ^ ε := by ring
    have h4 : (|C| * c) * x ^ ε < 1 / 2 * x ^ ε :=
      mul_lt_mul_of_pos_right hCc (by positivity)
    linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal, eventually_ge_atTop (max n₀ 1)]
    with n hn hn0
  intro p hp
  have hpP : p = P n := rfl
  rw [hpP] at hp ⊢
  have hKp : ⌈C * Real.log n ^ 2⌉₊ ≤ P n := by
    rw [Nat.ceil_le]
    linarith
  have hup := hE n (le_of_max_le_left hn0)
  rw [max_eq_left hKp] at hup
  exact le_antisymm hup (P_le_h (le_of_max_le_right hn0))

theorem erdos_770_iii_of_bach (hB : Ankeny.BachSubgroupBound (21 / 5)) : Erdos770Part3 :=
  erdos_770_iii_of_explicit (explicitBound_of_bach hB)

end Erdos770
