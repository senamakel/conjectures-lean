import LLS.L1.Defs
import LLS.L1.PrinAux.Ces
import LLS.L1.PrinAux.Mertens
import Robin.RH.Bach

/-! # Principal sums for Theorem 1.5

* `l1Sum1_le` (under GRH): `Σ_{n≤x} Λ(n)/(n log n) · log(x/n)/log x ≤ log log x + γ − 1 + 3/log x`
  for `x ≥ 10^5`. The sum is `Σ_{n≤x} Λ(n)/(n log n) − (1/log x) Σ_{n≤x} Λ(n)/n`; the first part
  is at most Mertens' `Σ_{p≤x} −log(1 − 1/p)`, bounded by `LLS.primeSum_cp_le` (robin-rh's
  `mertens_RH` with explicit tails, `Psi1NatBound` from erdos-985's principal bound); the second
  is at least `log x − 2` (`LLS.vonMangoldt_ces_ge`).
* `vonMangoldt_ces_le` (unconditional): `Σ_{n<x} Λ(n)/n (1 − n/x) ≤ log x − 1 + 1/x`.
-/

namespace LLS

open ArithmeticFunction Erdos985

/-- `Psi1NatBound` from GRH (via erdos-985's principal bound). -/
theorem psi1NatBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Robin.Psi1NatBound :=
  Robin.psi1NatBound_of_bachBound fun x hx => Erdos985.Analytic.bach_principal_of_GRH hGRH x hx

lemma l1Sum1_eq (x : ℕ) (hx : 2 ≤ x) :
    l1Sum1 x = ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n))
      - (1 / Real.log x) * ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) / n := by
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [l1Sum1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : n ≤ x := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  by_cases h0 : (Λ n : ℝ) = 0
  · simp [h0]
  have hpp : IsPrimePow n := by
    by_contra h; exact h0 (by rw [vonMangoldt_apply, if_neg h])
  have hn2 : 2 ≤ n := hpp.two_le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [Real.log_div (by positivity) hn0.ne']
  field_simp

theorem l1Sum1_le (hGRH : DirichletLNonvanishingRightOfHalf) (x : ℕ) (hx : 100000 ≤ x) :
    l1Sum1 x ≤ Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 + 3 / Real.log x := by
  have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL := log_ge_eleven hxR
  have hL0 : 0 < Real.log x := by linarith
  set L := Real.log (x : ℝ) with hLdef
  -- the two sums
  have hP := primeSum_cp_le (psi1NatBound_of_GRH hGRH) hxR
  have hA := sum_vonMangoldt_div_log_le x
  have hC : L - 2 ≤ ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) / n := by
    have h := vonMangoldt_ces_ge x (by omega)
    refine h.trans ?_
    rw [Finset.sum_range_succ]
    have h1 : ∑ n ∈ Finset.range x, (Λ n : ℝ) / n * (1 - (n : ℝ) / x)
        ≤ ∑ n ∈ Finset.range x, (Λ n : ℝ) / n := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hnx : (n : ℝ) ≤ x := by exact_mod_cast (Finset.mem_range.1 hn).le
      have h0 : 0 ≤ (Λ n : ℝ) / n := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
      have : 0 ≤ (n : ℝ) / x := by positivity
      nlinarith
    have h2 : 0 ≤ (Λ x : ℝ) / x := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    linarith
  rw [l1Sum1_eq x (by omega)]
  have hC' : (1 / L) * (L - 2) ≤ (1 / L) * ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) / n :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  have e1 : (1 / L) * (L - 2) = 1 - 2 / L := by field_simp
  -- the error terms, with `v = x^{1/4}`
  set v := (x : ℝ) ^ ((1 : ℝ) / 4) with hv
  have hv0 : 0 < v := by positivity
  have hv4 : v ^ 4 = x := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hv17 : 17.76 ≤ v := by
    by_contra h
    push Not at h
    have : v ^ 4 < 17.76 ^ 4 := pow_lt_pow_left₀ h hv0.le (by norm_num)
    norm_num at this
    linarith
  have hu : (x : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / v := by
    rw [Real.rpow_neg hx0.le, hv, one_div]; norm_num
  have hu2 : (x : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / v ^ 2 := by
    rw [Real.rpow_neg hx0.le, hv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, one_div]
    norm_num
  have hLv : L ≤ 4 * v / Real.exp 1 := by
    have hlv : Real.log v = L / 4 := by
      rw [hv, Real.log_rpow hx0]; ring
    have h := Real.log_le_sub_one_of_pos (show 0 < v / Real.exp 1 by positivity)
    rw [Real.log_div hv0.ne' (Real.exp_pos 1).ne', Real.log_exp, hlv] at h
    have : 4 * v / Real.exp 1 = 4 * (v / Real.exp 1) := by ring
    linarith
  have he := Real.exp_one_gt_d9
  have hE : (59 / 11) * (1 / v) / L + (48 / 11) * (1 / v ^ 2) ≤ 1 / L := by
    rw [div_add' _ _ _ hL0.ne', div_le_div_iff_of_pos_right hL0]
    -- `L / v² ≤ 4/(e v)`
    have h1 : L * (1 / v ^ 2) ≤ 4 / Real.exp 1 * (1 / v) := by
      rw [show 4 / Real.exp 1 * (1 / v) = 4 * v / Real.exp 1 * (1 / v ^ 2) by field_simp]
      exact mul_le_mul_of_nonneg_right hLv (by positivity)
    have h2 : 4 / Real.exp 1 ≤ 1.4716 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    have h3 : 1 / v ≤ 1 / 17.76 := one_div_le_one_div_of_le (by norm_num) hv17
    have h4 : 0 ≤ 1 / v := by positivity
    nlinarith
  rw [hu, hu2, ← hLdef] at hP
  have hfin : 59 / 11 * (1 / v) / L + 48 / 11 * (1 / v ^ 2) + 2 / L ≤ 3 / L := by
    have : 3 / L = 1 / L + 2 / L := by ring
    linarith
  linarith

theorem vonMangoldt_ces_le (x : ℕ) (hx : 2 ≤ x) :
    ∑ n ∈ Finset.range x, (Λ n : ℝ) / n * (1 - (n : ℝ) / x) ≤ Real.log x - 1 + 1 / x :=
  vonMangoldt_ces_le_aux x hx

end LLS
