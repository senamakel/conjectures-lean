import Robin.Mertens.Identity
import Robin.RH.Psi1
import LLS.Numerics.Budget

/-!
# Mertens' third theorem, upper bound, under RH, for `x ≥ 10^5`

robin-rh's `Robin.mertens_RH` gives
`Σ_{p≤x} c_p ≤ γ + log log x + (θ(x) − x)/(x log x) − ∫_x^∞ (θ(t) − t) w(t) dt`.
With `ψ(t) ≤ t + t^{3/4}`, `ψ(t) ≥ t − t^{3/4}` (robin-rh, `t ≥ 1000`, from `Psi1NatBound`) and
`ψ − θ ≤ 2√t log t` (Mathlib), for `log t ≥ log x ≥ 11` the integrand `(t − θ) w` is at most
`(12/11)/log x · t^{−5/4} + (24/11) t^{−3/2}`, which gives
`Σ_{p≤x} c_p ≤ γ + log log x + (59/11) x^{−1/4}/log x + (48/11) x^{−1/2}`.
-/

namespace LLS

open Real Chebyshev MeasureTheory Set Finset ArithmeticFunction

lemma log_ge_eleven {x : ℝ} (hx : 100000 ≤ x) : 11 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h2 : Real.exp 1 ^ 11 ≤ 2.7182818286 ^ 11 := by
    gcongr
  have h3 : (2.7182818286 : ℝ) ^ 11 ≤ 100000 := by norm_num
  linarith

/-- The pointwise bound for the integrand. -/
lemma tail_integrand_le (hB : Robin.Psi1NatBound) {x t : ℝ} (hx : 100000 ≤ x) (ht : x ≤ t) :
    -((θ t - t) * Robin.wM t)
      ≤ (12 / 11) / Real.log x * t ^ (-(5 / 4 : ℝ)) + (24 / 11) * t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hL := log_ge_eleven hx
  have hlt : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) ht
  set lt := Real.log t
  have hlt11 : 11 ≤ lt := by linarith
  have hpl := Robin.psi_lower hB (show (1000 : ℝ) ≤ t by linarith)
  have hpt := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ t by linarith)
  set a := t ^ (-(5 / 4 : ℝ))
  set b := t ^ (-(3 / 2 : ℝ))
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hA : t ^ ((3 : ℝ) / 4) = a * t ^ 2 := by
    rw [show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_add ht0]; try norm_num
  have hS : √t = b * t ^ 2 := by
    rw [Real.sqrt_eq_rpow, show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_add ht0]
    try norm_num
  have hw : Robin.wM t = (1 + lt) / (t ^ 2 * lt ^ 2) := rfl
  have hw0 : 0 ≤ Robin.wM t := by rw [hw]; positivity
  have hdiff : t - θ t ≤ a * t ^ 2 + 2 * (b * t ^ 2) * lt := by
    rw [← hA, ← hS]; linarith
  have h1 : -((θ t - t) * Robin.wM t) ≤ (a * t ^ 2 + 2 * (b * t ^ 2) * lt) * Robin.wM t := by
    have := mul_le_mul_of_nonneg_right hdiff hw0
    linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hlt0 : 0 < lt := by linarith
  have e : (a * t ^ 2 + 2 * (b * t ^ 2) * lt) * Robin.wM t
      = a * ((1 + lt) / lt ^ 2) + 2 * b * ((1 + lt) / lt) := by
    rw [hw]; field_simp
  have h2 : (1 + lt) / lt ^ 2 ≤ (12 / 11) / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith
  have h3 : (1 + lt) / lt ≤ 12 / 11 := by
    rw [div_le_iff₀ hlt0]; linarith
  have h4 := mul_le_mul_of_nonneg_left h2 ha0
  have h5 := mul_le_mul_of_nonneg_left h3 hb0
  rw [e] at h1
  nlinarith

lemma integral_Ioi_rpow_eval {c a : ℝ} (ha : a < -1) (hc : 0 < c) :
    ∫ t in Ioi c, t ^ a = c ^ (a + 1) / (-(a + 1)) := by
  rw [integral_Ioi_rpow_of_lt ha hc, div_neg, neg_div]

/-- Mertens' third theorem, upper bound, for `x ≥ 10^5`, given `Psi1NatBound`. -/
theorem primeSum_cp_le (hB : Robin.Psi1NatBound) {x : ℝ} (hx : 100000 ≤ x) :
    Robin.primeSum Robin.cp x ≤ Real.eulerMascheroniConstant + Real.log (Real.log x)
      + (59 / 11) * x ^ (-(1 / 4 : ℝ)) / Real.log x + (48 / 11) * x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hL := log_ge_eleven hx
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨hint, hM⟩ := Robin.mertens_RH (Robin.theta_sub_bound hB) (show (2 : ℝ) ≤ x by linarith)
  -- the boundary term
  have hθx : θ x - x ≤ x ^ ((3 : ℝ) / 4) := by
    have := Robin.psi_upper hB (show (1000 : ℝ) ≤ x by linarith)
    have := Chebyshev.theta_le_psi x
    linarith
  have h34 : x ^ ((3 : ℝ) / 4) = x ^ (-(1 / 4 : ℝ)) * x := by
    rw [show (3 : ℝ) / 4 = -(1 / 4) + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hbd : (θ x - x) / (x * Real.log x) ≤ x ^ (-(1 / 4 : ℝ)) / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    have := mul_le_mul_of_nonneg_right hθx hL0.le
    rw [h34] at this
    nlinarith
  -- the integral
  set g : ℝ → ℝ := fun t =>
    (12 / 11) / Real.log x * t ^ (-(5 / 4 : ℝ)) + (24 / 11) * t ^ (-(3 / 2 : ℝ))
  have hg : IntegrableOn g (Ioi x) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx0).const_mul _).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx0).const_mul _)
  have hmono : ∫ t in Ioi x, -((θ t - t) * Robin.wM t) ≤ ∫ t in Ioi x, g t :=
    setIntegral_mono_on hint.neg hg measurableSet_Ioi fun t ht =>
      tail_integrand_le hB hx (le_of_lt ht)
  have hgint : ∫ t in Ioi x, g t
      = (12 / 11) / Real.log x * (x ^ (-(1 / 4 : ℝ)) / (1 / 4))
        + (24 / 11) * (x ^ (-(1 / 2 : ℝ)) / (1 / 2)) := by
    simp only [g]
    rw [integral_add ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx0).const_mul _)
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx0).const_mul _), integral_const_mul,
      integral_const_mul, integral_Ioi_rpow_eval (by norm_num) hx0,
      integral_Ioi_rpow_eval (by norm_num) hx0]
    norm_num
  rw [integral_neg] at hmono
  rw [hgint] at hmono
  have : (12 / 11) / Real.log x * (x ^ (-(1 / 4 : ℝ)) / (1 / 4))
      = (48 / 11) * x ^ (-(1 / 4 : ℝ)) / Real.log x := by field_simp; ring
  rw [this] at hmono
  have : (24 / 11) * (x ^ (-(1 / 2 : ℝ)) / (1 / 2)) = (48 / 11) * x ^ (-(1 / 2 : ℝ)) := by ring
  rw [this] at hmono
  have e : (59 / 11) * x ^ (-(1 / 4 : ℝ)) / Real.log x
      = x ^ (-(1 / 4 : ℝ)) / Real.log x + (48 / 11) * x ^ (-(1 / 4 : ℝ)) / Real.log x := by ring
  rw [e]
  linarith

/-- `Σ_{n≤x} Λ(n)/(n log n) ≤ Σ_{p≤x} −log(1 − 1/p)`. -/
theorem sum_vonMangoldt_div_log_le (x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n))
      ≤ Robin.primeSum Robin.cp x := by
  classical
  set S := (Finset.Iic x).filter Nat.Prime
  have hw : ∀ n ≤ x, (0 : ℝ) ≤ 1 / ((n : ℝ) * Real.log n) := fun n _ => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      positivity
  have h1 := sum_le_sum_ppF x (fun _ => True) S (fun n => 1 / ((n : ℝ) * Real.log n)) hw
    (fun n hn _ hpp => by
      simp only [S, Finset.mem_filter, Finset.mem_Iic]
      have hn1 : n ≠ 1 := fun h => by rw [h] at hpp; exact not_isPrimePow_one hpp
      exact ⟨(Nat.minFac_le (hpp.pos)).trans hn, Nat.minFac_prime hn1⟩)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h1
  refine h1.trans ?_
  have hps : Robin.primeSum Robin.cp x = ∑ p ∈ S, Robin.cp p := by
    simp only [Robin.primeSum, Nat.floor_natCast, S]
  rw [hps]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos hp1
  calc ∑ n ∈ ppF x p, (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n))
      ≤ ∑ n ∈ (range (Nat.log p x)).image (fun k => p ^ (k + 1)),
          (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (ppF_subset x p hpp) fun n hn _ => ?_
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hn
        have : (0 : ℝ) ≤ Real.log ((p ^ (k + 1) : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast Nat.one_le_pow _ _ hpp.pos)
        exact mul_nonneg vonMangoldt_nonneg (by positivity)
    _ = ∑ k ∈ range (Nat.log p x), (1 / (p : ℝ)) ^ (k + 1) / ((k : ℝ) + 1) := by
        rw [image_sum_eq hpp]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hpp]
        push_cast
        rw [Real.log_pow, one_div_pow]
        have hpk : (p : ℝ) ^ (k + 1) ≠ 0 := by positivity
        field_simp
        push_cast; ring
    _ ≤ Robin.cp p := by
        have hh := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / (p : ℝ))
          (by rw [abs_of_pos (by positivity), div_lt_one hp0]; exact hp1)
        unfold Robin.cp
        exact sum_le_hasSum _ (fun i _ => by positivity) hh

end LLS
