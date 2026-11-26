import Erdos233.Basic

/-!
# Step 3. Local zero density: `Σ_ρ m_ρ / (1 + (T − γ)²) ≪ log(|T| + 2)`

Unconditional. Hadamard (`hadamard_logDeriv`) at `s = 2 + iT`, real parts:
`Re ξ'/ξ(s) = Re b + Σ m_ρ Re(1/(s−ρ) + 1/ρ)`, and for `0 < β < 1`,
`Re 1/ρ ≥ 0`, `Re 1/(s−ρ) = (2−β)/((2−β)² + (T−γ)²) ≥ 1/(4(1 + (T−γ)²))`.
`ξ'/ξ = ζ'/ζ + 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2)`, `|ζ'/ζ(2+iT)| ≤ 0.6`,
`Re ψ(1 + iT/2) ≤ log(|T| + 2) + O(1)`.
-/

namespace Erdos233

open Complex Erdos985.Analytic

namespace DensityAux

/-- `2(A−B)/(A+B) ≤ log A − log B` for `0 < B ≤ A`. -/
lemma two_mul_div_le_log_sub {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) :
    2 * ((A - B) / (A + B)) ≤ Real.log A - Real.log B := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hAB : 0 < A + B := by linarith
  set y := (A - B) / (A + B) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hAB.le
  have hy1 : y < 1 := by rw [hy, div_lt_one hAB]; linarith
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have h1 : 1 + y = 2 * A / (A + B) := by rw [hy]; field_simp; ring
  have h2 : 1 - y = 2 * B / (A + B) := by rw [hy]; field_simp; ring
  have hl : Real.log (1 + y) - Real.log (1 - y) = Real.log A - Real.log B := by
    rw [h1, h2, Real.log_div (by positivity) hAB.ne', Real.log_div (by positivity) hAB.ne',
      Real.log_mul (by norm_num) hA.ne', Real.log_mul (by norm_num) hB.ne']
    ring
  rw [← hl]
  have := le_hasSum hs 0 (fun k _ => by positivity)
  simpa using this

/-- The real part of the `k`-th digamma series term at `w = 1 + it`. -/
lemma re_term (t : ℝ) (k : ℕ) :
    (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + t * I))).re
      = t ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + t ^ 2)) := by
  have e1 : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((k : ℂ) + (1 + t * I)) = ⟨(k : ℝ) + 1, t⟩ := by
    apply Complex.ext <;> simp
  rw [e1, e2, sub_re, one_div, one_div, inv_re, inv_re, normSq_ofReal, ofReal_re]
  simp only [normSq_mk]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + 1) + t * t := by nlinarith [mul_self_nonneg t]
  field_simp
  ring

/-- Telescoping majorant `g(x) = ½ (log(x² + t²) − log x²)`. -/
noncomputable def g (t x : ℝ) : ℝ := (Real.log (x ^ 2 + t ^ 2) - Real.log (x ^ 2)) / 2

lemma g_nonneg (t : ℝ) {x : ℝ} (hx : 0 < x) : 0 ≤ g t x := by
  unfold g
  have : Real.log (x ^ 2) ≤ Real.log (x ^ 2 + t ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [sq_nonneg t])
  linarith

lemma term_le_g (t : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    t ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + t ^ 2)) ≤ g t k - g t ((k : ℝ) + 1) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set x : ℝ := (k : ℝ) with hx
  set A := (x ^ 2 + t ^ 2) * (x + 1) ^ 2
  set B := ((x + 1) ^ 2 + t ^ 2) * x ^ 2
  have hB : 0 < B := by positivity
  have hBA : B ≤ A := by
    have : A - B = t ^ 2 * (2 * x + 1) := by ring
    nlinarith [sq_nonneg t]
  have hl := two_mul_div_le_log_sub hB hBA
  have hgl : g t x - g t (x + 1) = (Real.log A - Real.log B) / 2 := by
    unfold g
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hgl]
  have hAB : A - B = t ^ 2 * (2 * x + 1) := by ring
  rw [hAB] at hl
  have key : t ^ 2 / ((x + 1) * ((x + 1) ^ 2 + t ^ 2)) ≤ t ^ 2 * (2 * x + 1) / (A + B) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpoly : (2 * x + 1) * ((x + 1) * ((x + 1) ^ 2 + t ^ 2)) - (A + B)
        = 3 * (x + 1) ^ 3 - 2 * (x + 1) ^ 2 + t ^ 2 * x := by ring
    have : 0 ≤ 3 * (x + 1) ^ 3 - 2 * (x + 1) ^ 2 + t ^ 2 * x := by
      have h1 : 0 ≤ (x + 1) ^ 2 * (3 * (x + 1) - 2) := by
        apply mul_nonneg (by positivity); linarith
      nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0:ℝ) ≤ x)]
    nlinarith [sq_nonneg t]
  linarith

/-- `Re ψ(1 + it) ≤ 1 + ½ log(1 + t²)`. -/
theorem re_digamma_le (t : ℝ) :
    (digamma (1 + t * I)).re ≤ 1 + Real.log (1 + t ^ 2) / 2 := by
  have hw : 1 / 2 < (1 + t * I).re := by simp; norm_num
  have hs := Complex.reCLM.hasSum (Erdos985.Analytic.BoundsAux.hasSum_digamma hw)
  simp only [Complex.reCLM_apply, re_term] at hs
  rw [sub_re, digamma_one, neg_re, ofReal_re] at hs
  set r : ℕ → ℝ := fun k => t ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + t ^ 2))
  have hr0 : ∀ k, 0 ≤ r k := fun k => by positivity
  let G : ℕ → ℝ := fun k => if k = 0 then 1 + g t 1 else g t k
  have hG : ∀ k, r k ≤ G k - G (k + 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [G, r, ↓reduceIte, Nat.cast_zero, zero_add, one_ne_zero, Nat.cast_one]
      have : t ^ 2 / (1 * (1 ^ 2 + t ^ 2)) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      linarith
    · simp only [G, r, hk.ne', Nat.succ_ne_zero k, ↓reduceIte]
      push_cast
      exact term_le_g t hk
  have hGnn : ∀ k, 0 ≤ G k := by
    intro k
    simp only [G]
    split_ifs with h
    · linarith [g_nonneg t one_pos]
    · exact g_nonneg t (by positivity)
  have hpart : ∀ n, ∑ k ∈ Finset.range n, r k ≤ G 0 := by
    intro n
    calc ∑ k ∈ Finset.range n, r k ≤ ∑ k ∈ Finset.range n, (G k - G (k + 1)) :=
          Finset.sum_le_sum fun k _ => hG k
      _ = G 0 - G n := Finset.sum_range_sub' G n
      _ ≤ G 0 := by linarith [hGnn n]
  have hle := Real.tsum_le_of_sum_range_le hr0 hpart
  rw [hs.tsum_eq] at hle
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hG0 : G 0 = 1 + Real.log (1 + t ^ 2) / 2 := by
    simp [G, g]
  linarith

/-- `Re (1/z) ≤ 1` when `Re z ≥ 1`. -/
lemma re_one_div_le {z : ℂ} (hz : 1 ≤ z.re) : (1 / z).re ≤ 1 := by
  rw [one_div, inv_re, normSq_apply]
  have h0 : 0 < z.re * z.re + z.im * z.im := by nlinarith [mul_self_nonneg z.im]
  rw [div_le_one h0]
  nlinarith [mul_self_nonneg z.im]

/-- `‖ζ'/ζ(s)‖ ≤ 0.6` on `Re s = 2`. -/
lemma norm_logDeriv_zeta_le {s : ℂ} (hs : s.re = 2) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ 0.6 := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have key := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  rw [show deriv riemannZeta s / riemannZeta s = -(-deriv riemannZeta s / riemannZeta s) by ring,
    ← key, norm_neg]
  refine le_trans ?_ Erdos985.Analytic.BoundsAux.S2_le
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  rw [LSeries]
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hsum.norm Erdos985.Analytic.BoundsAux.summable_Λ2
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, ↓reduceIte]
  rw [hs, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  norm_cast

/-- `Re ξ'/ξ(2 + iT) ≤ 4 + ½ log(|T| + 2)`. -/
lemma re_logDeriv_xi_le (T : ℝ) :
    (deriv xiZeta (2 + T * I) / xiZeta (2 + T * I)).re ≤ 4 + Real.log (|T| + 2) / 2 := by
  set s : ℂ := 2 + T * I with hsdef
  have hsre : s.re = 2 := by simp [hsdef]
  have hsim : s.im = T := by simp [hsdef]
  have he := PrincipalAux.logDeriv_riemannZeta_eq (s := s) (by rw [hsre]; norm_num)
  rw [PrincipalAux.gammaLogDeriv_one] at he
  have hxi : deriv xiZeta s / xiZeta s = deriv riemannZeta s / riemannZeta s + 1 / s
      + 1 / (s - 1) + (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2)) := by
    rw [he]; ring
  have hs2 : s / 2 = 1 + ((T / 2 : ℝ) : ℂ) * I := by rw [hsdef]; push_cast; ring
  rw [hxi, hs2]
  have hz := norm_logDeriv_zeta_le hsre
  have hzre := (Complex.re_le_norm (deriv riemannZeta s / riemannZeta s)).trans hz
  have h1 := re_one_div_le (z := s) (by rw [hsre]; norm_num)
  have h2 := re_one_div_le (z := s - 1) (by rw [sub_re, hsre]; norm_num)
  have hd := re_digamma_le (T / 2)
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog : Real.log (1 + (T / 2) ^ 2) ≤ 2 * Real.log (|T| + 2) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [show ((|T| + 2) ^ (2 : ℝ)) = (|T| + 2) ^ 2 by norm_cast]
    nlinarith [abs_nonneg T, sq_abs T]
  have hre : (-(1 / 2) * (Real.log Real.pi : ℂ)).re + ((1 / 2) * digamma (1 + ((T / 2 : ℝ) : ℂ) * I)).re
      = -(1 / 2) * Real.log Real.pi + (1 / 2) * (digamma (1 + ((T / 2 : ℝ) : ℂ) * I)).re := by
    simp
  simp only [add_re]
  rw [hre]
  linarith

/-- The real part of one Hadamard term dominates `m / (4 (1 + (T − γ)²))`. -/
lemma term_le_re (T : ℝ) (ρ : Zeros) :
    (mult ρ : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤
      4 * ((mult ρ : ℂ) * (1 / ((2 + T * I) - ρ) + 1 / ρ)).re := by
  obtain ⟨hβ0, hβ1⟩ := xiZeta_zero_re_mem ρ.2
  set β := (ρ : ℂ).re
  set γ := (ρ : ℂ).im
  have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re]
  have hρ : (1 / (ρ : ℂ)).re ≥ 0 := by
    rw [one_div, inv_re]; exact div_nonneg hβ0.le (normSq_nonneg _)
  have hsr : (1 / ((2 + T * I) - (ρ : ℂ))).re = (2 - β) / ((2 - β) ^ 2 + (T - γ) ^ 2) := by
    rw [one_div, inv_re, normSq_apply]
    simp [β, γ]
    ring
  have hd : 1 / (4 * (1 + (T - γ) ^ 2)) ≤ (2 - β) / ((2 - β) ^ 2 + (T - γ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by nlinarith [sq_nonneg (T - γ)])]
    nlinarith [sq_nonneg (T - γ), mul_nonneg (sq_nonneg (T - γ)) (by linarith : (0:ℝ) ≤ 1 - β)]
  rw [hsr]
  have : (mult ρ : ℝ) / (1 + (T - γ) ^ 2) = 4 * ((mult ρ : ℝ) * (1 / (4 * (1 + (T - γ) ^ 2)))) := by
    field_simp
  rw [this]
  have := mul_le_mul_of_nonneg_left hd hm
  nlinarith [mul_nonneg hm hρ]

end DensityAux

open DensityAux in
theorem zero_density : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
    Summable (fun ρ : Zeros => (mult ρ : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2)) ∧
    ∑' ρ : Zeros, (mult ρ : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) ≤ C * Real.log (|T| + 2) := by
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * ((4 + |b.re|) / Real.log 2 + 1), by positivity, fun T => ?_⟩
  have hne : xiZeta (2 + T * I) ≠ 0 := by
    intro h
    have := (xiZeta_zero_re_mem h).2
    norm_num at this
  obtain ⟨hsum, heq⟩ := H _ hne
  have hre := Complex.reCLM.hasSum hsum.hasSum
  simp only [Complex.reCLM_apply] at hre
  have hcmp := term_le_re T
  have hnn : ∀ ρ : Zeros, 0 ≤ (mult ρ : ℝ) / (1 + (T - (ρ : ℂ).im) ^ 2) :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hre4 := hre.mul_left 4
  have hS := Summable.of_nonneg_of_le hnn hcmp hre4.summable
  refine ⟨hS, ?_⟩
  have hle := (hS.tsum_le_tsum hcmp hre4.summable).trans_eq hre4.tsum_eq
  have hv := congrArg Complex.re heq
  rw [add_re] at hv
  have hb := re_logDeriv_xi_le T
  have hL : Real.log 2 ≤ Real.log (|T| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  have hL0 : 0 < Real.log (|T| + 2) := lt_of_lt_of_le hl2 hL
  have hab : -b.re ≤ |b.re| := neg_le_abs _
  have hk : (4 + |b.re|) ≤ (4 + |b.re|) / Real.log 2 * Real.log (|T| + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  nlinarith

end Erdos233
