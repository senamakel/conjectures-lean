import Robin.Mertens.Abelian.Mellin

/-!
# Comparison of the Mertens series with `log ζ(s)`

* `log_riemannZeta_re_eq_tsum`: for real `s > 1`, `log ζ(s) = Σ_p −log(1 − p^{−s})`;
* `tendsto_tsum_aP_sub_bZ`: `Σ_p (c_p p^{1−s} − (−log(1 − p^{−s}))) → 0` as `s → 1⁺`;
* `tendsto_log_zeta_add_log`: `log ζ(s) + log(s − 1) → 0` as `s → 1⁺`.
-/

namespace Robin

open Filter Topology Real MeasureTheory Set

/-- `−log(1 − n^{−s})` on primes, `0` elsewhere. -/
noncomputable def bZ (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - (n : ℝ) ^ (-s)) else 0

lemma log_riemannZeta_re_eq_tsum {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta s).re = ∑' n, bZ s n := by
  have h := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) (by simpa using hs)
  have hterm : ∀ p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))
      = ((-Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) : ℝ) : ℂ) := by
    intro p
    have hp0 : (0:ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
    have hp1 : (1:ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
    have hlt : ((p : ℕ) : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cpow hp0, Complex.ofReal_neg, Complex.ofReal_natCast]
  simp_rw [hterm] at h
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp] at h
  rw [← h, Complex.ofReal_re, Real.log_exp]
  have := tsum_subtype {p : ℕ | p.Prime} (fun n : ℕ => -Real.log (1 - (n : ℝ) ^ (-s)))
  refine this.trans (tsum_congr fun n => ?_)
  simp [Set.indicator_apply, bZ]

lemma tendsto_term (k : ℕ) :
    Tendsto (fun s : ℝ => aP k * (k : ℝ) ^ (1 - s) - bZ s k) (𝓝[>] 1) (𝓝 0) := by
  by_cases hk : k.Prime
  · have hk1 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hc : ContinuousAt (fun s : ℝ => aP k * (k : ℝ) ^ (1 - s) - bZ s k) 1 := by
      simp only [bZ, hk, ↓reduceIte]
      have h1 : ContinuousAt (fun s : ℝ => (k : ℝ) ^ (1 - s)) 1 :=
        (Real.continuousAt_const_rpow hk0).comp (continuousAt_const.sub continuousAt_id)
      have h2 : ContinuousAt (fun s : ℝ => (k : ℝ) ^ (-s)) 1 :=
        (Real.continuousAt_const_rpow hk0).comp continuousAt_id.neg
      have h3 : (1 : ℝ) - (k : ℝ) ^ (-(1:ℝ)) ≠ 0 := by
        have : (k : ℝ) ^ (-(1:ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hk1 (by norm_num)
        linarith
      exact (continuousAt_const.mul h1).sub ((continuousAt_const.sub h2).log h3).neg
    have hv : aP k * (k : ℝ) ^ (1 - (1:ℝ)) - bZ 1 k = 0 := by
      simp [aP, bZ, hk, cp, Real.rpow_neg_one]
    have := hc.tendsto
    rw [hv] at this
    exact this.mono_left nhdsWithin_le_nhds
  · simp [aP, bZ, hk]

lemma term_bound {s : ℝ} (hs : 1 ≤ s) (k : ℕ) :
    ‖aP k * (k : ℝ) ^ (1 - s) - bZ s k‖ ≤ 2 * (1 / (k : ℝ) ^ 2) := by
  by_cases hk : k.Prime
  · simp only [aP, bZ, hk, ↓reduceIte]
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.one_lt.le
    have hk0 : (0:ℝ) < k := by linarith
    have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk.two_le
    set x := (k : ℝ) ^ (-s) with hx
    set y := 1 / (k : ℝ) with hy
    have hx0 : 0 ≤ x := by positivity
    have hxy : x ≤ y := by
      calc x ≤ (k : ℝ) ^ (-(1:ℝ)) := rpow_le_rpow_of_exponent_le hk1 (by linarith)
        _ = y := by rw [Real.rpow_neg_one, hy, one_div]
    have hy2 : y ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2
    have hyk : y * k = 1 := by rw [hy]; field_simp
    have hw : (k : ℝ) ^ (1 - s) = k * x := natCast_rpow_one_sub hk.ne_zero s
    obtain ⟨hc1, hc2⟩ := cp_bounds hk
    rw [← hy] at hc1 hc2
    obtain ⟨hb1, hb2⟩ := neg_log_one_sub_bounds hx0 (le_trans hxy hy2)
    have hA1 : x ≤ cp k * (k * x) := by
      have : y * k * x ≤ cp k * k * x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hk0.le) hx0
      rw [hyk] at this; linarith
    have hA2 : cp k * (k * x) ≤ x + 2 * y ^ 2 := by
      have : cp k * k * x ≤ (y + 2 * y ^ 2) * k * x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hk0.le) hx0
      have e : (y + 2 * y ^ 2) * k * x = x + 2 * y * x := by
        have : (y + 2 * y ^ 2) * k = 1 + 2 * y := by nlinarith
        rw [this]; ring
      have : 2 * y * x ≤ 2 * y * y := mul_le_mul_of_nonneg_left hxy (by positivity)
      nlinarith
    have hB2 : -Real.log (1 - x) ≤ x + 2 * y ^ 2 := by
      have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0 hxy 2
      linarith
    have hyy : 2 * (1 / (k : ℝ) ^ 2) = 2 * y ^ 2 := by rw [hy, div_pow, one_pow]
    rw [hyy, Real.norm_eq_abs, hw, abs_sub_le_iff]
    constructor <;> linarith
  · simp [aP, bZ, hk]

lemma tendsto_tsum_aP_sub_bZ :
    Tendsto (fun s : ℝ => ∑' k, (aP k * (k : ℝ) ^ (1 - s) - bZ s k)) (𝓝[>] 1) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (1:ℝ))
    (f := fun s k => aP k * (k : ℝ) ^ (1 - s) - bZ s k) (g := fun _ => (0:ℝ))
    (bound := fun k : ℕ => 2 * (1 / (k : ℝ) ^ 2))
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2)
    tendsto_term
    (by filter_upwards [self_mem_nhdsWithin] with s hs using fun k => term_bound (le_of_lt hs) k)
  simpa using h

lemma tendsto_log_zeta_add_log :
    Tendsto (fun s : ℝ => Real.log (riemannZeta s).re + Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Complex.continuous_ofReal.tendsto (1:ℝ)
      rw [Complex.ofReal_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs : (1:ℝ) < s := hs
      simp only [mem_compl_iff, mem_singleton_iff]
      exact_mod_cast hs.ne'
  have h2 := (Complex.continuous_re.tendsto 1).comp (riemannZeta_residue_one.comp h1)
  have h3 : Tendsto (fun s : ℝ => (s - 1) * (riemannZeta s).re) (𝓝[>] 1) (𝓝 1) := by
    refine (h2.congr fun s => ?_).trans (by simp)
    simp [Complex.mul_re]
  have h4 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h3)
  rw [Real.log_one] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : (1:ℝ) < s := hs
  have hz := riemannZeta_re_pos_of_one_lt hs
  simp only [Function.comp_apply]
  rw [Real.log_mul (by linarith) hz.ne', add_comm]

end Robin
