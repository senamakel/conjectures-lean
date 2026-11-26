import Robin.Defs

/-!
# The Mellin transform of the Mertens sum

For `s > 1`, `(s − 1) ∫₁^∞ P(t) t^{-s} dt = Σ_p c_p p^{1-s}`, where `P = primeSum cp`.
We index the prime sum by `ℕ`, using `aP n = c_n` for prime `n` and `0` otherwise.
-/

namespace Robin

open Filter Topology Real MeasureTheory Set

/-- `c_n` on primes, `0` elsewhere. -/
noncomputable def aP (n : ℕ) : ℝ := if n.Prime then cp n else 0

/-- `y ≤ −log(1 − y) ≤ y + 2y²` for `0 ≤ y ≤ 1/2`. -/
lemma neg_log_one_sub_bounds {y : ℝ} (_h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    y ≤ -Real.log (1 - y) ∧ -Real.log (1 - y) ≤ y + 2 * y ^ 2 := by
  have hpos : 0 < 1 - y := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have : (1 - y)⁻¹ - 1 ≤ y + 2 * y ^ 2 := by
      rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
      nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) (by linarith : (0:ℝ) ≤ 1 - 2 * y)]
    linarith

lemma cp_bounds {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) ≤ cp p ∧ cp p ≤ 1 / (p : ℝ) + 2 * (1 / (p : ℝ)) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  exact neg_log_one_sub_bounds h0 h1

lemma aP_nonneg (n : ℕ) : 0 ≤ aP n := by
  unfold aP
  split_ifs with h
  · exact le_trans (by positivity) (cp_bounds h).1
  · exact le_rfl

lemma aP_le (n : ℕ) : aP n ≤ 2 / (n : ℝ) := by
  unfold aP
  split_ifs with h
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h.two_le
    have hb := (cp_bounds h).2
    have : 2 * (1 / (n : ℝ)) ^ 2 ≤ 1 / (n : ℝ) := by
      rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    calc cp n ≤ 1 / (n : ℝ) + 1 / n := by linarith
      _ = 2 / n := by ring
  · positivity

lemma natCast_rpow_one_sub {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    (n : ℝ) ^ (1 - s) = n * (n : ℝ) ^ (-s) := by
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [sub_eq_add_neg, rpow_add this, rpow_one]

lemma aP_mul_rpow_le {s : ℝ} (n : ℕ) : aP n * (n : ℝ) ^ (1 - s) ≤ 2 * (n : ℝ) ^ (-s) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aP, Nat.not_prime_zero]; positivity
  rw [natCast_rpow_one_sub hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := aP_le n
  have hr : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  calc aP n * (n * (n : ℝ) ^ (-s)) = (aP n * n) * (n : ℝ) ^ (-s) := by ring
    _ ≤ 2 * (n : ℝ) ^ (-s) := by
        apply mul_le_mul_of_nonneg_right _ hr
        rw [le_div_iff₀ hnpos] at h; linarith

lemma summable_aP_mul_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => aP n * (n : ℝ) ^ (1 - s)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (aP_nonneg n) (by positivity))
    (fun n => aP_mul_rpow_le n) ?_
  exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2

/-- `primeSum cp t = Σ_{n ≤ ⌊t⌋} aP n`. -/
lemma primeSum_cp_eq (t : ℝ) : primeSum cp t = ∑ n ∈ Finset.Iic ⌊t⌋₊, aP n := by
  unfold primeSum aP
  rw [Finset.sum_filter]

/-- The `n`-th term of the series for `P(t) t^{-s}`. -/
noncomputable def mellinTerm (s : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  aP n * (Ici (n : ℝ)).indicator (fun t => t ^ (-s)) t

lemma primeSum_mul_rpow_eq_tsum (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    primeSum cp t * t ^ (-s) = ∑' n, mellinTerm s n t := by
  rw [tsum_eq_sum (s := Finset.Iic ⌊t⌋₊)]
  · rw [primeSum_cp_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : (n : ℝ) ≤ t := (Nat.le_floor_iff ht).mp (Finset.mem_Iic.mp hn)
    simp [mellinTerm, indicator_of_mem (show t ∈ Ici (n : ℝ) from this)]
  · intro n hn
    have : ⌊t⌋₊ < n := by simpa using hn
    have : t < n := Nat.lt_of_floor_lt this
    simp [mellinTerm, indicator_of_notMem (show t ∉ Ici (n : ℝ) by simpa using this)]

lemma mellinTerm_nonneg (s : ℝ) (n : ℕ) {t : ℝ} : 0 ≤ mellinTerm s n t := by
  unfold mellinTerm
  apply mul_nonneg (aP_nonneg n)
  by_cases h : t ∈ Ici (n : ℝ)
  · rw [indicator_of_mem h]
    have : (0 : ℝ) ≤ t := le_trans (Nat.cast_nonneg n) h
    positivity
  · rw [indicator_of_notMem h]

lemma integrableOn_rpow_neg {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

lemma integrable_mellinTerm {s : ℝ} (hs : 1 < s) (n : ℕ) :
    IntegrableOn (mellinTerm s n) (Ioi 1) :=
  ((integrableOn_rpow_neg hs).indicator measurableSet_Ici).const_mul (aP n)

lemma integral_mellinTerm {s : ℝ} (hs : 1 < s) (n : ℕ) :
    ∫ t in Ioi 1, mellinTerm s n t = aP n * (n : ℝ) ^ (1 - s) / (s - 1) := by
  unfold mellinTerm
  rw [integral_const_mul, setIntegral_indicator measurableSet_Ici]
  by_cases hp : n.Prime
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
    have hsub : Ioi (1 : ℝ) ∩ Ici (n : ℝ) = Ici (n : ℝ) :=
      inter_eq_right.mpr (fun x hx => lt_of_lt_of_le (show (1:ℝ) < n by linarith) (mem_Ici.mp hx))
    rw [hsub, integral_Ici_eq_integral_Ioi,
      integral_Ioi_rpow_of_lt (by linarith) (by linarith)]
    have e : -s + 1 = -(s - 1) := by ring
    have e2 : 1 - s = -s + 1 := by ring
    rw [e2, e, div_neg, neg_div, neg_neg, mul_div_assoc]
  · simp [aP, hp]

/-- **Mellin transform of the Mertens sum.** -/
theorem mellin_primeSum {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => primeSum cp t * t ^ (-s)) (Ioi 1) ∧
    (s - 1) * ∫ t in Ioi 1, primeSum cp t * t ^ (-s) = ∑' n : ℕ, aP n * (n : ℝ) ^ (1 - s) := by
  have hs0 : 0 < s - 1 := by linarith
  have hnorm : ∀ n, ∫ t in Ioi 1, ‖mellinTerm s n t‖ = aP n * (n : ℝ) ^ (1 - s) / (s - 1) := by
    intro n
    rw [← integral_mellinTerm hs n]
    exact integral_congr_ae (Eventually.of_forall fun t =>
      Real.norm_of_nonneg (mellinTerm_nonneg s n))
  have hsum : Summable fun n => ∫ t in Ioi 1, ‖mellinTerm s n t‖ := by
    simp_rw [hnorm]
    exact (summable_aP_mul_rpow hs).div_const _
  have hHas := hasSum_integral_of_summable_integral_norm (integrable_mellinTerm hs) hsum
  have heq : ∫ t in Ioi 1, primeSum cp t * t ^ (-s) = ∫ t in Ioi 1, ∑' n, mellinTerm s n t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      primeSum_mul_rpow_eq_tsum s (le_of_lt (lt_trans zero_lt_one ht))
  have hval : ∫ t in Ioi 1, ∑' n, mellinTerm s n t
      = (∑' n : ℕ, aP n * (n : ℝ) ^ (1 - s)) / (s - 1) := by
    rw [← hHas.tsum_eq]
    simp_rw [integral_mellinTerm hs]
    rw [tsum_div_const]
  have hpos : 0 < ∑' n : ℕ, aP n * (n : ℝ) ^ (1 - s) := by
    refine (summable_aP_mul_rpow hs).tsum_pos
      (fun n => mul_nonneg (aP_nonneg n) (by positivity)) 2 ?_
    have : 0 < aP 2 := by
      simp only [aP, Nat.prime_two, ↓reduceIte]
      exact lt_of_lt_of_le (by norm_num) (cp_bounds Nat.prime_two).1
    positivity
  refine ⟨?_, ?_⟩
  · have hint : IntegrableOn (fun t => ∑' n, mellinTerm s n t) (Ioi 1) := by
      apply Integrable.of_integral_ne_zero
      rw [hval]; positivity
    refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
    exact (primeSum_mul_rpow_eq_tsum s (le_of_lt (lt_trans zero_lt_one ht))).symm
  · rw [heq, hval]
    field_simp

end Robin
