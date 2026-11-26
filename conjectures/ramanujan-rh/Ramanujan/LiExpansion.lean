import Schoenfeld.LogIntegral

/-!
# The asymptotic expansion of `li` with explicit remainder

For `1 < a ≤ y` write `I m a y = ∫ₐʸ dt / log^m t`. Integration by parts gives

  `I m a y = y / log^m y − a / log^m a + m · I (m+1) a y`,

and iterating it `n` times,

  `li y = li a + Σ_{k<n} k! (y / log^{k+1} y − a / log^{k+1} a) + n! · I (n+1) a y`.

The remainder satisfies `0 ≤ I m a y` and, for `m < log a`,
`I m a y ≤ (y / log^m y) / (1 − m / log a)`.
-/

namespace Ramanujan

open Real MeasureTheory intervalIntegral

/-- `I m a y = ∫ₐʸ dt / (log t)^m`. -/
noncomputable def I (m : ℕ) (a y : ℝ) : ℝ := ∫ t in a..y, 1 / Real.log t ^ m

lemma continuousOn_inv_log_pow (m : ℕ) {s : Set ℝ} (hs : ∀ t ∈ s, 1 < t) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t ^ m) s := by
  intro t ht
  have h1 := hs t ht
  have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
  exact (continuousAt_const.div ((Real.continuousAt_log (by linarith)).pow m)
    (pow_ne_zero _ hl)).continuousWithinAt

lemma intervalIntegrable_inv_log_pow (m : ℕ) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ m) volume a y := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_inv_log_pow
  intro t ht
  rw [Set.uIcc_of_le hay] at ht
  linarith [ht.1]

/-- The derivative of `t / log^m t`. -/
lemma hasDerivAt_div_log_pow (m : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => t / Real.log t ^ m)
      (1 / Real.log t ^ m - m * (1 / Real.log t ^ (m + 1))) t := by
  have hl : 0 < Real.log t := Real.log_pos ht
  have ht0 : t ≠ 0 := by linarith
  have h := (hasDerivAt_id t).div ((Real.hasDerivAt_log ht0).pow m) (pow_ne_zero m hl.ne')
  convert h using 1
  rcases m with _ | k
  · simp
  · simp only [id, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    field_simp
    ring

/-- Integration by parts: `I m = y/log^m y − a/log^m a + m · I (m+1)`. -/
lemma I_ibp (m : ℕ) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) :
    I m a y = y / Real.log y ^ m - a / Real.log a ^ m + m * I (m + 1) a y := by
  have hderiv : ∀ t ∈ Set.uIcc a y, HasDerivAt (fun t : ℝ => t / Real.log t ^ m)
      (1 / Real.log t ^ m - m * (1 / Real.log t ^ (m + 1))) t := by
    intro t ht
    rw [Set.uIcc_of_le hay] at ht
    exact hasDerivAt_div_log_pow m (by linarith [ht.1])
  have hint : IntervalIntegrable
      (fun t : ℝ => 1 / Real.log t ^ m - m * (1 / Real.log t ^ (m + 1))) volume a y :=
    (intervalIntegrable_inv_log_pow m ha hay).sub
      ((intervalIntegrable_inv_log_pow (m + 1) ha hay).const_mul _)
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [integral_sub (intervalIntegrable_inv_log_pow m ha hay)
    ((intervalIntegrable_inv_log_pow (m + 1) ha hay).const_mul _),
    integral_const_mul] at hftc
  unfold I
  linarith

lemma I_nonneg (m : ℕ) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) : 0 ≤ I m a y := by
  unfold I
  apply integral_nonneg hay
  intro t ht
  have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  positivity

/-- `I (m+1) ≤ I m / log a`. -/
lemma I_succ_le (m : ℕ) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) :
    I (m + 1) a y ≤ I m a y / Real.log a := by
  have hla : 0 < Real.log a := Real.log_pos ha
  rw [le_div_iff₀ hla]
  unfold I
  rw [← integral_mul_const]
  apply integral_mono_on hay (intervalIntegrable_inv_log_pow (m + 1) ha hay)
    ((intervalIntegrable_inv_log_pow m ha hay).mul_const _)
  intro t ht
  have hlt : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
  have hl : 0 < Real.log t := by linarith
  rw [pow_succ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity),
    one_mul]
  exact mul_le_mul_of_nonneg_left hlt (by positivity)

/-- The remainder bound `I m · (1 − m/log a) ≤ y / log^m y`. -/
lemma I_le (m : ℕ) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) :
    I m a y * (1 - m / Real.log a) ≤ y / Real.log y ^ m := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have h1 := I_ibp m ha hay
  have h2 := I_succ_le m ha hay
  have h3 : 0 ≤ a / Real.log a ^ m := by have := ha.le; positivity
  have h4 : (m : ℝ) * I (m + 1) a y ≤ m * (I m a y / Real.log a) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m)
  have h5 : I m a y * (1 - m / Real.log a) = I m a y - m * (I m a y / Real.log a) := by ring
  linarith

/-- The `n`-fold expansion of `I 1`. -/
lemma I_one_expansion (n : ℕ) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) :
    I 1 a y = (∑ k ∈ Finset.range n, (k.factorial : ℝ) *
        (y / Real.log y ^ (k + 1) - a / Real.log a ^ (k + 1))) +
      (n.factorial : ℝ) * I (n + 1) a y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, I_ibp (n + 1) ha hay, Nat.factorial_succ]
    push_cast
    ring

/-- `li y = li a + I 1 a y` for `2 ≤ a ≤ y`. -/
lemma logIntegral_eq (a y : ℝ) (ha : 2 ≤ a) (hay : a ≤ y) :
    Real.logIntegral y = Real.logIntegral a + I 1 a y := by
  unfold Real.logIntegral I
  simp only [pow_one]
  have h1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 a := by
    have := intervalIntegrable_inv_log_pow 1 (by norm_num : (1 : ℝ) < 2) ha
    simpa using this
  have h2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a y := by
    have := intervalIntegrable_inv_log_pow 1 (by linarith : (1 : ℝ) < a) hay
    simpa using this
  rw [← integral_add_adjacent_intervals h1 h2]
  ring

/-- `li(2) ≤ 2`. -/
lemma logIntegralTwo_le_two : Real.logIntegralTwo ≤ 2 := by
  unfold Real.logIntegralTwo
  have h : ∫ u in Set.Ioo (0 : ℝ) 1, (1 / Real.log (1 + u) + 1 / Real.log (1 - u)) ≤
      ∫ _ in Set.Ioo (0 : ℝ) 1, (2 : ℝ) := by
    apply setIntegral_mono_on Real.logIntegralTwo_integrand_integrableOn
      (integrableOn_const (by simp) (by simp)) measurableSet_Ioo
    intro u hu
    exact Real.logIntegralTwo_integrand_le_two hu.1 hu.2
  simpa [Real.volume_Ioo] using h

/-- `0 ≤ li a ≤ 2a` for `a ≥ 2`. -/
lemma logIntegral_bounds {a : ℝ} (ha : 2 ≤ a) :
    0 ≤ Real.logIntegral a ∧ Real.logIntegral a ≤ 2 * a := by
  constructor
  · have := Real.logIntegralTwo_le_logIntegral ha
    have := Real.logIntegral_two_pos
    rw [Real.logIntegral_two] at this
    linarith
  · have hl2 := Real.log_two_gt_d9
    have hint : ∫ t in (2 : ℝ)..a, 1 / Real.log t ≤ ∫ _ in (2 : ℝ)..a, (2 : ℝ) := by
      apply integral_mono_on ha
      · have := intervalIntegrable_inv_log_pow 1 (by norm_num : (1 : ℝ) < 2) ha
        simpa using this
      · exact intervalIntegrable_const
      intro t ht
      have : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
      rw [div_le_iff₀ (by linarith)]
      linarith
    simp only [integral_const, smul_eq_mul] at hint
    have := logIntegralTwo_le_two
    unfold Real.logIntegral
    linarith

end Ramanujan
