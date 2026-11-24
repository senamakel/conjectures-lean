import Schoenfeld.ZeroSums

/-!
# The zero sum `F(T) = Σ_ρ m · min(1/|ρ|, T/|ρ|²)` under RH

`F(T)` is what the differenced explicit formula leaves (`Schoenfeld/PsiInt.lean`). Two bounds:

* `fmin_tsum_le_triv`: `F(T) ≤ T/20`, from `Σ m/|ρ|² < 1/20` alone;
* `fmin_tsum_le`: for `T ≥ 2`, `F(T) ≤ 0.9 · Jb(10T) + 2 Vb(T) + 2.75 Vb(5)`, where
  `Vb(a) = ½ log a − ½ log 2π + (12/5)/a` bounds the Poisson sum `Σ m a/(a²+γ²)`
  (`kern_le`) and `Jb(A) = ∫₂ᴬ Vb(a)/a da = ¼ log² A − ½ log 2π log A − (12/5)/A − (…)(2)`.

The pointwise inequality behind the second bound, for a zero `ρ = 1/2 + iγ` (`|ρ|² ≥ 20`):

* `|γ| ≥ T`: `T/|ρ|² ≤ 2 · T/(T² + γ²)`;
* `6 ≤ |γ| < T`: `1/|γ| ≤ 0.9 ∫₂^{10T} da/(a² + γ²)`, since the integral is
  `(arctan(10T/|γ|) − arctan(2/|γ|))/|γ| ≥ (π/2 − 1/10 − 1/3)/|γ|`;
* `|γ| < 6`: `1/|ρ| ≤ 1/√20 ≤ 2.75 · 5/(25 + γ²)`.

Summing over the zeros and exchanging sum and integral (dominated convergence) turns the middle
term into `∫₂^{10T} (Σ m a/(a²+γ²)) da/a ≤ ∫₂^{10T} Vb(a)/a da = Jb(10T)`.
-/

namespace Schoenfeld

open Complex Real MeasureTheory

/-- `m · min(1/|ρ|, T/|ρ|²)`. -/
noncomputable def fmin (T : ℝ) (ρ : Zeros) : ℝ :=
  mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2)

/-- The bound `½ log a − ½ log 2π + (12/5)/a` for the Poisson sum. -/
noncomputable def Vb (a : ℝ) : ℝ := Real.log a / 2 - Real.log (2 * π) / 2 + 12 / 5 / a

/-- An antiderivative of `Vb(a)/a`. -/
noncomputable def Jp (a : ℝ) : ℝ := Real.log a ^ 2 / 4 - Real.log (2 * π) / 2 * Real.log a - 12 / 5 / a

/-- `∫₂ᴬ Vb(a)/a da`. -/
noncomputable def Jb (A : ℝ) : ℝ := Jp A - Jp 2

lemma fmin_nonneg {T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) : 0 ≤ fmin T ρ :=
  mul_nonneg (mult_nonneg ρ) (le_min (by positivity) (by positivity))

lemma fmin_le_triv {T : ℝ} (_hT : 0 ≤ T) (ρ : Zeros) :
    fmin T ρ ≤ T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  unfold fmin
  calc mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ mult ρ * (T / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (mult_nonneg ρ)
    _ = _ := by ring

theorem fmin_summable (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) : Summable (fmin T) :=
  Summable.of_nonneg_of_le (fmin_nonneg hT) (fmin_le_triv hT) ((zeroSum_summable hRH).mul_left T)

theorem fmin_tsum_le_triv (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    ∑' ρ, fmin T ρ ≤ T / 20 := by
  calc ∑' ρ, fmin T ρ ≤ ∑' ρ, T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) :=
        (fmin_summable hRH hT).tsum_le_tsum (fmin_le_triv hT) ((zeroSum_summable hRH).mul_left T)
    _ = T * ∑' ρ, mult ρ / ‖(ρ : ℂ)‖ ^ 2 := tsum_mul_left
    _ ≤ T * (1 / 20) := mul_le_mul_of_nonneg_left (zeroSum_le hRH) hT
    _ = T / 20 := by ring

theorem fmin_tsum_mono (hRH : RiemannHypothesis) {T T' : ℝ} (hT : 0 ≤ T) (hTT : T ≤ T') :
    ∑' ρ, fmin T ρ ≤ ∑' ρ, fmin T' ρ := by
  refine (fmin_summable hRH hT).tsum_le_tsum (fun ρ => ?_) (fmin_summable hRH (hT.trans hTT))
  unfold fmin
  gcongr
  exact mult_nonneg ρ

/-! ### The integral of the kernel -/

/-- `m/(a² + γ²)`, the integrand. -/
noncomputable def kint (ρ : Zeros) (a : ℝ) : ℝ := mult ρ / (a ^ 2 + (ρ : ℂ).im ^ 2)

lemma im_sq_ge (hRH : RiemannHypothesis) (ρ : Zeros) :
    ‖(ρ : ℂ)‖ ^ 2 / 2 ≤ (ρ : ℂ).im ^ 2 := by
  have h1 := normSq_of_re (re_eq_half hRH ρ)
  have h2 := twenty_le_normSq hRH ρ
  linarith

lemma im_sq_pos (hRH : RiemannHypothesis) (ρ : Zeros) : 0 < (ρ : ℂ).im ^ 2 := by
  have := im_sq_ge hRH ρ; have := twenty_le_normSq hRH ρ; linarith

lemma integral_kint (hRH : RiemannHypothesis) (ρ : Zeros) (A : ℝ) :
    ∫ a in (2 : ℝ)..A, kint ρ a
      = mult ρ * ((Real.arctan (A / |(ρ : ℂ).im|) - Real.arctan (2 / |(ρ : ℂ).im|)) / |(ρ : ℂ).im|) := by
  set g := |(ρ : ℂ).im| with hg
  have hg0 : 0 < g := by
    have := im_sq_pos hRH ρ
    rw [hg]; exact abs_pos.mpr (fun h => by rw [h] at this; norm_num at this)
  have hgg : (ρ : ℂ).im ^ 2 = g ^ 2 := by rw [hg, sq_abs]
  have e : ∀ a : ℝ, kint ρ a = mult ρ / g ^ 2 * (1 + (a / g) ^ 2)⁻¹ := by
    intro a; unfold kint; rw [hgg]; field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div
    (fun x => (1 + x ^ 2)⁻¹) hg0.ne', integral_inv_one_add_sq, smul_eq_mul]
  field_simp

lemma norm_kint_le (hRH : RiemannHypothesis) (ρ : Zeros) (a : ℝ) :
    ‖kint ρ a‖ ≤ 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have h1 := im_sq_ge hRH ρ
  have h2 := twenty_le_normSq hRH ρ
  have hp : 0 < (ρ : ℂ).im ^ 2 := im_sq_pos hRH ρ
  rw [Real.norm_eq_abs, kint, abs_of_nonneg (div_nonneg (mult_nonneg ρ) (by positivity)),
    div_le_iff₀ (by positivity)]
  have hm := mult_nonneg ρ
  rw [show 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) * (a ^ 2 + (ρ : ℂ).im ^ 2)
      = mult ρ * (2 * (a ^ 2 + (ρ : ℂ).im ^ 2) / ‖(ρ : ℂ)‖ ^ 2) by ring]
  refine le_mul_of_one_le_right hm ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg a]

lemma Vb_pos {a : ℝ} (ha : 2 ≤ a) : 0 < Vb a := by
  unfold Vb
  have ha0 : 0 < a := by linarith
  -- `log (a/2π) ≥ 1 − 2π/a` and `π < 3.15`
  have h := Real.log_le_sub_one_of_pos (show 0 < 2 * π / a by positivity)
  rw [Real.log_div (by positivity) ha0.ne'] at h
  have hpi := Real.pi_lt_d2
  have : 2 * π / a < 6.3 / a := div_lt_div_of_pos_right (by linarith) ha0
  have h2 : 6.3 / a / 2 ≤ 12 / 5 / a + 1 / 2 := by
    rw [div_div, div_add' _ _ _ ha0.ne', div_le_div_iff₀ (by positivity) ha0]; nlinarith
  linarith

lemma hasDerivAt_Jp {a : ℝ} (ha : 0 < a) : HasDerivAt Jp (Vb a / a) a := by
  have hl := Real.hasDerivAt_log ha.ne'
  have h1 := (hl.pow 2).div_const 4
  have h2 := hl.const_mul (Real.log (2 * π) / 2)
  have h3 := (hasDerivAt_inv ha.ne').const_mul (12 / 5 : ℝ)
  have := (h1.sub h2).sub h3
  convert this using 1
  · funext x; simp [Jp, div_eq_mul_inv]
  · unfold Vb; field_simp; ring

theorem integral_Vb_div (A : ℝ) (hA : 2 ≤ A) : ∫ a in (2 : ℝ)..A, Vb a / a = Jb A := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Jp)]
  · rfl
  · intro x hx
    rw [Set.uIcc_of_le hA] at hx
    exact hasDerivAt_Jp (by linarith [hx.1])
  · refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    unfold Vb
    exact ((((Real.continuousAt_log hx0).div_const _).sub continuousAt_const).add
      (continuousAt_const.div continuousAt_id hx0)).div continuousAt_id hx0 |>.continuousWithinAt

/-- `Σ_ρ ∫₂ᴬ m/(a²+γ²) da ≤ Jb(A)`. -/
theorem tsum_integral_kint_le (hRH : RiemannHypothesis) {A : ℝ} (hA : 2 ≤ A) :
    Summable (fun ρ : Zeros => ∫ a in (2 : ℝ)..A, kint ρ a) ∧
    ∑' ρ : Zeros, ∫ a in (2 : ℝ)..A, kint ρ a ≤ Jb A := by
  set f : ℝ → ℝ := fun a => ∑' ρ : Zeros, kint ρ a
  have hS := zeroSum_summable hRH
  have hlim : ∀ a : ℝ, 0 < a → HasSum (fun ρ => kint ρ a) (f a) := by
    intro a ha
    refine Summable.hasSum ?_
    refine Summable.of_norm_bounded (hS.mul_left 2) (fun ρ => norm_kint_le hRH ρ a)
  have hsum : HasSum (fun ρ : Zeros => ∫ a in (2 : ℝ)..A, kint ρ a) (∫ a in (2 : ℝ)..A, f a) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun ρ _ => 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2)) (fun ρ => ?_) (fun ρ => ?_) ?_ ?_ ?_
    · have hd : Continuous fun a : ℝ => a ^ 2 + (ρ : ℂ).im ^ 2 := by fun_prop
      have hne : ∀ a : ℝ, a ^ 2 + (ρ : ℂ).im ^ 2 ≠ 0 := fun a => by
        have := im_sq_pos hRH ρ; have := sq_nonneg a; exact ne_of_gt (by linarith)
      have hc : Continuous fun a : ℝ => mult ρ / (a ^ 2 + (ρ : ℂ).im ^ 2) :=
        continuous_const.div hd hne
      exact hc.aestronglyMeasurable
    · exact ae_of_all _ fun a _ => norm_kint_le hRH ρ a
    · exact ae_of_all _ fun a _ => hS.mul_left 2
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun a ha => hlim a ?_
      rw [Set.uIoc_of_le hA] at ha; linarith [ha.1]
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, ← integral_Vb_div A hA]
  have hfle : ∀ a ∈ Set.Icc (2 : ℝ) A, f a ≤ Vb a / a := by
    intro a ha
    have ha0 : 0 < a := by linarith [ha.1]
    have hk := kern_hasSum hRH (a := a) (by linarith [ha.1])
    have hk' : HasSum (fun ρ => kint ρ a) ((∑' ρ : Zeros, kern a ρ) / a) := by
      rw [hk.tsum_eq]
      convert hk.div_const a using 1
      funext ρ; unfold kint kern; field_simp
    rw [(hlim a ha0).unique hk']
    exact div_le_div_of_nonneg_right (kern_le hRH ha.1) ha0.le
  by_cases hint : IntervalIntegrable f volume 2 A
  · refine intervalIntegral.integral_mono_on hA hint ?_ hfle
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    unfold Vb
    exact ((((Real.continuousAt_log hx0).div_const _).sub continuousAt_const).add
      (continuousAt_const.div continuousAt_id hx0)).div continuousAt_id hx0 |>.continuousWithinAt
  · rw [intervalIntegral.integral_undef hint]
    refine intervalIntegral.integral_nonneg hA fun x hx => ?_
    exact div_nonneg (Vb_pos hx.1).le (by linarith [hx.1])

/-! ### The pointwise inequality -/

lemma arctan_ge_of_le {x : ℝ} (hx : 10 ≤ x) : π / 2 - 1 / 10 ≤ Real.arctan x := by
  have h0 : 0 < x := by linarith
  have := arctan_inv_of_pos h0
  have h1 : Real.arctan x⁻¹ ≤ x⁻¹ := arctan_le_self (by positivity)
  have h2 : x⁻¹ ≤ 1 / 10 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx
  linarith

theorem fmin_le_pointwise (hRH : RiemannHypothesis) {T : ℝ} (hT : 2 ≤ T) (ρ : Zeros) :
    fmin T ρ ≤ 0.9 * (∫ a in (2 : ℝ)..10 * T, kint ρ a) + 2 * kern T ρ + 2.75 * kern 5 ρ := by
  set g := |(ρ : ℂ).im| with hg
  have hp := im_sq_pos hRH ρ
  have hn20 := twenty_le_normSq hRH ρ
  have hnorm := normSq_of_re (re_eq_half hRH ρ)
  have hgg : (ρ : ℂ).im ^ 2 = g ^ 2 := by rw [hg, sq_abs]
  have hg0 : 0 < g := by
    rw [hg]; exact abs_pos.mpr (fun h => by rw [h] at hp; norm_num at hp)
  have hm := mult_nonneg ρ
  have hN : 0 < ‖(ρ : ℂ)‖ := by nlinarith [norm_nonneg (ρ : ℂ)]
  have hgN : g ≤ ‖(ρ : ℂ)‖ := by
    have : g ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by rw [hnorm, ← hgg]; linarith
    exact (pow_le_pow_iff_left₀ hg0.le hN.le two_ne_zero).mp this
  have hI : 0 ≤ ∫ a in (2 : ℝ)..10 * T, kint ρ a := by
    refine intervalIntegral.integral_nonneg (by linarith) fun a _ => ?_
    unfold kint; positivity
  have hkT : 0 ≤ kern T ρ := kern_nonneg (by linarith) ρ
  have hk5 : 0 ≤ kern 5 ρ := kern_nonneg (by norm_num) ρ
  unfold fmin
  rcases le_or_gt T g with h1 | h1
  · -- `|γ| ≥ T`
    have : mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ 2 * kern T ρ := by
      refine (mul_le_mul_of_nonneg_left (min_le_right _ _) hm).trans ?_
      unfold kern
      rw [hgg]
      have hT0 : 0 < T := by linarith
      rw [show 2 * (mult ρ * (T / (T ^ 2 + g ^ 2))) = mult ρ * (2 * T / (T ^ 2 + g ^ 2)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hm
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : T ^ 2 + g ^ 2 ≤ 2 * g ^ 2 := by nlinarith
      nlinarith
    linarith
  rcases le_or_gt 6 g with h2 | h2
  · -- `6 ≤ |γ| < T`
    have : mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ 0.9 * ∫ a in (2 : ℝ)..10 * T, kint ρ a := by
      refine (mul_le_mul_of_nonneg_left (min_le_left _ _) hm).trans ?_
      rw [integral_kint hRH ρ, ← hg]
      have ha1 : π / 2 - 1 / 10 ≤ Real.arctan (10 * T / g) := by
        apply arctan_ge_of_le
        rw [le_div_iff₀ hg0]; nlinarith
      have ha2 : Real.arctan (2 / g) ≤ 1 / 3 := by
        refine (arctan_le_self (by positivity)).trans ?_
        rw [div_le_div_iff₀ hg0 (by norm_num)]; linarith
      have hpi := Real.pi_gt_d2
      have hkey : 1 / ‖(ρ : ℂ)‖ ≤ 0.9 * ((Real.arctan (10 * T / g) - Real.arctan (2 / g)) / g) := by
        rw [mul_div_assoc', le_div_iff₀ hg0, one_div, inv_mul_eq_div, div_le_iff₀ hN]
        nlinarith
      nlinarith
    linarith
  · -- `|γ| < 6`
    have : mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ 2.75 * kern 5 ρ := by
      refine (mul_le_mul_of_nonneg_left (min_le_left _ _) hm).trans ?_
      unfold kern
      rw [show 2.75 * (mult ρ * (5 / (5 ^ 2 + (ρ : ℂ).im ^ 2)))
        = mult ρ * (2.75 * 5 / (5 ^ 2 + (ρ : ℂ).im ^ 2)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hm
      rw [div_le_div_iff₀ hN (by positivity), hgg]
      -- `25 + g² ≤ 61 ≤ 13.75 · √20 ≤ 13.75 ‖ρ‖`
      have hg6 : g ^ 2 < 36 := by nlinarith
      have h20 : (4.47 : ℝ) ≤ ‖(ρ : ℂ)‖ := by nlinarith
      nlinarith
    linarith

theorem fmin_tsum_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 2 ≤ T) :
    ∑' ρ, fmin T ρ ≤ 0.9 * Jb (10 * T) + 2 * Vb T + 2.75 * Vb 5 := by
  obtain ⟨hIs, hIle⟩ := tsum_integral_kint_le hRH (A := 10 * T) (by linarith)
  have hKT := (kern_hasSum hRH (a := T) (by linarith)).summable
  have hK5 := (kern_hasSum hRH (a := 5) (by norm_num)).summable
  have hsum := ((hIs.mul_left 0.9).add (hKT.mul_left 2)).add (hK5.mul_left 2.75)
  calc ∑' ρ, fmin T ρ
      ≤ ∑' ρ, (0.9 * (∫ a in (2 : ℝ)..10 * T, kint ρ a) + 2 * kern T ρ + 2.75 * kern 5 ρ) :=
        (fmin_summable hRH (by linarith)).tsum_le_tsum (fmin_le_pointwise hRH hT) hsum
    _ = 0.9 * (∑' ρ, ∫ a in (2 : ℝ)..10 * T, kint ρ a) + 2 * (∑' ρ, kern T ρ)
          + 2.75 * ∑' ρ, kern 5 ρ := by
        rw [Summable.tsum_add ((hIs.mul_left 0.9).add (hKT.mul_left 2)) (hK5.mul_left 2.75),
          Summable.tsum_add (hIs.mul_left 0.9) (hKT.mul_left 2), tsum_mul_left, tsum_mul_left,
          tsum_mul_left]
    _ ≤ 0.9 * Jb (10 * T) + 2 * Vb T + 2.75 * Vb 5 := by
        have := kern_le hRH (a := T) hT
        have := kern_le hRH (a := 5) (by norm_num)
        unfold Vb
        nlinarith

end Schoenfeld
