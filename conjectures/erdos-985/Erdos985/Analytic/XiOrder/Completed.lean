import Erdos985.Analytic.XiOrder.MellinBound

/-!
# Growth of the completed Dirichlet L-function

For a non-trivial Dirichlet character `χ`, `completedLFunction χ` lies in the class `LogGrowth`.
-/

namespace Erdos985.Analytic.XiOrderAux

open Real Set Filter Asymptotics HurwitzZeta

lemma exp_bound_of_isBigO {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (h : F =O[atTop] fun x => exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 < t → |F t| ≤ C * exp (-p * t) := by
  obtain ⟨c, hc'⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc'
  set T' := max T 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T')).exists_bound_of_continuousOn
    (hc.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
  refine ⟨max (max c 0) (max M 0 * exp (p * T')), by positivity, fun t ht => ?_⟩
  rcases le_total T' t with h1 | h1
  · have := hT t ((le_max_left _ _).trans h1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have h2 := hM t ⟨ht.le, h1⟩
    rw [Real.norm_eq_abs] at h2
    calc |F t| ≤ max M 0 := h2.trans (le_max_left _ _)
      _ ≤ max M 0 * (exp (p * T') * exp (-p * t)) := by
          refine le_mul_of_one_le_right (le_max_right _ _) ?_
          rw [← exp_add, one_le_exp_iff]
          nlinarith
      _ = (max M 0 * exp (p * T')) * exp (-p * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le

lemma combine_bounds {f g : ℝ → ℝ} {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hf : ∀ t, 1 < t → f t ≤ C₁ * exp (-p₁ * t)) (hg : ∀ t, 1 < t → g t ≤ C₂ * exp (-p₂ * t)) :
    ∃ p C, 0 < p ∧ 0 ≤ C ∧ (∀ t, 1 < t → f t ≤ C * exp (-p * t)) ∧
      (∀ t, 1 < t → g t ≤ C * exp (-p * t)) := by
  refine ⟨min p₁ p₂, max C₁ C₂, lt_min hp₁ hp₂, le_max_of_le_left hC₁, fun t ht => ?_,
    fun t ht => ?_⟩
  · refine (hf t ht).trans (mul_le_mul (le_max_left _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_left p₁ p₂]
  · refine (hg t ht).trans (mul_le_mul (le_max_right _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_right p₁ p₂]

lemma even_logGrowth (a : UnitAddCircle) : LogGrowth (hurwitzEvenFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C₁, hC₁, hb₁⟩ := exp_bound_of_isBigO
    ((continuousOn_evenKernel a).sub continuousOn_const) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := exp_bound_of_isBigO
    ((continuousOn_cosKernel a).sub continuousOn_const) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := combine_bounds hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine Λ₀_logGrowth _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · have : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀ =
        ((evenKernel a t - if a = 0 then 1 else 0 : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hf t ht
  · have : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀ =
        ((cosKernel a t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hg t ht

lemma odd_logGrowth (a : UnitAddCircle) : LogGrowth (hurwitzOddFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_oddKernel a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_sinKernel a
  obtain ⟨C₁, hC₁, hb₁⟩ := exp_bound_of_isBigO (continuousOn_oddKernel a) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := exp_bound_of_isBigO (continuousOn_sinKernel a) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := combine_bounds hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine Λ₀_logGrowth _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · simpa [hurwitzOddFEPair, Complex.norm_real] using hf t ht
  · simpa [hurwitzOddFEPair, Complex.norm_real] using hg t ht

lemma completedHurwitzZetaEven₀_logGrowth (a : UnitAddCircle) :
    LogGrowth (completedHurwitzZetaEven₀ a) := by
  refine (((even_logGrowth a).comp (g := fun s => s / 2) le_rfl (fun s => ?_)).mul
    (LogGrowth.const (1 / 2))).congr (fun s => ?_)
  · rw [norm_div, Complex.norm_two, add_zero]
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaEven₀]; ring

lemma completedHurwitzZetaOdd_logGrowth (a : UnitAddCircle) :
    LogGrowth (completedHurwitzZetaOdd a) := by
  refine (((odd_logGrowth a).comp (g := fun s => (s + 1) / 2) zero_le_one (fun s => ?_)).mul
    (LogGrowth.const (1 / 2))).congr (fun s => ?_)
  · rw [norm_div, Complex.norm_two]
    have := norm_add_le s 1
    rw [norm_one] at this
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaOdd, WeakFEPair.Λ, hurwitzOddFEPair_f₀, hurwitzOddFEPair_g₀,
      smul_zero, sub_zero]
    ring

theorem completedLFunction_logGrowth {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : LogGrowth (DirichletCharacter.completedLFunction χ) := by
  have hN : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have h0 : χ 0 = 0 := χ.map_zero' hN
  have hsum : ∑ j, χ j = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpow := LogGrowth.natCast_cpow_neg hNpos
  have hE : LogGrowth (fun s => ∑ j : ZMod N, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) :=
    LogGrowth.sum _ (fun j _ => (LogGrowth.const (χ j)).mul
      (completedHurwitzZetaEven₀_logGrowth _))
  have hO : LogGrowth (fun s => ∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) :=
    LogGrowth.sum _ (fun j _ => (LogGrowth.const (χ j)).mul
      (completedHurwitzZetaOdd_logGrowth _))
  refine ((hpow.mul hE).add (hpow.mul hO)).congr (fun s => ?_)
  rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq]
  simp only [h0, hsum, mul_zero, zero_div, sub_zero, ZMod.completedLFunction₀]

end Erdos985.Analytic.XiOrderAux
