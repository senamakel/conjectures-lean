import Cramer.MeanSquare.Finite

/-!
# Asymptotic, step 4: the finite approximant and the tail

For a finite set `S` of zeros:

* `binv ρ = m_ρ/ρ` are the coefficients of the finite approximant `wave S binv`, and
  `Σ_ρ ‖binv ρ‖² = Σ_ρ m_ρ²/|ρ|²` converges under RH (`m_ρ ≪ log(|γ| + 2)` by `zero_density`);
* `G δ = wave S (m·acoef δ) + zeroWave (tcoef S δ)` (`zeroWave_split`), and
  `‖wave S (m·acoef δ) − wave S binv‖ ≤ eta S δ → 0` as `δ → 0⁺`;
* the tail has `∫_U^{U+2} ‖zeroWave (tcoef S δ)‖² ≤ C · tailS S` uniformly in `δ` and `U`
  (erdos-233's `mean_value` with `‖acoef δ ρ‖ ≤ 2/‖ρ‖`), and `tailS S → 0` as `S` grows.
-/

namespace Cramer.MeanSq

open Complex Erdos985.Analytic Erdos233 Erdos233.CoeffAux MeasureTheory intervalIntegral
  Filter Topology

/-- Coefficients of the finite approximant: `m_ρ / ρ`. -/
noncomputable def binv (ρ : Zeros) : ℂ := (mult ρ : ℂ) * (1 / (ρ : ℂ))

/-- `m_ρ ‖1/ρ‖² log(|γ| + 2)`. -/
noncomputable def wgt (ρ : Zeros) : ℝ :=
  (mult ρ : ℝ) * ‖1 / (ρ : ℂ)‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)

/-- The weighted tail outside `S`. -/
noncomputable def tailS (S : Finset Zeros) : ℝ := ∑' ρ, ((S : Set Zeros)ᶜ).indicator wgt ρ

/-- The first-difference coefficients outside `S`. -/
noncomputable def tcoef (S : Finset Zeros) (δ : ℝ) (ρ : Zeros) : ℂ :=
  if ρ ∈ S then 0 else acoef δ ρ

/-- `Σ_{ρ ∈ S} m_ρ ‖acoef δ ρ − 1/ρ‖`. -/
noncomputable def eta (S : Finset Zeros) (δ : ℝ) : ℝ :=
  ∑ ρ ∈ S, (mult ρ : ℝ) * ‖acoef δ ρ - 1 / (ρ : ℂ)‖

lemma wgt_nonneg (ρ : Zeros) : 0 ≤ wgt ρ := by
  unfold wgt
  have := Real.log_nonneg (by linarith [abs_nonneg (ρ : ℂ).im] : (1 : ℝ) ≤ |(ρ : ℂ).im| + 2)
  positivity

lemma norm_one_div_sq (hRH : RiemannHypothesis) (ρ : Zeros) :
    ‖1 / (ρ : ℂ)‖ ^ 2 = 1 / (1 / 4 + (ρ : ℂ).im ^ 2) := by
  rw [norm_div, norm_one, div_pow, one_pow, sq_norm_rho (zero_re_of_RH hRH ρ)]

theorem wgt_summable (hRH : RiemannHypothesis) : Summable wgt := by
  obtain ⟨C, -, hC⟩ := sq_log_sums
  exact (hC (fun ρ => 1 / (ρ : ℂ)) 1 zero_le_one fun ρ => (norm_one_div_sq hRH ρ).le).1

theorem tailS_tendsto (hRH : RiemannHypothesis) : Tendsto tailS atTop (𝓝 0) := by
  have hs := wgt_summable hRH
  have he : ∀ S : Finset Zeros, tailS S = ∑' ρ, wgt ρ - ∑ ρ ∈ S, wgt ρ := fun S => by
    rw [← hs.sum_add_tsum_compl (s := S), tailS, ← tsum_subtype]
    ring
  rw [show tailS = fun S => ∑' ρ, wgt ρ - ∑ ρ ∈ S, wgt ρ from funext he]
  have := (tendsto_const_nhds (x := ∑' ρ, wgt ρ)).sub hs.hasSum
  rwa [sub_self] at this

theorem mult_le_log : ∃ C : ℝ, 0 < C ∧ ∀ ρ : Zeros,
    (mult ρ : ℝ) ≤ C * Real.log (|(ρ : ℂ).im| + 2) := by
  obtain ⟨C, hC0, hC⟩ := zero_density
  refine ⟨C, hC0, fun ρ => ?_⟩
  obtain ⟨hs, ht⟩ := hC (ρ : ℂ).im
  have h := hs.le_tsum ρ (fun j _ => by positivity)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    div_one] at h
  exact h.trans ht

theorem binv_summable (hRH : RiemannHypothesis) : Summable fun ρ => ‖binv ρ‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := mult_le_log
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    ((wgt_summable hRH).mul_left C)
  have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
  rw [binv, norm_mul, Complex.norm_natCast, mul_pow, wgt]
  have h1 : (mult ρ : ℝ) ^ 2 ≤ (mult ρ : ℝ) * (C * Real.log (|(ρ : ℂ).im| + 2)) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (hC ρ) hm
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ‖1 / (ρ : ℂ)‖ ^ 2)
  calc (mult ρ : ℝ) ^ 2 * ‖1 / (ρ : ℂ)‖ ^ 2
      ≤ (mult ρ : ℝ) * (C * Real.log (|(ρ : ℂ).im| + 2)) * ‖1 / (ρ : ℂ)‖ ^ 2 := h2
    _ = C * ((mult ρ : ℝ) * ‖1 / (ρ : ℂ)‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) := by ring

lemma wave_term (c : Zeros → ℂ) (ρ : Zeros) (u : ℝ) :
    (mult ρ : ℂ) * c ρ * exp ((((ρ : ℂ).im * u : ℝ) : ℂ) * I) = (mult ρ : ℂ) * c ρ * ex (ρ : ℂ).im u :=
  rfl

/-- `zeroWave c = wave S (m c) + zeroWave (c outside S)`. -/
theorem zeroWave_split (c : Zeros → ℂ) (hc : Summable fun ρ => (mult ρ : ℝ) * ‖c ρ‖)
    (S : Finset Zeros) (u : ℝ) :
    zeroWave c u = wave S (fun ρ => (mult ρ : ℂ) * c ρ) u
      + zeroWave (fun ρ => if ρ ∈ S then 0 else c ρ) u := by
  classical
  set f : Zeros → ℂ := fun ρ => (mult ρ : ℂ) * c ρ * ex (ρ : ℂ).im u with hf
  have hfs : Summable f := by
    refine Summable.of_norm ?_
    refine hc.congr fun ρ => ?_
    simp only [hf, norm_mul, norm_ex, mul_one, Complex.norm_natCast]
  set f₁ : Zeros → ℂ := fun ρ => if ρ ∈ S then f ρ else 0 with hf₁
  set f₂ : Zeros → ℂ := fun ρ => if ρ ∈ S then 0 else f ρ with hf₂
  have hsplit : f = f₁ + f₂ := by
    funext ρ; simp only [hf₁, hf₂, Pi.add_apply]; split_ifs <;> simp
  have h1s : Summable f₁ := summable_of_ne_finset_zero (s := S) fun ρ hρ => by
    simp [hf₁, hρ]
  have h2s : Summable f₂ := by
    have : f₂ = f - f₁ := by rw [hsplit]; ring
    rw [this]; exact hfs.sub h1s
  have ht1 : ∑' ρ, f₁ ρ = ∑ ρ ∈ S, f ρ := by
    rw [tsum_eq_sum (s := S) fun ρ hρ => by simp [hf₁, hρ]]
    exact Finset.sum_congr rfl fun ρ hρ => by simp [hf₁, hρ]
  have hz : zeroWave c u = ∑' ρ, f ρ := rfl
  have hz2 : zeroWave (fun ρ => if ρ ∈ S then 0 else c ρ) u = ∑' ρ, f₂ ρ := by
    unfold zeroWave
    refine tsum_congr fun ρ => ?_
    simp only [hf₂, hf]
    split_ifs <;> simp [ex]
  rw [hz, hz2]
  calc ∑' ρ, f ρ = ∑' ρ, (f₁ ρ + f₂ ρ) := tsum_congr fun ρ => congrFun hsplit ρ
    _ = ∑' ρ, f₁ ρ + ∑' ρ, f₂ ρ := h1s.tsum_add h2s
    _ = wave S (fun ρ => (mult ρ : ℂ) * c ρ) u + ∑' ρ, f₂ ρ := by rw [ht1]; rfl

/-- `‖G δ u − wave S binv u‖ ≤ eta S δ + ‖tail‖`. -/
theorem G_sub_wave (hRH : RiemannHypothesis) (S : Finset Zeros) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (u : ℝ) :
    ‖G δ u - wave S binv u‖ ≤ eta S δ + ‖zeroWave (tcoef S δ) u‖ := by
  obtain ⟨Ca, -, hCa⟩ := acoef_sums hRH
  obtain ⟨hS1, -, -⟩ := hCa δ hδ hδ'
  have hsplit := zeroWave_split (fun ρ => acoef δ ρ) hS1 S u
  have hG : G δ u = wave S (fun ρ => (mult ρ : ℂ) * acoef δ ρ) u + zeroWave (tcoef S δ) u := by
    rw [G, hsplit]; rfl
  rw [hG]
  have hdiff : wave S (fun ρ => (mult ρ : ℂ) * acoef δ ρ) u - wave S binv u
      = ∑ ρ ∈ S, (mult ρ : ℂ) * (acoef δ ρ - 1 / (ρ : ℂ)) * ex (ρ : ℂ).im u := by
    rw [wave, wave, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [binv]; ring
  have hle : ‖wave S (fun ρ => (mult ρ : ℂ) * acoef δ ρ) u - wave S binv u‖ ≤ eta S δ := by
    rw [hdiff, eta]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
    rw [norm_mul, norm_mul, norm_ex, mul_one, Complex.norm_natCast]
  calc ‖wave S (fun ρ => (mult ρ : ℂ) * acoef δ ρ) u + zeroWave (tcoef S δ) u - wave S binv u‖
      = ‖(wave S (fun ρ => (mult ρ : ℂ) * acoef δ ρ) u - wave S binv u)
          + zeroWave (tcoef S δ) u‖ := by ring_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hle le_rfl)

/-- **Tail mean square**, uniform in `δ` and the window. -/
theorem tail_mean (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Zeros) (δ : ℝ),
    0 < δ → δ ≤ 1 / 2 → Continuous (zeroWave (tcoef S δ)) ∧
    ∀ U : ℝ, ∫ u in U..U + 2, ‖zeroWave (tcoef S δ) u‖ ^ 2 ≤ C * tailS S := by
  obtain ⟨Cm, hCm, hM⟩ := mean_value
  obtain ⟨Ca, -, hCa⟩ := acoef_sums hRH
  refine ⟨Cm * 4, by positivity, fun S δ hδ hδ' => ?_⟩
  obtain ⟨hS1, -, -⟩ := hCa δ hδ hδ'
  have hre := zero_re_of_RH hRH
  have hle1 : ∀ ρ, (mult ρ : ℝ) * ‖tcoef S δ ρ‖ ≤ (mult ρ : ℝ) * ‖acoef δ ρ‖ := fun ρ => by
    unfold tcoef; split_ifs <;> simp; positivity
  have hs1 : Summable fun ρ => (mult ρ : ℝ) * ‖tcoef S δ ρ‖ :=
    Summable.of_nonneg_of_le (fun ρ => by positivity) hle1 hS1
  have hpt : ∀ ρ, (mult ρ : ℝ) * ‖tcoef S δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ 4 * ((S : Set Zeros)ᶜ).indicator wgt ρ := fun ρ => by
    unfold tcoef
    by_cases h : ρ ∈ S
    · simp [h]
    · have hin : ρ ∈ ((S : Set Zeros)ᶜ) := by simpa using h
      simp only [h, ↓reduceIte, Set.indicator_of_mem hin, wgt]
      have ha := acoef_le_inv (hre ρ) hδ hδ'
      have hsq : ‖acoef δ ρ‖ ^ 2 ≤ 4 * ‖1 / (ρ : ℂ)‖ ^ 2 := by
        rw [norm_div, norm_one]
        calc ‖acoef δ ρ‖ ^ 2 ≤ (2 / ‖(ρ : ℂ)‖) ^ 2 := by gcongr
          _ = 4 * (1 / ‖(ρ : ℂ)‖) ^ 2 := by ring
      have hl := Real.log_nonneg (by linarith [abs_nonneg (ρ : ℂ).im] :
        (1 : ℝ) ≤ |(ρ : ℂ).im| + 2)
      have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
      calc (mult ρ : ℝ) * ‖acoef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
          ≤ (mult ρ : ℝ) * (4 * ‖1 / (ρ : ℂ)‖ ^ 2) * Real.log (|(ρ : ℂ).im| + 2) := by gcongr
        _ = _ := by ring
  have hind : Summable fun ρ => ((S : Set Zeros)ᶜ).indicator wgt ρ :=
    (wgt_summable hRH).indicator _
  have hs2 : Summable fun ρ => (mult ρ : ℝ) * ‖tcoef S δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2) :=
    Summable.of_nonneg_of_le (fun ρ => by
      have := Real.log_nonneg (by linarith [abs_nonneg (ρ : ℂ).im] :
        (1 : ℝ) ≤ |(ρ : ℂ).im| + 2)
      positivity) hpt (hind.mul_left 4)
  refine ⟨continuous_zeroWave hs1, fun U => (hM _ hs1 hs2 U).trans ?_⟩
  have := hs2.tsum_le_tsum hpt (hind.mul_left 4)
  rw [tsum_mul_left] at this
  rw [tailS, mul_assoc]
  exact mul_le_mul_of_nonneg_left this hCm.le

theorem eta_tendsto (hRH : RiemannHypothesis) (S : Finset Zeros) :
    Tendsto (fun Y : ℝ => eta S (1 / Y)) atTop (𝓝 0) := by
  have hY : Tendsto (fun Y : ℝ => 1 / Y) atTop (𝓝[>] 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero
  have h : Tendsto (fun Y : ℝ => eta S (1 / Y)) atTop
      (𝓝 (∑ ρ ∈ S, (mult ρ : ℝ) * ‖(1 / (ρ : ℂ)) - 1 / (ρ : ℂ)‖)) := by
    unfold eta
    refine tendsto_finsetSum _ fun ρ _ => ?_
    refine Tendsto.const_mul _ (Tendsto.norm (Tendsto.sub_const ?_ _))
    exact (acoef_tendsto (zero_re_of_RH hRH ρ)).comp hY
  simpa using h

end Cramer.MeanSq
