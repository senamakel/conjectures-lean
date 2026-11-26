import Erdos233.Basic

/-!
# Pointwise bounds on `coef δ ρ` for `Re ρ = 1/2`
-/

namespace Erdos233.CoeffAux

open Complex

/-- `φ c t = (1+t)^c` for a real `t`. -/
noncomputable def φ (c : ℂ) (t : ℝ) : ℂ := (((1 + t : ℝ)) : ℂ) ^ c

lemma hasDerivAt_φ (c : ℂ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (φ c) (c * φ (c - 1) t) t := by
  have h1 : HasDerivAt (fun z : ℂ => 1 + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add 1
  have h2 := h1.cpow_const (c := c) (by
    rw [Complex.mem_slitPlane_iff]; left; simp; linarith)
  have h3 := h2.comp_ofReal
  have he : φ c = fun y : ℝ => (1 + (y : ℂ)) ^ c := by
    funext y; simp [φ]
  rw [he]
  convert h3 using 1
  simp [φ]

lemma norm_φ (c : ℂ) {t : ℝ} (ht : -1 < t) : ‖φ c t‖ = (1 + t) ^ c.re :=
  norm_cpow_eq_rpow_re_of_pos (by linarith) c

lemma norm_sub_le_of_deriv {f f' : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (hC : ∀ x ∈ Set.Icc a b, ‖f' x‖ ≤ C) :
    ‖f b - f a‖ ≤ C * (b - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' (fun x hx => (hf x hx).hasDerivWithinAt)
    (fun x hx => hC x (Set.Ico_subset_Icc_self hx)) b ⟨hab, le_rfl⟩

variable {δ : ℝ} {ρ : ℂ}

lemma coef_eq (δ : ℝ) (ρ : ℂ) :
    coef δ ρ = (φ (ρ + 1) (2 * δ) - 2 * φ (ρ + 1) δ + φ (ρ + 1) 0) / (ρ * (ρ + 1)) := by
  simp [coef, φ]

lemma norm_rho_le (hre : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [add_re, one_re, add_im, one_im, add_zero, hre]
  nlinarith

lemma rho_ne_zero (hre : ρ.re = 1 / 2) : ρ ≠ 0 := by
  intro h; rw [h] at hre; simp at hre

lemma rho_add_one_ne_zero (hre : ρ.re = 1 / 2) : ρ + 1 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [hre] at this; norm_num at this

lemma sq_norm_rho (hre : ρ.re = 1 / 2) : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, hre]; ring

/-- Numerator bound. -/
lemma coef_norm_eq (_hre : ρ.re = 1 / 2) (δ : ℝ) :
    ‖coef δ ρ‖ = ‖φ (ρ + 1) (2 * δ) - 2 * φ (ρ + 1) δ + φ (ρ + 1) 0‖ / (‖ρ‖ * ‖ρ + 1‖) := by
  rw [coef_eq, norm_div, norm_mul]

lemma deriv_bound1 (hre : ρ.re = 1 / 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(ρ + 1) * φ (ρ + 1 - 1) t‖ ≤ 2 * ‖ρ + 1‖ := by
  rw [norm_mul, norm_φ _ (by linarith), add_sub_cancel_right, hre, mul_comm]
  gcongr
  calc (1 + t) ^ (1 / 2 : ℝ) ≤ (1 + t) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ 2 := by rw [Real.rpow_one]; linarith

/-- (b) -/
lemma coef_le_first (hre : ρ.re = 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ‖coef δ ρ‖ ≤ 4 * δ / ‖ρ‖ := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  have hd : ∀ a : ℝ, 0 ≤ a → a + δ ≤ 1 →
      ‖φ (ρ + 1) (a + δ) - φ (ρ + 1) a‖ ≤ 2 * ‖ρ + 1‖ * δ := by
    intro a ha0 ha1
    have := norm_sub_le_of_deriv (f := φ (ρ + 1)) (C := 2 * ‖ρ + 1‖) (by linarith : a ≤ a + δ)
      (fun x hx => hasDerivAt_φ _ (by linarith [hx.1]))
      (fun x hx => deriv_bound1 hre (by linarith [hx.1]) (by linarith [hx.2]))
    simpa using this
  have h1 := hd δ hδ0.le (by linarith)
  have h2 := hd 0 le_rfl (by linarith)
  rw [show δ + δ = 2 * δ by ring] at h1
  rw [zero_add] at h2
  rw [coef_norm_eq hre, div_le_div_iff₀ (by positivity) hρ0]
  have : φ (ρ + 1) (2 * δ) - 2 * φ (ρ + 1) δ + φ (ρ + 1) 0
      = (φ (ρ + 1) (2 * δ) - φ (ρ + 1) δ) - (φ (ρ + 1) δ - φ (ρ + 1) 0) := by ring
  rw [this]
  calc _ ≤ (‖φ (ρ + 1) (2 * δ) - φ (ρ + 1) δ‖ + ‖φ (ρ + 1) δ - φ (ρ + 1) 0‖) * ‖ρ‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (2 * ‖ρ + 1‖ * δ + 2 * ‖ρ + 1‖ * δ) * ‖ρ‖ := by gcongr
    _ = 4 * δ * (‖ρ‖ * ‖ρ + 1‖) := by ring

/-- (a) -/
lemma coef_le_second (hre : ρ.re = 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ‖coef δ ρ‖ ≤ δ ^ 2 := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  have hψ : ∀ a : ℝ, 0 ≤ a → ‖φ ρ (a + δ) - φ ρ a‖ ≤ ‖ρ‖ * δ := by
    intro a ha0
    have := norm_sub_le_of_deriv (f := φ ρ) (C := ‖ρ‖) (by linarith : a ≤ a + δ)
      (fun x hx => hasDerivAt_φ _ (by linarith [hx.1]))
      (fun x hx => by
        rw [norm_mul, norm_φ _ (by linarith [hx.1])]
        have : (1 + x) ^ (ρ - 1).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by simp [hre]; norm_num)
        have := norm_nonneg ρ
        nlinarith)
    simpa using this
  set h : ℝ → ℂ := fun t => φ (ρ + 1) (t + δ) - φ (ρ + 1) t with hh
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) δ, HasDerivAt h
      ((ρ + 1) * φ (ρ + 1 - 1) (x + δ) - (ρ + 1) * φ (ρ + 1 - 1) x) x := by
    intro x hx
    have h1 := hasDerivAt_φ (ρ + 1) (t := x + δ) (by linarith [hx.1])
    have h1' : HasDerivAt (fun t => φ (ρ + 1) (t + δ)) ((ρ + 1) * φ (ρ + 1 - 1) (x + δ)) x := by
      simpa using h1.comp_add_const x δ
    exact h1'.sub (hasDerivAt_φ (ρ + 1) (by linarith [hx.1]))
  have hmain := norm_sub_le_of_deriv (f := h) (C := ‖ρ + 1‖ * (‖ρ‖ * δ)) hδ0.le hderiv
    (fun x hx => by
      rw [add_sub_cancel_right, ← mul_sub, norm_mul]
      gcongr
      exact hψ x hx.1)
  have hnum : φ (ρ + 1) (2 * δ) - 2 * φ (ρ + 1) δ + φ (ρ + 1) 0 = h δ - h 0 := by
    simp only [hh, zero_add]; rw [show δ + δ = 2 * δ by ring]; ring
  rw [coef_norm_eq hre, hnum, div_le_iff₀ (by positivity)]
  calc ‖h δ - h 0‖ ≤ ‖ρ + 1‖ * (‖ρ‖ * δ) * (δ - 0) := hmain
    _ = δ ^ 2 * (‖ρ‖ * ‖ρ + 1‖) := by ring

/-- (c) -/
lemma coef_le_trivial (hre : ρ.re = 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ‖coef δ ρ‖ ≤ 52 / (1 + ρ.im ^ 2) := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖φ (ρ + 1) t‖ ≤ 4 := by
    intro t h0 h1
    rw [norm_φ _ (by linarith)]
    simp only [add_re, one_re, hre]
    calc (1 + t) ^ (1 / 2 + 1 : ℝ) ≤ (1 + t) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ ≤ 4 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; nlinarith
  have hnum : ‖φ (ρ + 1) (2 * δ) - 2 * φ (ρ + 1) δ + φ (ρ + 1) 0‖ ≤ 13 := by
    calc _ ≤ ‖φ (ρ + 1) (2 * δ)‖ + ‖2 * φ (ρ + 1) δ‖ + ‖φ (ρ + 1) 0‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ 4 + 2 * 4 + 1 := by
          rw [norm_mul]
          have : ‖φ (ρ + 1) 0‖ = 1 := by simp [φ]
          rw [this]
          gcongr
          · exact hb _ (by linarith) (by linarith)
          · norm_num
          · exact hb _ hδ0.le (by linarith)
      _ = 13 := by norm_num
  have hden : ‖ρ‖ ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (norm_rho_le hre) (norm_nonneg _)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  have hsq := sq_norm_rho hre
  rw [coef_norm_eq hre, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ρ.im]

end Erdos233.CoeffAux
