import Erdos233.Selberg.Trapezoid
import Erdos233.Selberg.Waves

/-!
# Size of the trapezoid coefficients `tcoef a σ D ρ` under RH

Take `3/4 ≤ a ≤ 1`, `0 < σ ≤ D ≤ 1/2` and `Re ρ = 1/2`. With `g(t) = t^{ρ+1}` the numerator
of `tcoef` is `g(a+D+σ) − g(a+D) − g(a+σ) + g(a)`, a mixed second difference with steps `σ`
and `D`, all arguments in `[3/4, 2]`. Hence

* `‖tcoef‖ ≤ 2σD` (`|g''| ≤ 2|ρ(ρ+1)|`),
* `‖tcoef‖ ≤ 4σ/|ρ|` (two first differences of step `σ`, `|g'| ≤ 2|ρ+1|`),
* `‖tcoef‖ ≤ 64/(1+γ²)` (trivially),

so `‖tcoef‖² ≤ (4σ²/D²) · w D ⌊|γ|⌋` and `wave_sums` gives
`Σ m_ρ ‖tcoef‖² log(|γ|+2) ≤ C σ² D log²(2/D)` (`tcoef_sums`).
-/

namespace Erdos233

open Complex Erdos985.Analytic Erdos233.CoeffAux

variable {a σ D : ℝ} {ρ : ℂ}

lemma tcoef_eq (a σ D : ℝ) (ρ : ℂ) :
    tcoef a σ D ρ = (φ (ρ + 1) (a - 1 + D + σ) - φ (ρ + 1) (a - 1 + D)
      - φ (ρ + 1) (a - 1 + σ) + φ (ρ + 1) (a - 1)) / (ρ * (ρ + 1)) := by
  simp only [tcoef, φ]
  rw [show (1 : ℝ) + (a - 1 + D + σ) = a + D + σ by ring,
    show (1 : ℝ) + (a - 1 + D) = a + D by ring, show (1 : ℝ) + (a - 1 + σ) = a + σ by ring,
    show (1 : ℝ) + (a - 1) = a by ring]

lemma rpow_neg_half_le {x : ℝ} (hx : 3 / 4 ≤ x) : x ^ (-(1 / 2) : ℝ) ≤ 2 := by
  rcases le_or_gt x 1 with h | h
  · calc x ^ (-(1 / 2) : ℝ) ≤ x ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by linarith) h (by norm_num)
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  · linarith [Real.rpow_le_one_of_one_le_of_nonpos h.le (show (-(1 / 2) : ℝ) ≤ 0 by norm_num)]

lemma rpow_half_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 4) : x ^ (1 / 2 : ℝ) ≤ 2 := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
  linarith

lemma tcoef_le_first (hre : ρ.re = 1 / 2) (ha : 3 / 4 ≤ a) (ha1 : a ≤ 1) (hσ : 0 < σ)
    (hσD : σ ≤ D) (hD : D ≤ 1 / 2) : ‖tcoef a σ D ρ‖ ≤ 2 * σ * D := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  set α := a - 1 with hα
  have hψ : ∀ u : ℝ, -(1 / 4) ≤ u → ‖φ ρ (u + σ) - φ ρ u‖ ≤ 2 * ‖ρ‖ * σ := by
    intro u hu
    have := norm_sub_le_of_deriv (f := φ ρ) (C := 2 * ‖ρ‖) (by linarith : u ≤ u + σ)
      (fun x hx => hasDerivAt_φ _ (by linarith [hx.1]))
      (fun x hx => by
        rw [norm_mul, norm_φ _ (by linarith [hx.1])]
        have : (1 + x) ^ (ρ - 1).re ≤ 2 := by
          rw [show (ρ - 1).re = -(1 / 2) by simp [hre]; norm_num]
          exact rpow_neg_half_le (by linarith [hx.1])
        have := norm_nonneg ρ
        nlinarith)
    simpa using this
  set h : ℝ → ℂ := fun t => φ (ρ + 1) (t + σ) - φ (ρ + 1) t with hh
  have hderiv : ∀ x ∈ Set.Icc α (α + D), HasDerivAt h
      ((ρ + 1) * φ (ρ + 1 - 1) (x + σ) - (ρ + 1) * φ (ρ + 1 - 1) x) x := by
    intro x hx
    have h1 := hasDerivAt_φ (ρ + 1) (t := x + σ) (by linarith [hx.1])
    have h1' : HasDerivAt (fun t => φ (ρ + 1) (t + σ)) ((ρ + 1) * φ (ρ + 1 - 1) (x + σ)) x := by
      simpa using h1.comp_add_const x σ
    exact h1'.sub (hasDerivAt_φ (ρ + 1) (by linarith [hx.1]))
  have hmain := norm_sub_le_of_deriv (f := h) (C := ‖ρ + 1‖ * (2 * ‖ρ‖ * σ))
    (by linarith : α ≤ α + D) hderiv
    (fun x hx => by
      rw [add_sub_cancel_right, ← mul_sub, norm_mul]
      gcongr
      exact hψ x (by linarith [hx.1]))
  have hnum : φ (ρ + 1) (α + D + σ) - φ (ρ + 1) (α + D) - φ (ρ + 1) (α + σ) + φ (ρ + 1) α
      = h (α + D) - h α := by simp only [hh]; ring
  rw [tcoef_eq, ← hα, hnum, norm_div, norm_mul, div_le_iff₀ (by positivity)]
  calc ‖h (α + D) - h α‖ ≤ ‖ρ + 1‖ * (2 * ‖ρ‖ * σ) * (α + D - α) := hmain
    _ = 2 * σ * D * (‖ρ‖ * ‖ρ + 1‖) := by ring

lemma tcoef_le_second (hre : ρ.re = 1 / 2) (ha : 3 / 4 ≤ a) (ha1 : a ≤ 1) (hσ : 0 < σ)
    (hσD : σ ≤ D) (hD : D ≤ 1 / 2) : ‖tcoef a σ D ρ‖ ≤ 4 * σ / ‖ρ‖ := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  set α := a - 1 with hα
  have hd : ∀ u : ℝ, -(1 / 4) ≤ u → u + σ ≤ 1 →
      ‖φ (ρ + 1) (u + σ) - φ (ρ + 1) u‖ ≤ 2 * ‖ρ + 1‖ * σ := by
    intro u hu0 hu1
    have := norm_sub_le_of_deriv (f := φ (ρ + 1)) (C := 2 * ‖ρ + 1‖) (by linarith : u ≤ u + σ)
      (fun x hx => hasDerivAt_φ _ (by linarith [hx.1]))
      (fun x hx => by
        rw [norm_mul, norm_φ _ (by linarith [hx.1]), add_sub_cancel_right, hre, mul_comm]
        gcongr
        exact rpow_half_le (by linarith [hx.1]) (by linarith [hx.2]))
    simpa using this
  have h1 := hd (α + D) (by linarith) (by linarith)
  have h2 := hd α (by linarith) (by linarith)
  have hnum : φ (ρ + 1) (α + D + σ) - φ (ρ + 1) (α + D) - φ (ρ + 1) (α + σ) + φ (ρ + 1) α
      = (φ (ρ + 1) (α + D + σ) - φ (ρ + 1) (α + D)) - (φ (ρ + 1) (α + σ) - φ (ρ + 1) α) := by
    ring
  rw [tcoef_eq, ← hα, hnum, norm_div, norm_mul, div_le_div_iff₀ (by positivity) hρ0]
  calc _ ≤ (‖φ (ρ + 1) (α + D + σ) - φ (ρ + 1) (α + D)‖ + ‖φ (ρ + 1) (α + σ) - φ (ρ + 1) α‖)
        * ‖ρ‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (2 * ‖ρ + 1‖ * σ + 2 * ‖ρ + 1‖ * σ) * ‖ρ‖ := by gcongr
    _ = 4 * σ * (‖ρ‖ * ‖ρ + 1‖) := by ring

lemma tcoef_le_trivial (hre : ρ.re = 1 / 2) (ha : 3 / 4 ≤ a) (ha1 : a ≤ 1) (hσ : 0 < σ)
    (hσD : σ ≤ D) (hD : D ≤ 1 / 2) : ‖tcoef a σ D ρ‖ ≤ 64 / (1 + ρ.im ^ 2) := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  have hb : ∀ t : ℝ, -(1 / 4) ≤ t → t ≤ 1 → ‖φ (ρ + 1) t‖ ≤ 4 := by
    intro t h0 h1
    rw [norm_φ _ (by linarith)]
    simp only [add_re, one_re, hre]
    calc (1 + t) ^ (1 / 2 + 1 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 + 1 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  set α := a - 1 with hα
  have hnum : ‖φ (ρ + 1) (α + D + σ) - φ (ρ + 1) (α + D) - φ (ρ + 1) (α + σ) + φ (ρ + 1) α‖
      ≤ 16 := by
    calc _ ≤ ‖φ (ρ + 1) (α + D + σ)‖ + ‖φ (ρ + 1) (α + D)‖ + ‖φ (ρ + 1) (α + σ)‖
          + ‖φ (ρ + 1) α‖ :=
          (norm_add_le _ _).trans (by
            gcongr
            exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
      _ ≤ 4 + 4 + 4 + 4 := by
          gcongr
          · exact hb _ (by linarith) (by linarith)
          · exact hb _ (by linarith) (by linarith)
          · exact hb _ (by linarith) (by linarith)
          · exact hb _ (by linarith) (by linarith)
      _ = 16 := by norm_num
  have hden : ‖ρ‖ ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (norm_rho_le hre) (norm_nonneg _)
  have hsq := sq_norm_rho hre
  rw [tcoef_eq, ← hα, norm_div, norm_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ρ.im]

/-- `‖tcoef‖² ≤ (4σ²/D²) w D ⌊|γ|⌋`. -/
lemma tcoef_sq_le (hre : ρ.re = 1 / 2) (ha : 3 / 4 ≤ a) (ha1 : a ≤ 1) (hσ : 0 < σ)
    (hσD : σ ≤ D) (hD : D ≤ 1 / 2) :
    ‖tcoef a σ D ρ‖ ^ 2 ≤ 4 * σ ^ 2 / D ^ 2 * w D ⌊|ρ.im|⌋₊ := by
  have hD0 : 0 < D := hσ.trans_le hσD
  set n := ⌊|ρ.im|⌋₊
  have hn1 : (n : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hsq := sq_norm_rho hre
  have hK : 0 < 4 * σ ^ 2 / D ^ 2 := by positivity
  unfold w
  rw [mul_min_of_nonneg _ _ hK.le]
  refine le_min ?_ ?_
  · have := tcoef_le_first hre ha ha1 hσ hσD hD
    calc ‖tcoef a σ D ρ‖ ^ 2 ≤ (2 * σ * D) ^ 2 := by gcongr
      _ = 4 * σ ^ 2 / D ^ 2 * D ^ 4 := by field_simp; norm_num
  · have h := tcoef_le_second hre ha ha1 hσ hσD hD
    have hg : (n : ℝ) ^ 2 ≤ ρ.im ^ 2 := by rw [← sq_abs ρ.im]; gcongr
    calc ‖tcoef a σ D ρ‖ ^ 2 ≤ (4 * σ / ‖ρ‖) ^ 2 := by gcongr
      _ = 16 * σ ^ 2 / (1 / 4 + ρ.im ^ 2) := by rw [div_pow, hsq]; ring
      _ ≤ 16 * σ ^ 2 / ((n : ℝ) ^ 2 + 1 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ ≤ 64 * σ ^ 2 / ((n : ℝ) ^ 2 + 1 / 4) :=
          div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ = 4 * σ ^ 2 / D ^ 2 * (16 * D ^ 2 / ((n : ℝ) ^ 2 + 1 / 4)) := by field_simp; ring

/-- **The trapezoid coefficient sums, under RH.** -/
theorem tcoef_sums (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ a σ D : ℝ,
    3 / 4 ≤ a → a ≤ 1 → 0 < σ → σ ≤ D → D ≤ 1 / 2 →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖tcoef a σ D ρ‖) ∧
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖tcoef a σ D ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) ∧
    ∑' ρ : Zeros, (mult ρ : ℝ) * ‖tcoef a σ D ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ C * σ ^ 2 * D * Real.log (2 / D) ^ 2 := by
  obtain ⟨C, hC, hW⟩ := wave_sums
  refine ⟨4 * C, by positivity, fun a σ D ha ha1 hσ hσD hD => ?_⟩
  have hD0 : 0 < D := hσ.trans_le hσD
  have hre := zero_re_of_RH hRH
  obtain ⟨h1, h2, h3⟩ := hW D (4 * σ ^ 2 / D ^ 2) 64 hD0 hD (by positivity)
    (fun ρ => tcoef a σ D ρ) (fun ρ => tcoef_le_trivial (hre ρ) ha ha1 hσ hσD hD)
    (fun ρ => tcoef_sq_le (hre ρ) ha ha1 hσ hσD hD)
  refine ⟨h1, h2, h3.trans (le_of_eq ?_)⟩
  field_simp

end Erdos233
