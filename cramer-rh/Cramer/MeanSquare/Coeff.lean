import Erdos233.Coeff
import Erdos233.MeanValue

/-!
# Mean square, step 1: the first-difference coefficients

`acoef δ ρ = ((1+δ)^{ρ+1} − 1) / (ρ(ρ+1)) / δ`, so that the zero `ρ` contributes
`−δ y^{ρ+1} acoef δ ρ` to `psi1(y(1+δ)) − psi1(y)`. For `Re ρ = 1/2`, `0 < δ ≤ 1/2`:

* `‖acoef δ ρ‖ ≤ 2/‖ρ‖` (mean value theorem, `|d/dt (1+t)^{ρ+1}| ≤ 2|ρ+1|`), uniformly in `δ`;
* `‖acoef δ ρ‖ ≤ 20/(δ(1+γ²))` (trivially), for absolute convergence.

Summing with erdos-233's `zero_density` over unit windows gives
`Σ m_ρ ‖acoef δ ρ‖² log(|γ|+2) ≤ C`, with `C` independent of `δ`: this is where the
convergence of `Σ_ρ log|γ| / |ρ|²` (the unit-window zero count) enters.
-/

namespace Cramer.MeanSq

open Complex Erdos985.Analytic Erdos233 Erdos233.CoeffAux

/-- The coefficient of `−δ y^{ρ+1}` in `psi1(y(1+δ)) − psi1(y)`. -/
noncomputable def acoef (δ : ℝ) (ρ : ℂ) : ℂ :=
  ((((1 + δ : ℝ) : ℂ) ^ (ρ + 1) - 1) / (ρ * (ρ + 1))) / (δ : ℂ)

variable {δ : ℝ} {ρ : ℂ}

lemma acoef_le_inv (hre : ρ.re = 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ‖acoef δ ρ‖ ≤ 2 / ‖ρ‖ := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  have hd : ‖φ (ρ + 1) δ - φ (ρ + 1) 0‖ ≤ 2 * ‖ρ + 1‖ * δ := by
    have := norm_sub_le_of_deriv (f := φ (ρ + 1)) (C := 2 * ‖ρ + 1‖) hδ0.le
      (fun x hx => hasDerivAt_φ _ (by linarith [hx.1]))
      (fun x hx => deriv_bound1 hre hx.1 (by linarith [hx.2]))
    simpa using this
  have hnum : (((1 + δ : ℝ) : ℂ) ^ (ρ + 1) - 1) = φ (ρ + 1) δ - φ (ρ + 1) 0 := by
    simp [φ]
  unfold acoef
  rw [hnum, norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ0.le,
    div_div, div_le_div_iff₀ (by positivity) hρ0]
  calc ‖φ (ρ + 1) δ - φ (ρ + 1) 0‖ * ‖ρ‖ ≤ 2 * ‖ρ + 1‖ * δ * ‖ρ‖ := by gcongr
    _ = 2 * (‖ρ‖ * ‖ρ + 1‖ * δ) := by ring

lemma acoef_le_trivial (hre : ρ.re = 1 / 2) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ‖acoef δ ρ‖ ≤ 20 / δ / (1 + ρ.im ^ 2) := by
  have hρ0 := norm_pos_iff.mpr (rho_ne_zero hre)
  have hs0 := norm_pos_iff.mpr (rho_add_one_ne_zero hre)
  have hb : ‖φ (ρ + 1) δ‖ ≤ 4 := by
    rw [norm_φ _ (by linarith)]
    simp only [add_re, one_re, hre]
    calc (1 + δ) ^ (1 / 2 + 1 : ℝ) ≤ (1 + δ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ ≤ 4 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; nlinarith
  have hnum : ‖(((1 + δ : ℝ) : ℂ) ^ (ρ + 1) - 1)‖ ≤ 5 := by
    have e : (((1 + δ : ℝ) : ℂ) ^ (ρ + 1)) = φ (ρ + 1) δ := by simp [φ]
    rw [e]
    calc ‖φ (ρ + 1) δ - 1‖ ≤ ‖φ (ρ + 1) δ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 4 + 1 := by rw [norm_one]; linarith
      _ = 5 := by norm_num
  have hden : ‖ρ‖ ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (norm_rho_le hre) (norm_nonneg _)
  have hsq := sq_norm_rho hre
  unfold acoef
  rw [norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ0.le]
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (1 + ρ.im ^ 2) ≤ 4 * (‖ρ‖ * ‖ρ + 1‖) := by nlinarith [sq_nonneg ρ.im]
  calc ‖(((1 + δ : ℝ) : ℂ) ^ (ρ + 1) - 1)‖ * (δ * (1 + ρ.im ^ 2))
      ≤ 5 * (δ * (4 * (‖ρ‖ * ‖ρ + 1‖))) := by
        gcongr
    _ = 20 * (‖ρ‖ * ‖ρ + 1‖ * δ) := by ring

/-- A family whose squared norms are bounded by `K/(n²+1/4)` on the window `⌊|γ|⌋ = n` has a
log-weighted square sum `≤ C·K`. -/
theorem sq_log_sums : ∃ C : ℝ, 0 < C ∧ ∀ (c : Zeros → ℂ) (K : ℝ), 0 ≤ K →
    (∀ ρ : Zeros, ‖c ρ‖ ^ 2 ≤ K / (1 / 4 + (ρ : ℂ).im ^ 2)) →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) ∧
    ∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2) ≤ C * K := by
  obtain ⟨C, hC0, hC⟩ := zero_density
  obtain ⟨hbS, -⟩ := series_bound (1 / 2) (by norm_num) le_rfl
  set Sw : ℝ := ∑' n : ℕ, w (1 / 2) n * Real.log (n + 4) ^ 2 with hSw
  have hSw0 : 0 ≤ Sw := tsum_nonneg fun n => mul_nonneg (w_nonneg _ _) (sq_nonneg _)
  refine ⟨4 * C * 256 * (Sw + 1), by positivity, fun c K hK hcK => ?_⟩
  set P : ℕ → Zeros → ℝ := fun n ρ => (mult ρ : ℝ) / (1 + ((n : ℝ) - (ρ : ℂ).im) ^ 2) +
    (mult ρ : ℝ) / (1 + (-(n : ℝ) - (ρ : ℂ).im) ^ 2) with hP
  set f : ℕ → Zeros → ℝ := fun n ρ =>
    2 * (256 * K * w (1 / 2) n) * Real.log (n + 4) * P n ρ with hf
  have hlog0 : ∀ n : ℕ, 0 ≤ Real.log ((n : ℝ) + 4) :=
    fun n => Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hP0 : ∀ n ρ, 0 ≤ P n ρ := fun n ρ => by simp only [hP]; positivity
  have hf0 : ∀ n ρ, 0 ≤ f n ρ := fun n ρ => by
    simp only [hf]
    have := w_nonneg (1 / 2) n; have := hlog0 n; have := hP0 n ρ
    positivity
  have hPs : ∀ n : ℕ, Summable (P n) := fun n => (hC n).1.add (hC (-(n : ℝ))).1
  have hPt : ∀ n : ℕ, ∑' ρ, P n ρ ≤ 2 * C * Real.log (n + 4) := by
    intro n
    simp only [hP]
    rw [Summable.tsum_add (hC n).1 (hC (-(n : ℝ))).1]
    have h1 := (hC n).2
    have h2 := (hC (-(n : ℝ))).2
    rw [abs_neg, Nat.abs_cast] at h2
    rw [Nat.abs_cast] at h1
    have : Real.log ((n : ℝ) + 2) ≤ Real.log (n + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    nlinarith
  have hfs : ∀ n, Summable (f n) := fun n => (hPs n).mul_left _
  have hft : ∀ n : ℕ, ∑' ρ, f n ρ ≤
      4 * C * 256 * K * (w (1 / 2) n * Real.log (n + 4) ^ 2) := by
    intro n
    simp only [hf]
    rw [tsum_mul_left]
    have := w_nonneg (1 / 2) n
    have := hlog0 n
    calc 2 * (256 * K * w (1 / 2) n) * Real.log (n + 4) * ∑' ρ, P n ρ
        ≤ 2 * (256 * K * w (1 / 2) n) * Real.log (n + 4) * (2 * C * Real.log (n + 4)) := by
          gcongr; exact hPt n
      _ = _ := by ring
  have hfsum : Summable (Function.uncurry f) := by
    refine (summable_prod_of_nonneg (f := Function.uncurry f) (fun p => hf0 p.1 p.2)).mpr
      ⟨fun n => hfs n, ?_⟩
    exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (hf0 n)) hft (hbS.mul_left _)
  have hslice : ∀ ρ, Summable (fun n => f n ρ) := fun ρ =>
    hfsum.comp_injective (i := fun n => (n, ρ)) (fun a b h => by simpa using h)
  have hsumρ : Summable (fun ρ => ∑' n, f n ρ) := hfsum.prod_symm.prod
  have hpt : ∀ ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ f ⌊|(ρ : ℂ).im|⌋₊ ρ := by
    intro ρ
    set γ := (ρ : ℂ).im with hγ
    set n := ⌊|γ|⌋₊ with hn
    have hn1 : (n : ℝ) ≤ |γ| := Nat.floor_le (abs_nonneg _)
    have hn2 : |γ| < n + 1 := Nat.lt_floor_add_one _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
    have hw : ‖c ρ‖ ^ 2 ≤ 256 * K * w (1 / 2) n := by
      have h1 : ‖c ρ‖ ^ 2 ≤ K / ((n : ℝ) ^ 2 + 1 / 4) := by
        refine (hcK ρ).trans (div_le_div_of_nonneg_left hK (by positivity) ?_)
        have : (n : ℝ) ^ 2 ≤ γ ^ 2 := by rw [← sq_abs γ]; gcongr
        linarith
      have h2 : 1 / ((n : ℝ) ^ 2 + 1 / 4) ≤ 256 * w (1 / 2) n := by
        unfold w
        have hD : 0 < (n : ℝ) ^ 2 + 1 / 4 := by positivity
        rcases le_total ((1 / 2 : ℝ) ^ 4) (16 * (1 / 2) ^ 2 / ((n : ℝ) ^ 2 + 1 / 4)) with h | h
        · rw [min_eq_left h]
          rw [div_le_iff₀ hD]
          nlinarith
        · rw [min_eq_right h]
          have e : 256 * (16 * (1 / 2 : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1 / 4))
              = 1024 / ((n : ℝ) ^ 2 + 1 / 4) := by ring
          rw [e]
          exact div_le_div_of_nonneg_right (by norm_num) hD.le
      calc ‖c ρ‖ ^ 2 ≤ K / ((n : ℝ) ^ 2 + 1 / 4) := h1
        _ = K * (1 / ((n : ℝ) ^ 2 + 1 / 4)) := by ring
        _ ≤ K * (256 * w (1 / 2) n) := mul_le_mul_of_nonneg_left h2 hK
        _ = 256 * K * w (1 / 2) n := by ring
    have hlog : Real.log (|γ| + 2) ≤ Real.log (n + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogγ : 0 ≤ Real.log (|γ| + 2) := Real.log_nonneg (by linarith [abs_nonneg γ])
    have hP2 : (mult ρ : ℝ) ≤ 2 * P n ρ := by
      simp only [hP]
      have key : ∀ x : ℝ, x ^ 2 < 1 → (mult ρ : ℝ) ≤ 2 * ((mult ρ : ℝ) / (1 + x ^ 2)) := by
        intro x hx
        have : (mult ρ : ℝ) / 2 ≤ (mult ρ : ℝ) / (1 + x ^ 2) :=
          div_le_div_of_nonneg_left hm (by positivity) (by linarith)
        linarith
      have ha : 0 ≤ (mult ρ : ℝ) / (1 + ((n : ℝ) - γ) ^ 2) := by positivity
      have hb : 0 ≤ (mult ρ : ℝ) / (1 + (-(n : ℝ) - γ) ^ 2) := by positivity
      rcases le_or_gt 0 γ with hg | hg
      · rw [abs_of_nonneg hg] at hn1 hn2
        have := key ((n : ℝ) - γ) (by nlinarith)
        linarith
      · rw [abs_of_neg hg] at hn1 hn2
        have := key (-(n : ℝ) - γ) (by nlinarith)
        linarith
    have hw0 : 0 ≤ 256 * K * w (1 / 2) n := by have := w_nonneg (1 / 2) n; positivity
    have hl0 := hlog0 n
    calc (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|γ| + 2)
        ≤ (mult ρ : ℝ) * (256 * K * w (1 / 2) n) * Real.log (n + 4) := by gcongr
      _ ≤ (2 * P n ρ) * (256 * K * w (1 / 2) n) * Real.log (n + 4) := by gcongr
      _ = f n ρ := by simp only [hf]; ring
  have hpt' : ∀ ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ ∑' n, f n ρ := fun ρ =>
    (hpt ρ).trans ((hslice ρ).le_tsum _ (fun j _ => hf0 j ρ))
  have hS2 : Summable (fun ρ : Zeros =>
      (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (by positivity)
      (Real.log_nonneg (by linarith [abs_nonneg (ρ : ℂ).im]))) hpt' hsumρ
  refine ⟨hS2, ?_⟩
  calc ∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ ∑' ρ, ∑' n, f n ρ := Summable.tsum_le_tsum hpt' hS2 hsumρ
    _ = ∑' n, ∑' ρ, f n ρ := hfsum.tsum_comm' hfs hslice
    _ ≤ ∑' n : ℕ, 4 * C * 256 * K * (w (1 / 2) n * Real.log (n + 4) ^ 2) :=
        Summable.tsum_le_tsum hft hfsum.prod (hbS.mul_left _)
    _ = 4 * C * 256 * K * Sw := tsum_mul_left
    _ ≤ 4 * C * 256 * (Sw + 1) * K := by nlinarith [mul_nonneg hC0.le hK]

/-- Under RH: absolute summability of `m_ρ acoef δ ρ`, and the log-weighted square sum bounded
uniformly in `δ`. -/
theorem acoef_sums (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖acoef δ ρ‖) ∧
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖acoef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) ∧
    ∑' ρ : Zeros, (mult ρ : ℝ) * ‖acoef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2) ≤ C := by
  obtain ⟨Cd, -, hd⟩ := zero_density
  obtain ⟨C, hC0, hC⟩ := sq_log_sums
  refine ⟨C * 4, by positivity, fun δ hδ0 hδ => ?_⟩
  have hre := zero_re_of_RH hRH
  have hS1 : Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖acoef δ ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
      ((hd 0).1.mul_left (20 / δ))
    have := acoef_le_trivial (hre ρ) hδ0 hδ
    have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
    calc (mult ρ : ℝ) * ‖acoef δ ρ‖ ≤ (mult ρ : ℝ) * (20 / δ / (1 + (ρ : ℂ).im ^ 2)) := by
          gcongr
      _ = 20 / δ * ((mult ρ : ℝ) / (1 + (0 - (ρ : ℂ).im) ^ 2)) := by ring
  have hpt : ∀ ρ : Zeros, ‖acoef δ ρ‖ ^ 2 ≤ 4 / (1 / 4 + (ρ : ℂ).im ^ 2) := by
    intro ρ
    have h := acoef_le_inv (hre ρ) hδ0 hδ
    have hsq := sq_norm_rho (hre ρ)
    calc ‖acoef δ ρ‖ ^ 2 ≤ (2 / ‖(ρ : ℂ)‖) ^ 2 := by gcongr
      _ = 4 / (1 / 4 + (ρ : ℂ).im ^ 2) := by rw [div_pow, hsq]; norm_num
  obtain ⟨h2, h3⟩ := hC (fun ρ => acoef δ ρ) 4 (by norm_num) hpt
  exact ⟨hS1, h2, h3⟩

end Cramer.MeanSq
