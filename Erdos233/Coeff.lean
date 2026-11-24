import Erdos233.RH
import Erdos233.Density
import Erdos233.Coeff.Bounds
import Erdos233.Coeff.Series

/-!
# Step 4. Size of the coefficients `coef δ ρ` under RH

For `Re ρ = 1/2` and `0 < δ ≤ 1/2`, with `g(t) = (1+t)^{ρ+1}`:
`|coef δ ρ| ≤ δ²` (second difference, `|g''| ≤ |ρ(ρ+1)|`),
`|coef δ ρ| ≤ 4δ/|ρ|` (first differences, `|g'| ≤ 2 |ρ+1|`),
`|coef δ ρ| ≤ 52/(1+γ²)` (trivially). These are in `Erdos233/Coeff/Bounds.lean`.
Summing with `zero_density` over the unit windows `⌊|γ|⌋ = n` (each zero is charged to the
two kernels centred at `±n`):
`Σ m |coef|² log(|γ|+2) ≤ 4C Σ_n min(δ⁴, 16δ²/(n²+1/4)) log²(n+4) ≪ δ³ log²(2/δ)`,
the last series being bounded in `Erdos233/Coeff/Series.lean`.
-/

namespace Erdos233

open Complex Erdos985.Analytic Erdos233.CoeffAux

theorem coef_sums (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖coef δ ρ‖) ∧
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) ∧
    ∑' ρ : Zeros, (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ C * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := zero_density
  refine ⟨1200 * C, by positivity, fun δ hδ0 hδ => ?_⟩
  have hre := zero_re_of_RH hRH
  -- summability of `m ‖coef‖`
  have hS1 : Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖coef δ ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) ((hC 0).1.mul_left 52)
    have := coef_le_trivial (hre ρ) hδ0 hδ
    have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
    calc (mult ρ : ℝ) * ‖coef δ ρ‖ ≤ (mult ρ : ℝ) * (52 / (1 + (ρ : ℂ).im ^ 2)) := by gcongr
      _ = 52 * ((mult ρ : ℝ) / (1 + (0 - (ρ : ℂ).im) ^ 2)) := by ring
  -- the double family over windows `n` and zeros `ρ`
  set P : ℕ → Zeros → ℝ := fun n ρ => (mult ρ : ℝ) / (1 + ((n : ℝ) - (ρ : ℂ).im) ^ 2) +
    (mult ρ : ℝ) / (1 + (-(n : ℝ) - (ρ : ℂ).im) ^ 2) with hP
  set f : ℕ → Zeros → ℝ := fun n ρ => 2 * w δ n * Real.log (n + 4) * P n ρ with hf
  have hlog0 : ∀ n : ℕ, 0 ≤ Real.log ((n : ℝ) + 4) :=
    fun n => Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hP0 : ∀ n ρ, 0 ≤ P n ρ := fun n ρ => by simp only [hP]; positivity
  have hf0 : ∀ n ρ, 0 ≤ f n ρ := fun n ρ => by
    simp only [hf]
    have := w_nonneg δ n; have := hlog0 n; have := hP0 n ρ
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
  have hft : ∀ n : ℕ, ∑' ρ, f n ρ ≤ 4 * C * (w δ n * Real.log (n + 4) ^ 2) := by
    intro n
    simp only [hf]
    rw [tsum_mul_left]
    have := w_nonneg δ n
    have := hlog0 n
    calc 2 * w δ n * Real.log (n + 4) * ∑' ρ, P n ρ
        ≤ 2 * w δ n * Real.log (n + 4) * (2 * C * Real.log (n + 4)) := by
          gcongr; exact hPt n
      _ = _ := by ring
  obtain ⟨hbS, hbT⟩ := series_bound δ hδ0 hδ
  have hfsum : Summable (Function.uncurry f) := by
    refine (summable_prod_of_nonneg (f := Function.uncurry f) (fun p => hf0 p.1 p.2)).mpr
      ⟨fun n => hfs n, ?_⟩
    exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (hf0 n)) hft (hbS.mul_left _)
  have hslice : ∀ ρ, Summable (fun n => f n ρ) := fun ρ =>
    hfsum.comp_injective (i := fun n => (n, ρ)) (fun a b h => by simpa using h)
  have hsumρ : Summable (fun ρ => ∑' n, f n ρ) := hfsum.prod_symm.prod
  -- the pointwise bound
  have hpt : ∀ ρ : Zeros, (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ f ⌊|(ρ : ℂ).im|⌋₊ ρ := by
    intro ρ
    set γ := (ρ : ℂ).im with hγ
    set n := ⌊|γ|⌋₊ with hn
    have hn1 : (n : ℝ) ≤ |γ| := Nat.floor_le (abs_nonneg _)
    have hn2 : |γ| < n + 1 := Nat.lt_floor_add_one _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
    have hw : ‖coef δ ρ‖ ^ 2 ≤ w δ n := by
      unfold w
      refine le_min ?_ ?_
      · have := coef_le_second (hre ρ) hδ0 hδ
        calc ‖coef δ ρ‖ ^ 2 ≤ (δ ^ 2) ^ 2 := by gcongr
          _ = δ ^ 4 := by ring
      · have h := coef_le_first (hre ρ) hδ0 hδ
        have hsq := sq_norm_rho (hre ρ)
        have hρ0 := norm_pos_iff.mpr (rho_ne_zero (hre ρ))
        calc ‖coef δ ρ‖ ^ 2 ≤ (4 * δ / ‖(ρ : ℂ)‖) ^ 2 := by gcongr
          _ = 16 * δ ^ 2 / (1 / 4 + γ ^ 2) := by rw [div_pow, hsq]; ring
          _ ≤ 16 * δ ^ 2 / ((n : ℝ) ^ 2 + 1 / 4) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have : (n : ℝ) ^ 2 ≤ γ ^ 2 := by rw [← sq_abs γ]; gcongr
            linarith
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
    have hw0 := w_nonneg δ n
    have hl0 := hlog0 n
    calc (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|γ| + 2)
        ≤ (mult ρ : ℝ) * w δ n * Real.log (n + 4) := by gcongr
      _ ≤ (2 * P n ρ) * w δ n * Real.log (n + 4) := by gcongr
      _ = f n ρ := by simp only [hf]; ring
  have hpt' : ∀ ρ : Zeros, (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ ∑' n, f n ρ := fun ρ =>
    (hpt ρ).trans ((hslice ρ).le_tsum _ (fun j _ => hf0 j ρ))
  have hS2 : Summable (fun ρ : Zeros =>
      (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (by positivity)
      (Real.log_nonneg (by linarith [abs_nonneg (ρ : ℂ).im]))) hpt' hsumρ
  refine ⟨hS1, hS2, ?_⟩
  calc ∑' ρ : Zeros, (mult ρ : ℝ) * ‖coef δ ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ ∑' ρ, ∑' n, f n ρ := Summable.tsum_le_tsum hpt' hS2 hsumρ
    _ = ∑' n, ∑' ρ, f n ρ := hfsum.tsum_comm' hfs hslice
    _ ≤ ∑' n : ℕ, 4 * C * (w δ n * Real.log (n + 4) ^ 2) :=
        Summable.tsum_le_tsum hft hfsum.prod (hbS.mul_left _)
    _ = 4 * C * ∑' n : ℕ, w δ n * Real.log (n + 4) ^ 2 := tsum_mul_left
    _ ≤ 4 * C * (300 * δ ^ 3 * Real.log (2 / δ) ^ 2) := by gcongr
    _ = 1200 * C * δ ^ 3 * Real.log (2 / δ) ^ 2 := by ring

end Erdos233
