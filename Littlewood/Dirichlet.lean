import Littlewood.Kernel
import Erdos985.Analytic.ExplicitFormula.Identity.Zeros

/-!
# Step 3: the Dirichlet-series side of the explicit formula

For `Re s > -1` and `x ≥ 1`,

    (1/2π) ∫ L(Λ, s + w) x^w / w² dv = Σ_{n ≤ x} Λ(n) n^{-s} log (x/n)      (Re w = 2),

by integrating the absolutely convergent series `L(Λ, s + w) = Σ Λ(n) n^{-s} n^{-w}` term by
term against `perron_log`.
-/

open Complex MeasureTheory ArithmeticFunction

namespace Littlewood

open Erdos985.Analytic

/-- One Dirichlet term against the kernel. -/
lemma term_mul_kerLog (s : ℂ) (x : ℝ) (hx : 0 < x) (v : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun n => (Λ n : ℂ)) (s + lineP v) n * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
      = (Λ n : ℂ) * (n : ℂ) ^ (-s) * ((((x / n : ℝ)) : ℂ) ^ lineP v * (1 / lineP v ^ 2)) := by
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsplit : (n : ℂ) ^ (s + lineP v) = (n : ℂ) ^ s * (n : ℂ) ^ lineP v := cpow_add _ _ hnc
  have hdiv : (((x / n : ℝ)) : ℂ) ^ lineP v = (x : ℂ) ^ lineP v / (n : ℂ) ^ lineP v := by
    rw [ofReal_div, div_eq_mul_inv ((x : ℝ) : ℂ), ← ofReal_inv,
      mul_cpow_ofReal_nonneg hx.le (inv_nonneg.2 hn0.le), ofReal_inv,
      inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast, div_eq_mul_inv]
  have h1 : (n : ℂ) ^ s ≠ 0 := by rw [cpow_ne_zero_iff]; left; exact hnc
  have h2 : (n : ℂ) ^ lineP v ≠ 0 := by rw [cpow_ne_zero_iff]; left; exact hnc
  rw [hsplit, hdiv, cpow_neg]
  field_simp

/-- **Weighted Perron formula for `Λ`** with the weight `log (x/n)`. -/
theorem perron_vonMangoldt {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun v : ℝ => LSeries (fun n => (Λ n : ℂ)) (s + lineP v) *
      ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))) ∧
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, LSeries (fun n => (Λ n : ℂ)) (s + lineP v) *
        ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
      = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * (n : ℂ) ^ (-s) * (Real.log (x / n) : ℂ) := by
  have hx0 : 0 < x := by linarith
  set C := ∫ v : ℝ, ‖1 / lineP v ^ 2‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < x / n := fun n hn =>
    div_pos hx0 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  set G : ℕ → ℝ → ℂ := fun n v => if n = 0 then 0 else
    (Λ n : ℂ) * (n : ℂ) ^ (-s) * ((((x / n : ℝ)) : ℂ) ^ lineP v * (1 / lineP v ^ 2)) with hG
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]; exact (integrable_kerLog (hpos n hn)).const_mul _
  have hnormK : ∀ y : ℝ, 0 < y → ∫ v : ℝ, ‖(y : ℂ) ^ lineP v * (1 / lineP v ^ 2)‖ = y ^ (2 : ℝ) * C := by
    intro y hy
    simp_rw [norm_mul (((y : ℂ)) ^ lineP _), norm_cpow_eq_rpow_re_of_pos hy, lineP_re]
    rw [integral_const_mul]
  have hG_norm : ∀ n, ∫ v, ‖G n v‖ = if n = 0 then 0 else
      ‖(Λ n : ℂ) * (n : ℂ) ^ (-s)‖ * ((x / n) ^ (2 : ℝ) * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul, ← hnormK _ (hpos n hn)]
      simp only [norm_mul]
  have hsumΛ := (LSeriesSummable_vonMangoldt (s := ((s.re + 2 : ℝ) : ℂ))
    (by simp; linarith)).norm
  have hsum : Summable fun n => ∫ v, ‖G n v‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (hsumΛ.mul_left (x ^ (2 : ℝ) * C))
    rw [hG_norm]
    split_ifs with hn
    · positivity
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
      rw [LSeries.norm_term_eq, ite_eq_right_iff.2 (fun h => absurd h hn), norm_mul,
        norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [neg_re, ofReal_re]
      rw [Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le, Real.rpow_add hn0]
      apply le_of_eq
      field_simp
  set f : ℝ → ℂ := fun v => LSeries (fun n => (Λ n : ℂ)) (s + lineP v) *
      ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)) with hf
  have hHas : ∀ v, HasSum (fun n => G n v) (f v) := by
    intro v
    have hre : 1 < (s + lineP v).re := by simp; linarith
    have h := ((LSeriesSummable_vonMangoldt hre).hasSum).mul_right
      ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
    rw [show f v = (∑' b, LSeries.term (fun n => (Λ n : ℂ)) (s + lineP v) b) *
      ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)) from rfl]
    convert h using 1
    funext n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      exact (term_mul_kerLog s x hx0 v hn).symm
  have hcont : Continuous fun v : ℝ => LSeries (fun n => (Λ n : ℂ)) (s + lineP v) := by
    have hab : ∀ v : ℝ, LSeries.abscissaOfAbsConv (fun n => (Λ n : ℂ)) < ((s + lineP v).re : EReal) := by
      intro v
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldt (s := ((s.re + 3 / 2 : ℝ) : ℂ)) (by simp; linarith))) ?_
      simp only [ofReal_re, add_re, lineP_re]
      exact_mod_cast (show s.re + 3 / 2 < s.re + 2 by linarith)
    exact (LSeries_differentiableOn _).continuousOn.comp_continuous
      (continuous_const.add continuous_lineP) hab
  have hfc : Continuous f :=
    hcont.mul ((continuous_lineP.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))).mul
      (Continuous.div (f := fun _ => (1 : ℂ)) continuous_const (continuous_lineP.pow 2)
        fun v => pow_ne_zero 2 (lineP_ne_zero v)))
  have hint : Integrable f :=
    IdentityAux.integrable_of_hasSum hfc.aestronglyMeasurable hG_int hsum hHas
  refine ⟨hint, ?_⟩
  have hGint : ∀ n, ∫ v, G n v = if n = 0 then 0 else
      (Λ n : ℂ) * (n : ℂ) ^ (-s) * (2 * Real.pi *
        (if 1 ≤ x / n then (Real.log (x / n) : ℂ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      have hp := perron_log (hpos n hn)
      have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
        mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
      rw [← hp, ← mul_assoc (2 * (Real.pi : ℂ)), mul_one_div_cancel hpi, one_mul]
  change (1 / (2 * Real.pi) : ℂ) * ∫ v, f v = _
  rw [show f = fun v => ∑' n, G n v from funext fun v => (hHas v).tsum_eq.symm,
    ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hn0 : n = 0
    · simp [hn0]
    rw [Finset.mem_range] at hn
    have hn1 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
    have hle : 1 ≤ x / n := by
      rw [one_le_div hn1]
      exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 hn)).trans (Nat.floor_le hx0.le)
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    field_simp
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hn0 : n ≠ 0 := by omega
    have hlt : ¬ 1 ≤ x / n := by
      have hn1 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
      rw [not_le, div_lt_one hn1]
      have := Nat.lt_floor_add_one x
      have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    simp [hn0, hlt]

end Littlewood
