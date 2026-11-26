import Density.ZeroCount.Global
import Erdos985.Analytic.Hadamard
import Erdos985.Analytic.ExplicitFormula.Bounds.DigammaSeries
import Erdos985.Analytic.ExplicitFormula.StepA.GammaFactor

/-!
# Local zero count `N(T + 1) - N(T) ≪ log T`

The classical argument (Davenport, *Multiplicative Number Theory*, ch. 15; Titchmarsh §9.2):

1. every zero `ρ = β + iγ` of `ξ` has `0 < β < 1` (`xiZeta_zero_re_mem`);
2. the Hadamard product of `ξ` (erdos-985's `hadamard_logDeriv`) at `s = 2 + iT` and at `2` gives
   `Σ_ρ m_ρ / (4 + (T - γ)²) ≤ Re ξ'/ξ(2 + iT) + K` (`tsum_window_le`);
3. each zero with `|γ - T| ≤ 1` contributes at least `1/5` (`zeroCountOn_window_le_tsum`);
4. `ξ'/ξ(s) = 1/s + 1/(s-1) - ½ log π + ½ ψ(s/2) + ζ'/ζ(s)`, and at `Re s = 2`,
   `Re ψ(1 + iy) ≤ ψ(1) + 2 + log(|y| + 1)` and `|ζ'/ζ| ≤ Σ Λ(n)/n²`
   (`re_logDeriv_xiZeta_le`).
-/

open Complex Filter Topology Set

namespace Density

open Erdos985.Analytic

/-! ### Step 1: the zeros of `ξ` lie in the open critical strip -/

lemma xiZeta_one_sub (s : ℂ) : xiZeta (1 - s) = xiZeta s := by
  simp only [xiZeta, completedRiemannZeta₀_one_sub]; ring

lemma completedRiemannZeta_eq_mul {s : ℂ} (h0 : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero h0]; field_simp

lemma xiZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1; rw [xiZeta_one]; exact one_ne_zero
  have h0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hΓ := Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < s.re)
  rw [xiZeta_eq h0 h1, completedRiemannZeta_eq_mul h0 hΓ]
  exact mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (mul_ne_zero hΓ (riemannZeta_ne_zero_of_one_le_re hs))

/-- Every zero of `ξ` lies in the open critical strip. -/
theorem xiZeta_zero_re_mem {ρ : ℂ} (h : xiZeta ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hc
    replace hc := not_lt.mp hc
    exact xiZeta_ne_zero_of_one_le_re (s := 1 - ρ) (by simp; linarith) (by rw [xiZeta_one_sub]; exact h)
  · by_contra hc
    exact xiZeta_ne_zero_of_one_le_re (not_lt.mp hc) h

/-! ### Step 2: the zero sum at `2 + iT` -/

lemma inv_re_eq (w : ℂ) : (1 / w).re = w.re / (w.re ^ 2 + w.im ^ 2) := by
  rw [one_div, inv_re, normSq_apply]; ring_nf

lemma pointwise_window {β γ T : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 / (4 + (T - γ) ^ 2) ≤ (2 - β) / ((2 - β) ^ 2 + (T - γ) ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [sq_nonneg (T - γ)]

lemma pointwise_two {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (2 - β) / ((2 - β) ^ 2 + γ ^ 2) ≤ 2 / (β ^ 2 + γ ^ 2) := by
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [sq_nonneg γ, mul_pos hβ0 hβ0]

/-- The weight of a zero `ρ` seen from height `T`. -/
noncomputable def windowWeight (T : ℝ) (ρ : {ρ : ℂ // xiZeta ρ = 0}) : ℝ :=
  (analyticOrderNatAt xiZeta ρ : ℝ) / (4 + (T - (ρ : ℂ).im) ^ 2)

lemma windowWeight_nonneg (T : ℝ) (ρ : {ρ : ℂ // xiZeta ρ = 0}) : 0 ≤ windowWeight T ρ := by
  unfold windowWeight; positivity

lemma window_pointwise (T : ℝ) {ρ : ℂ} (hρ : xiZeta ρ = 0) (m : ℝ) (hm : 0 ≤ m) :
    m / (4 + (T - ρ.im) ^ 2) ≤
      ((m : ℂ) * (1 / (2 + T * I - ρ) + 1 / ρ) - (m : ℂ) * (1 / (2 - ρ) + 1 / ρ)).re
        + 2 * (m / ‖ρ‖ ^ (1 + 1 : ℝ)) := by
  obtain ⟨hβ0, hβ1⟩ := xiZeta_zero_re_mem hρ
  rw [← mul_sub, add_sub_add_right_eq_sub, re_ofReal_mul, sub_re, inv_re_eq, inv_re_eq]
  have hnorm : ‖ρ‖ ^ (1 + 1 : ℝ) = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [show (1 + 1 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, ← Complex.normSq_eq_norm_sq, normSq_apply]; ring
  have e1 : (2 + T * I - ρ).re = 2 - ρ.re := by simp
  have e2 : (2 + T * I - ρ).im = T - ρ.im := by simp
  have e3 : (2 - ρ).re = 2 - ρ.re := by simp
  have e4 : (2 - ρ).im ^ 2 = ρ.im ^ 2 := by simp
  rw [hnorm, e1, e2, e3, e4]
  have hw := pointwise_window (T := T) (γ := ρ.im) hβ0 hβ1
  have ht := pointwise_two (γ := ρ.im) hβ0 hβ1
  have hw' := mul_le_mul_of_nonneg_left hw hm
  have ht' := mul_le_mul_of_nonneg_left ht hm
  rw [mul_one_div, mul_div_assoc'] at hw'
  rw [mul_sub, mul_div_assoc', mul_div_assoc', mul_div_assoc']
  have : m * 2 / (ρ.re ^ 2 + ρ.im ^ 2) = 2 * m / (ρ.re ^ 2 + ρ.im ^ 2) := by ring
  rw [mul_div_assoc', mul_div_assoc'] at ht'
  linarith

/-- **Step 2.** `Σ_ρ m_ρ / (4 + (T - γ)²) ≤ Re ξ'/ξ(2 + iT) + K`. -/
theorem tsum_window_le : ∃ K : ℝ, ∀ T : ℝ, Summable (windowWeight T) ∧
    ∑' ρ, windowWeight T ρ ≤ (deriv xiZeta (2 + T * I) / xiZeta (2 + T * I)).re + K := by
  obtain ⟨hsum, b, hb⟩ := hadamard_logDeriv differentiable_xiZeta
    (by rw [xiZeta_zero]; exact one_ne_zero) xiZeta_growth
  have h2 : xiZeta 2 ≠ 0 := xiZeta_ne_zero_of_one_le_re (by norm_num)
  obtain ⟨S2, e2⟩ := hb 2 h2
  have hsq := hsum 1 one_pos
  refine ⟨-(deriv xiZeta 2 / xiZeta 2).re + 2 * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
    (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 : ℝ), fun T => ?_⟩
  have hz : xiZeta (2 + T * I) ≠ 0 := xiZeta_ne_zero_of_one_le_re (by simp)
  obtain ⟨Sz, ez⟩ := hb (2 + T * I) hz
  have hAB := Sz.sub S2
  have hABre := Complex.reCLM.summable hAB
  have htsum := Complex.re_tsum hAB
  have eA : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (2 + T * I - ρ) + 1 / ρ) =
      deriv xiZeta (2 + T * I) / xiZeta (2 + T * I) - b := by rw [ez]; ring
  have eB : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ) =
      deriv xiZeta 2 / xiZeta 2 - b := by rw [e2]; ring
  rw [Sz.tsum_sub S2, eA, eB] at htsum
  have hpt : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, windowWeight T ρ ≤
      Complex.reCLM ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (2 + T * I - ρ) + 1 / ρ) -
        (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ)) +
        2 * ((analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 : ℝ)) := fun ρ => by
    have := window_pointwise T ρ.2 (analyticOrderNatAt xiZeta ρ) (Nat.cast_nonneg _)
    simpa [windowWeight] using this
  have hmaj := hABre.add (hsq.mul_left 2)
  have hW : Summable (windowWeight T) :=
    Summable.of_nonneg_of_le (windowWeight_nonneg T) hpt hmaj
  refine ⟨hW, (hW.tsum_le_tsum hpt hmaj).trans ?_⟩
  rw [hABre.tsum_add (hsq.mul_left 2), tsum_mul_left]
  simp only [Complex.reCLM_apply] at htsum ⊢
  rw [← htsum]
  simp only [sub_re]
  linarith

/-! ### Step 3: zeros near height `T` -/

/-- **Step 3.** Each zero with `|γ - T| ≤ 1` has weight at least `1/5`. -/
theorem zeroCountOn_le_window_tsum (T : ℝ) {S : Set ℂ}
    (hS : S ⊆ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im - T| ≤ 1})
    (hW : Summable (windowWeight T)) :
    (zeroCountOn riemannZeta S : ℝ) ≤ 5 * ∑' ρ, windowWeight T ρ := by
  classical
  rw [zeroCountOn_riemannZeta_eq_xiZeta fun s hs => by linarith [(hS hs).1]]
  have hpos : 0 ≤ 5 * ∑' ρ, windowWeight T ρ :=
    mul_nonneg (by norm_num) (tsum_nonneg (windowWeight_nonneg T))
  set g : ℂ → ℕ := fun s => analyticOrderNatAt xiZeta s with hg
  by_cases hfin : (S ∩ Function.support g).Finite
  · unfold zeroCountOn
    rw [finsum_mem_eq_sum g hfin]
    set F := hfin.toFinset
    have hF : ∀ s ∈ F, xiZeta s = 0 := by
      intro s hs
      have hs' := (hfin.mem_toFinset.mp hs).2
      exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hs'
    have hFS : ∀ s ∈ F, s ∈ S := fun s hs => (hfin.mem_toFinset.mp hs).1
    push_cast
    calc ∑ s ∈ F, (g s : ℝ) ≤ ∑ s ∈ F, 5 * ((g s : ℝ) / (4 + (T - s.im) ^ 2)) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hw := (hS (hFS s hs)).2.2
          have h1 : (T - s.im) ^ 2 ≤ 1 := by
            rw [← sq_abs, abs_sub_comm]; nlinarith [abs_nonneg (s.im - T)]
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          have : (0 : ℝ) ≤ g s := Nat.cast_nonneg _
          nlinarith
      _ = 5 * ∑ ρ ∈ F.subtype (fun s => xiZeta s = 0), windowWeight T ρ := by
          rw [← Finset.mul_sum]
          congr 1
          rw [show (∑ ρ ∈ F.subtype (fun s => xiZeta s = 0), windowWeight T ρ) =
            ∑ ρ ∈ F.subtype (fun s => xiZeta s = 0),
              (fun s : ℂ => (g s : ℝ) / (4 + (T - s.im) ^ 2)) ρ from rfl,
            Finset.sum_subtype_eq_sum_filter (fun s : ℂ => (g s : ℝ) / (4 + (T - s.im) ^ 2)),
            Finset.filter_true_of_mem hF]
      _ ≤ 5 * ∑' ρ, windowWeight T ρ := by
          gcongr
          exact hW.sum_le_tsum _ (fun ρ _ => windowWeight_nonneg T ρ)
  · unfold zeroCountOn
    rw [finsum_mem_eq_zero_of_infinite hfin, Nat.cast_zero]
    exact hpos

/-! ### Step 4: `Re ξ'/ξ(2 + iT) ≪ log T` -/

/-- The real part of the `k`-th term of the digamma series at `1 + iy`. -/
lemma re_digamma_term (y : ℝ) (k : ℕ) :
    (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + y * I))).re =
      y ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [sub_re, inv_re_eq, inv_re_eq]
  have e1 : ((k : ℂ) + 1).re = (k : ℝ) + 1 := by simp
  have e2 : ((k : ℂ) + 1).im = 0 := by simp
  have e3 : ((k : ℂ) + (1 + y * I)).re = (k : ℝ) + 1 := by simp
  have e4 : ((k : ℂ) + (1 + y * I)).im = y := by simp
  rw [e1, e2, e3, e4]
  field_simp
  ring

lemma digamma_tail_term_le {y : ℝ} {N j : ℕ} (hN : 1 ≤ N) (hy : |y| ≤ N) (hj : N ≤ j) :
    y ^ 2 / (((j : ℝ) + 1) * (((j : ℝ) + 1) ^ 2 + y ^ 2)) ≤
      (N : ℝ) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hy2 : y ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have e : (N : ℝ) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) = N / ((j : ℝ) * ((j : ℝ) + 1)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : y ^ 2 * ((j : ℝ) * ((j : ℝ) + 1)) ≤ (N : ℝ) ^ 2 * ((j : ℝ) * ((j : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right hy2 (by positivity)
  have h2 : (N : ℝ) * (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ N * ((j : ℝ) + 1))
  have h4 : 0 ≤ (N : ℝ) * ((j : ℝ) + 1) * y ^ 2 := by positivity
  nlinarith [h1, h3, h4]

/-- `Re ψ(1 + iy) ≤ Re ψ(1) + 2 + log (|y| + 1)`. -/
theorem re_digamma_one_add_le (y : ℝ) :
    (digamma (1 + y * I)).re ≤ (digamma 1).re + 2 + Real.log (|y| + 1) := by
  set t : ℕ → ℝ := fun k => y ^ 2 / (((k : ℝ) + 1) * (((k : ℝ) + 1) ^ 2 + y ^ 2)) with ht
  have hS := Complex.hasSum_re (Erdos985.Analytic.BoundsAux.hasSum_digamma
    (w := 1 + y * I) (by simp; norm_num))
  simp only [re_digamma_term] at hS
  have ht0 : ∀ k, 0 ≤ t k := fun k => by simp only [ht]; positivity
  have hsum : Summable t := hS.summable
  set N : ℕ := ⌈|y|⌉₊
  have hyN : |y| ≤ N := Nat.le_ceil _
  have hNy : (N : ℝ) < |y| + 1 := Nat.ceil_lt_add_one (abs_nonneg y)
  -- head: `Σ_{k < N} t k ≤ 1 + log (|y| + 1)`
  have hhead : ∑ k ∈ Finset.range N, t k ≤ 1 + Real.log (|y| + 1) := by
    have hle : ∑ k ∈ Finset.range N, t k ≤ ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
      refine Finset.sum_le_sum fun k _ => ?_
      simp only [ht]
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ (by positivity) hk]
      nlinarith [sq_nonneg ((k : ℝ) + 1), sq_nonneg y]
    have hharm : ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) = ((harmonic N : ℚ) : ℝ) := by
      simp [harmonic]
    have hlog : Real.log N ≤ Real.log (|y| + 1) := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by linarith [abs_nonneg y])
      · exact Real.log_le_log (by exact_mod_cast hpos) hNy.le
    linarith [harmonic_le_one_add_log N]
  -- tail: `Σ_{k ≥ N} t k ≤ 1`
  have htail : ∑' k, t (k + N) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · have hy0 : y = 0 := by
        have : |y| ≤ 0 := by rw [h0] at hyN; exact_mod_cast hyN
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg y))
      simp [ht, hy0]
    · refine Real.tsum_le_of_sum_range_le (fun k => ht0 _) fun M => ?_
      have hstep : ∀ k ∈ Finset.range M, t (k + N) ≤
          (N : ℝ) * (1 / ((k + N : ℕ) : ℝ)) - (N : ℝ) * (1 / ((k + 1 + N : ℕ) : ℝ)) := by
        intro k _
        have := digamma_tail_term_le (y := y) (j := k + N) hpos hyN (by omega)
        calc t (k + N) = _ := rfl
          _ ≤ _ := this
          _ = _ := by push_cast; ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [Finset.sum_range_sub' (fun k => (N : ℝ) * (1 / ((k + N : ℕ) : ℝ))) M]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
      simp only [zero_add]
      rw [mul_one_div_cancel hN0.ne']
      have : 0 ≤ (N : ℝ) * (1 / ((M + N : ℕ) : ℝ)) := by positivity
      linarith
  have htot := hsum.sum_add_tsum_nat_add N
  have heq := hS.tsum_eq
  rw [sub_re] at heq
  linarith

/-- `ξ'/ξ = 1/s + 1/(s-1) + Γℝ'/Γℝ + ζ'/ζ` right of `Re s = 1`. -/
theorem logDeriv_xiZeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv xiZeta s / xiZeta s = (1 / s + 1 / (s - 1)) +
      (-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 * digamma (s / 2)) +
      deriv riemannZeta s / riemannZeta s := by
  have hne : ∀ w : ℂ, 1 < w.re → w ≠ 0 ∧ w ≠ 1 := fun w hw =>
    ⟨by rintro rfl; simp at hw; linarith, by rintro rfl; simp at hw⟩
  obtain ⟨h0, h1⟩ := hne s hs
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const continuous_re
  have hev : xiZeta =ᶠ[𝓝 s] fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) := by
    filter_upwards [hU.mem_nhds hs] with w hw
    obtain ⟨w0, w1⟩ := hne w hw
    rw [xiZeta_eq w0 w1, completedRiemannZeta_eq_mul w0
      (Gammaℝ_ne_zero_of_re_pos (by have : 1 < w.re := hw; linarith))]
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hdΓ := Erdos985.Analytic.StepAAux.hasDerivAt_Gammaℝ (w := s) (by linarith)
  have hdζ := (differentiableAt_riemannZeta h1).hasDerivAt
  have hdP : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hd : HasDerivAt (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w)) _ s :=
    hdP.mul (hdΓ.mul hdζ)
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds]
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

/-- `|ζ'/ζ(s)| ≤ Σ Λ(n)/n²` on `Re s = 2`. -/
theorem norm_logDeriv_riemannZeta_le {s : ℂ} (hs : s.re = 2) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have he : ∀ n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ =
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := fun n => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]; norm_num
  have hsum := summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1)
  rw [neg_div, eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero] at h
  rw [h, norm_neg, LSeries]
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  exact tsum_congr he

/-- **Step 4.** `Re ξ'/ξ(2 + iT) ≤ C + log (|T| + 2)`. -/
theorem re_logDeriv_xiZeta_le : ∃ C : ℝ, ∀ T : ℝ,
    (deriv xiZeta (2 + T * I) / xiZeta (2 + T * I)).re ≤ C + Real.log (|T| + 2) := by
  set K₂ := ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖
  refine ⟨3 / 2 - 1 / 2 * Real.log Real.pi + 1 / 2 * ((digamma 1).re + 2) + K₂, fun T => ?_⟩
  set s : ℂ := 2 + T * I with hsdef
  have hsre : s.re = 2 := by simp [s]
  have hsim : s.im = T := by simp [s]
  rw [logDeriv_xiZeta_eq (by rw [hsre]; norm_num)]
  have hζ := (re_le_norm _).trans (norm_logDeriv_riemannZeta_le hsre)
  have hhalf : s / 2 = 1 + ((T / 2 : ℝ) : ℂ) * I := by simp [s]; ring
  have hψ := re_digamma_one_add_le (T / 2)
  rw [← hhalf] at hψ
  have hr1 : (1 / s).re ≤ 1 / 2 := by
    rw [inv_re_eq, hsre, hsim, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg T]
  have hr2 : (1 / (s - 1)).re ≤ 1 := by
    rw [inv_re_eq]
    simp only [sub_re, one_re, sub_im, one_im, sub_zero, hsre, hsim]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg T]
  have hlog : Real.log (|T / 2| + 1) ≤ Real.log (|T| + 2) := by
    refine Real.log_le_log (by positivity) ?_
    rw [abs_div, abs_two]; linarith [abs_nonneg T]
  have hlog0 : 0 ≤ Real.log (|T| + 2) := Real.log_nonneg (by linarith [abs_nonneg T])
  simp only [add_re, mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero,
    div_ofNat_re, one_re, div_ofNat_im, one_im, zero_div, zero_mul] at *
  norm_num at *
  nlinarith

/-! ### The local bound -/

/-- **Local zero count.** The zeros of `ζ`, with multiplicity, in any set inside the box
`0 ≤ Re s ≤ 1`, `|Im s - T| ≤ 1` number at most `C log (|T| + 2)`, uniformly in `T : ℝ`. In
particular `N(T + 1) - N(T) ≪ log T`. -/
theorem zeroCountOn_riemannZeta_le_of_subset_box :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, ∀ S : Set ℂ,
      S ⊆ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im - T| ≤ 1} →
      (zeroCountOn riemannZeta S : ℝ) ≤ C * Real.log (|T| + 2) := by
  obtain ⟨K, hK⟩ := tsum_window_le
  obtain ⟨C₁, hC₁⟩ := re_logDeriv_xiZeta_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D := max 0 (C₁ + K)
  refine ⟨5 * (1 + D / Real.log 2), by positivity, fun T S hS => ?_⟩
  obtain ⟨hW, hle⟩ := hK T
  have hL : Real.log 2 ≤ Real.log (|T| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  have hD : D ≤ D / Real.log 2 * Real.log (|T| + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL (le_max_left _ _)
  calc (zeroCountOn riemannZeta S : ℝ) ≤ 5 * ∑' ρ, windowWeight T ρ :=
        zeroCountOn_le_window_tsum T hS hW
    _ ≤ 5 * (C₁ + Real.log (|T| + 2) + K) := by linarith [hC₁ T]
    _ ≤ 5 * (D + Real.log (|T| + 2)) := by linarith [le_max_right 0 (C₁ + K)]
    _ ≤ 5 * (1 + D / Real.log 2) * Real.log (|T| + 2) := by nlinarith

end Density
