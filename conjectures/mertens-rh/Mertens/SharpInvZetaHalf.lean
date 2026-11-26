import Mertens.SharpInvZeta

/-!
# `1/ζ(s) ≪ exp(C log t / log log t)` on Titchmarsh's region `σ ≥ 1/2 + 1/log log t` (RH)

`Mertens.SharpLower` runs Selberg's device with the crude bounds `‖D(s,x)‖ ≤ (x+1)(log x)²` and
`‖E_R(s,x)‖ ≤ x + 1 + S`, and needs `(σ - 1/2) log x ≥ 4`; the `x` there forces
`log x < log log t` and so the region `σ ≥ 1/2 + c/log log t` with `c > 4`. Here three changes
reach `c = 1`:

1. `norm_dirPoly_le_half`: on `Re s ≥ 1/2`, `‖D(s,x)‖ ≤ 2√x (log x)²`, from
   `Λ(n) n^{-σ} log(x/n) ≤ (log x)² n^{-1/2}` and `∑_{n ≤ N} n^{-1/2} ≤ 2√N`;
   `norm_ER_le_half`: `‖E_R(s,x)‖ ≤ √x + 1 + S` (the pole term is `x^{1-σ} ≤ √x`).
2. `norm_zeroTerm_le_sharp`: at `s₀` itself the zero term is `≤ (1 + x^{-η}) m_ρ/|ρ - s₀|²`,
   and `x^{-η} ≤ e^{-3/2} ≤ 1/4` once `η log x ≥ 3/2`, `η = σ₀ - 1/2`.
3. `re_logDeriv_xi_le_half` (Selberg's device): with these, `η log x ≥ 3/2` suffices:
   `L W ≤ C + (5/4) W/η + L‖R‖ ≤ C + (5/6) L W + L‖R‖`, so `W ≤ 6C/L + 6‖R‖`.

With `log x = (3/2) log log t` and `σ - 1/2 ≥ 1/log log t`, `√x = (log t)^{3/4}`, and the
`√x (log x)` terms are `o(log t / log log t)`: `invZetaSharp_of_RH : InvZetaSharpBound`.
-/

open Complex MeasureTheory intervalIntegral Set Filter

namespace Mertens

open Littlewood Erdos985.Analytic ArithmeticFunction

/-- `InvZetaSharpBoundWith c` is monotone in `c`. -/
theorem InvZetaSharpBoundWith.mono {c c' : ℝ} (h : InvZetaSharpBoundWith c) (hc : c ≤ c') :
    InvZetaSharpBoundWith c' := by
  obtain ⟨C, t₀, hC⟩ := h
  refine ⟨C, max t₀ (Real.exp (Real.exp 1)), fun s hs hre => hC s (le_trans (le_max_left _ _) hs)
    (le_trans ?_ hre)⟩
  have ht : Real.exp (Real.exp 1) ≤ |s.im| := le_trans (le_max_right _ _) hs
  have ht0 : 0 < |s.im| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hu : Real.exp 1 ≤ Real.log |s.im| := by rw [Real.le_log_iff_exp_le ht0]; exact ht
  have hu0 : 0 < Real.log |s.im| := lt_of_lt_of_le (Real.exp_pos 1) hu
  have hv : 1 ≤ Real.log (Real.log |s.im|) := by rw [Real.le_log_iff_exp_le hu0]; exact hu
  have hv0 : 0 < Real.log (Real.log |s.im|) := by linarith
  have : c / Real.log (Real.log |s.im|) ≤ c' / Real.log (Real.log |s.im|) :=
    div_le_div_of_nonneg_right hc hv0.le
  linarith

/-- `A ((log u)² u^α + 1) + B ≤ u / log u` for large `u`, `0 ≤ α < 1`. -/
lemma eventually_le_div_log_rpow (A B : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∀ᶠ u : ℝ in atTop, A * (Real.log u ^ 2 * u ^ α + 1) + B ≤ u / Real.log u := by
  set c := 2 * |A| + |B| + 1 with hc
  have hc0 : 0 < c := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop 3 (show (0 : ℝ) < 1 - α by linarith)).def
    (show 0 < 1 / c by positivity)
  filter_upwards [hlo, eventually_ge_atTop (Real.exp 1)] with u h1 hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  have hu1 : 1 ≤ u := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hu
  have hℓ : 1 ≤ Real.log u := by rw [Real.le_log_iff_exp_le hu0]; exact hu
  set ℓ := Real.log u
  set r := u ^ (1 - α) with hr
  set q := u ^ α with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hu1 hα0
  have hrq : r * q = u := by
    rw [hr, hq, ← Real.rpow_add hu0]; norm_num
  have h3 : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _), h3] at h1
  have hℓ3 : c * ℓ ^ 3 ≤ r := by
    have := mul_le_mul_of_nonneg_left h1 hc0.le
    rw [← mul_assoc, mul_one_div_cancel hc0.ne', one_mul] at this
    exact this
  have hℓ1 : ℓ ≤ ℓ ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ - 1) (by positivity : (0 : ℝ) ≤ ℓ * (ℓ + 1))]
  have hℓ2 : ℓ ^ 2 * ℓ = ℓ ^ 3 := by ring
  rw [le_div_iff₀ (by linarith)]
  have hA : A * (ℓ ^ 2 * q + 1) ≤ |A| * (ℓ ^ 2 * q + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
  have hB := le_abs_self B
  have hpos : 0 ≤ ℓ ^ 3 * q := by positivity
  have e1 : ℓ ≤ ℓ ^ 3 * q := by nlinarith
  calc (A * (ℓ ^ 2 * q + 1) + B) * ℓ ≤ (|A| * (ℓ ^ 2 * q + 1) + |B|) * ℓ := by gcongr
    _ = |A| * (ℓ ^ 3 * q) + |A| * ℓ + |B| * ℓ := by rw [← hℓ2]; ring
    _ ≤ |A| * (ℓ ^ 3 * q) + |A| * (ℓ ^ 3 * q) + |B| * (ℓ ^ 3 * q) := by gcongr
    _ ≤ c * ℓ ^ 3 * q := by rw [hc]; nlinarith [abs_nonneg A, abs_nonneg B]
    _ ≤ r * q := by nlinarith
    _ = u := hrq

/-- `∑_{n ≤ N} n^{-1/2} ≤ 2 √N` (the `n = 0` term is `(√0)⁻¹ = 0`). -/
lemma sum_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (Real.sqrt n)⁻¹ ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    set a := Real.sqrt N with ha
    set b := Real.sqrt ((N + 1 : ℕ) : ℝ) with hb
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.2 (by positivity)
    have hab : b ^ 2 = a ^ 2 + 1 := by
      rw [ha, hb, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
    have hstep : b⁻¹ ≤ 2 * b - 2 * a := by
      rw [inv_eq_one_div, div_le_iff₀ hb0]
      nlinarith [sq_nonneg (a - b)]
    linarith

/-- **`‖D(s, x)‖ ≤ 2 √x (log x)²` on `Re s ≥ 1/2`.** -/
theorem norm_dirPoly_le_half {s : ℂ} (hs : 1 / 2 ≤ s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖dirPoly s x‖ ≤ 2 * Real.sqrt x * Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hterm : ∀ n ∈ Finset.range (⌊x⌋₊ + 1),
      ‖(Λ n : ℂ) * (n : ℂ) ^ (-s) * (Real.log (x / n) : ℂ)‖ ≤
        Real.log x ^ 2 * (Real.sqrt n)⁻¹ := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    rw [Finset.mem_range] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 (Nat.lt_succ_iff.1 hn)).trans (Nat.floor_le hx0.le)
    rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      norm_natCast_cpow_of_pos hn0]
    have h1 : Λ n ≤ Real.log x :=
      vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hnx)
    have h2 : (n : ℝ) ^ (-s).re ≤ (Real.sqrt n)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by simp; linarith)
    have h3 : ‖Real.log (x / n)‖ ≤ Real.log x := by
      rw [Real.norm_of_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)),
        Real.log_div hx0.ne' (by linarith)]
      linarith [Real.log_nonneg hn1]
    have h0 : 0 ≤ (n : ℝ) ^ (-s).re := Real.rpow_nonneg (by linarith) _
    calc Λ n * (n : ℝ) ^ (-s).re * ‖Real.log (x / n)‖
        ≤ Real.log x * (Real.sqrt n)⁻¹ * Real.log x := by
          gcongr
      _ = Real.log x ^ 2 * (Real.sqrt n)⁻¹ := by ring
  calc ‖dirPoly s x‖ ≤ ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        ‖(Λ n : ℂ) * (n : ℂ) ^ (-s) * (Real.log (x / n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Real.log x ^ 2 * (Real.sqrt n)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = Real.log x ^ 2 * ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Real.sqrt n)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Real.log x ^ 2 * (2 * Real.sqrt (⌊x⌋₊ : ℝ)) := by
        gcongr; exact sum_inv_sqrt_le _
    _ ≤ Real.log x ^ 2 * (2 * Real.sqrt x) := by
        gcongr; exact Nat.floor_le hx0.le
    _ = 2 * Real.sqrt x * Real.log x ^ 2 := by ring

/-- **`‖E_R(s, x)‖ ≤ √x + 1 + Σ 1/(k+1)²`** for `Re s ≥ 1/2`, `|Im s| ≥ 1`, `x ≥ 1`. -/
theorem norm_ER_le_half {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : 1 ≤ |s.im|) {x : ℝ} (hx : 1 ≤ x) :
    ‖ER s x‖ ≤ Real.sqrt x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 ≤ s.re := by linarith
  have hS : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := Erdos985.Analytic.BoundsAux.summable_inv_sq_succ
  have hcpow : ∀ b : ℂ, ‖(x : ℂ) ^ b‖ = x ^ b.re := fun b => norm_cpow_eq_rpow_re_of_pos hx0 b
  have h1s : 1 ≤ ‖1 - s‖ := by
    refine ht.trans (le_trans ?_ (abs_im_le_norm _)); simp
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  have hpole : ‖((x : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2‖ ≤ Real.sqrt x + 1 := by
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have hp : ‖(x : ℂ) ^ (1 - s) - 1‖ ≤ Real.sqrt x + 1 := by
      calc ‖(x : ℂ) ^ (1 - s) - 1‖ ≤ ‖(x : ℂ) ^ (1 - s)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = x ^ (1 - s.re) + 1 := by rw [hcpow]; simp
        _ ≤ x ^ (1 / 2 : ℝ) + 1 := by
            have := Real.rpow_le_rpow_of_exponent_le hx (show 1 - s.re ≤ 1 / 2 by linarith)
            linarith
        _ = Real.sqrt x + 1 := by rw [Real.sqrt_eq_rpow]
    have : 1 ≤ ‖1 - s‖ ^ 2 := one_le_pow₀ h1s
    nlinarith
  have htriv : ∀ k : ℕ, ‖-1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)‖
      ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hd := norm_trivPole_sub_ge hs0 k
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [norm_mul, norm_neg, norm_one, one_mul, norm_div, norm_pow]
    have hnum : ‖(x : ℂ) ^ (trivPole k - s) - 1‖ ≤ 2 := by
      calc ‖(x : ℂ) ^ (trivPole k - s) - 1‖ ≤ ‖(x : ℂ) ^ (trivPole k - s)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [hcpow, norm_one]
            gcongr
            refine Real.rpow_le_one_of_one_le_of_nonpos hx ?_
            simp only [trivPole, sub_re, mul_re, natCast_re, natCast_im]; norm_num
            linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        _ = 2 := by norm_num
    have hden : 4 * ((k : ℝ) + 1) ^ 2 ≤ ‖trivPole k - s‖ ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have hsumT : Summable fun k : ℕ =>
      ‖-1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)‖ :=
    hS.of_nonneg_of_le (fun _ => norm_nonneg _) htriv
  calc ‖ER s x‖ ≤ ‖((x : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2‖ +
        ‖∑' k : ℕ, -1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)‖ :=
          norm_add_le _ _
    _ ≤ (Real.sqrt x + 1) + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
        gcongr
        exact (norm_tsum_le_tsum_norm hsumT).trans (hsumT.tsum_le_tsum htriv hS)

/-- `e^{-3/2} ≤ 1/4`. -/
lemma exp_neg_three_halves_le : Real.exp (-(3 / 2)) ≤ 1 / 4 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : 1 / 2 + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have h3 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have h4 : 4 ≤ Real.exp (3 / 2) := by rw [h3]; nlinarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **The zero term at `s₀`, sharply**: `‖zeroTerm‖ ≤ (5/4) m_ρ/|ρ - s₀|²` once
`(σ₀ - 1/2) log x ≥ 3/2`. -/
lemma norm_zeroTerm_le_sharp (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) (t : ℝ)
    (ρ : XiZero) {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h32 : 3 / 2 ≤ (σ₀ - 1 / 2) * Real.log x) :
    ‖Littlewood.zeroTerm x t ρ σ₀‖ ≤ 5 / 4 * ((analyticOrderNatAt xiZeta ρ : ℝ) /
      normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))) := by
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  have hx0 : 0 < x := by linarith
  have hpos : 0 < normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I)) :=
    normSq_pos.2 (sub_line_ne_zero hρ h0 t)
  unfold Littlewood.zeroTerm
  rw [norm_mul, show ‖mult ρ‖ = (analyticOrderNatAt xiZeta ρ : ℝ) by simp [mult], norm_div,
    norm_pow, ← Complex.normSq_eq_norm_sq]
  have hxp : ‖(x : ℂ) ^ ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))‖ ≤ 1 / 4 := by
    rw [norm_cpow_eq_rpow_re_of_pos hx0, Real.rpow_def_of_pos hx0]
    have hre : ((ρ : ℂ) - ((σ₀ : ℂ) + t * I)).re = -(σ₀ - 1 / 2) := by simp [hρ]
    rw [hre]
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_three_halves_le
    nlinarith
  have hnum : ‖(x : ℂ) ^ ((ρ : ℂ) - ((σ₀ : ℂ) + t * I)) - 1‖ ≤ 5 / 4 := by
    calc _ ≤ ‖(x : ℂ) ^ ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 := by rw [norm_one]; linarith
      _ = 5 / 4 := by norm_num
  have hm : 0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) := Nat.cast_nonneg _
  calc (analyticOrderNatAt xiZeta ρ : ℝ) * (‖(x : ℂ) ^ ((ρ : ℂ) - ((σ₀ : ℂ) + t * I)) - 1‖ /
        normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I)))
      ≤ (analyticOrderNatAt xiZeta ρ : ℝ) * (5 / 4 / normSq ((ρ : ℂ) - ((σ₀ : ℂ) + t * I))) := by
        gcongr
    _ = _ := by ring

/-- The constant `C(x) = 2√x (log x)² + √x + 1 + S` of the half-line explicit formula. -/
noncomputable def Chalf (x : ℝ) : ℝ :=
  2 * Real.sqrt x * Real.log x ^ 2 + (Real.sqrt x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)

lemma Chalf_nonneg {x : ℝ} : 0 ≤ Chalf x := by
  unfold Chalf
  have : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := tsum_nonneg fun _ => by positivity
  positivity

/-- **Selberg's device on the half line** (RH): for `t ≥ 1` and `(σ₀ - 1/2) log x ≥ 3/2`,
`Re ξ'/ξ(σ₀+it) ≤ 6 C(x)/log x + 6‖R(σ₀+it)‖`. -/
theorem re_logDeriv_xi_le_half (hRH : RiemannHypothesis) {t x σ₀ : ℝ} (ht : 1 ≤ t)
    (hx : 1 < x) (h0 : 1 / 2 < σ₀)
    (h32 : 3 / 2 ≤ (σ₀ - 1 / 2) * Real.log x) :
    (deriv xiZeta ((σ₀ : ℂ) + t * I) / xiZeta ((σ₀ : ℂ) + t * I)).re ≤
      6 * Chalf x / Real.log x + 6 * ‖archR ((σ₀ : ℂ) + t * I)‖ := by
  have := countable_xiZero
  have hx1 : 1 ≤ x := hx.le
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos hx
  set C := Chalf x with hC
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀
  set η := σ₀ - 1 / 2 with hη
  have hη0 : 0 < η := by linarith
  have hs₀re : 1 / 2 < s₀.re := by simp [hs₀]; linarith
  have hne1 : s₀ ≠ 1 := fun h => by have := congrArg im h; simp [hs₀] at this; linarith
  have hζ : riemannZeta s₀ ≠ 0 := Lindelof.riemannZeta_ne_zero_of_RH hRH hs₀re hne1
  set W := (deriv xiZeta s₀ / xiZeta s₀).re with hW
  have hR := hasSum_re_logDeriv_xi hRH hs₀re
  have hterm : ∀ ρ : XiZero, (mult ρ * (1 / (s₀ - ρ))).re =
      η * ((analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀)) := by
    intro ρ
    rw [re_mult_div hRH s₀ ρ, normSq_sub_comm]
    simp [hs₀, hη]
    ring
  simp_rw [hterm] at hR
  have hW0 : 0 ≤ W := hR.nonneg fun ρ =>
    mul_nonneg hη0.le (div_nonneg (Nat.cast_nonneg _) (normSq_nonneg _))
  have hsumm := summable_mult_div_normSq hRH hs₀re
  have hsig : ∑' ρ : XiZero, (analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀) =
      W / η := by
    rw [hW, ← hR.tsum_eq, tsum_mul_left]; field_simp
  -- the zero sum at `s₀`
  have hZ : ‖zeroSum s₀ x‖ ≤ 5 / 4 * (W / η) := by
    set u : XiZero → ℝ := fun ρ =>
      5 / 4 * ((analyticOrderNatAt xiZeta ρ : ℝ) / normSq ((ρ : ℂ) - s₀))
    have hu : Summable u := hsumm.mul_left _
    have hb : ∀ ρ, ‖Littlewood.zeroTerm x t ρ σ₀‖ ≤ u ρ := fun ρ =>
      norm_zeroTerm_le_sharp hRH hx t ρ h0 h32
    have hsn : Summable fun ρ => ‖Littlewood.zeroTerm x t ρ σ₀‖ :=
      hu.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    have heq : zeroSum s₀ x = ∑' ρ, Littlewood.zeroTerm x t ρ σ₀ := rfl
    rw [heq]
    calc ‖∑' ρ, Littlewood.zeroTerm x t ρ σ₀‖ ≤ ∑' ρ, ‖Littlewood.zeroTerm x t ρ σ₀‖ :=
          norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' ρ, u ρ := hsn.tsum_le_tsum hb hu
      _ = 5 / 4 * (W / η) := by rw [tsum_mul_left, hsig]
  -- the explicit formula at `s₀`
  have hE := explicit_formula hRH hs₀re hne1 hx1
  have hD := norm_dirPoly_le_half (s := s₀) (by simp [hs₀]; linarith) hx1
  have hER := norm_ER_le_half (s := s₀) (by simp [hs₀]; linarith)
    (by simpa [hs₀, abs_of_pos (by linarith : (0 : ℝ) < t)] using ht) hx1
  have hlog : L * ‖deriv riemannZeta s₀ / riemannZeta s₀‖ ≤ C + 5 / 4 * (W / η) := by
    have h := congrArg norm hE
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hL.le] at h
    rw [h]
    calc ‖dirPoly s₀ x + zeroSum s₀ x - ER s₀ x‖
        ≤ ‖dirPoly s₀ x‖ + ‖zeroSum s₀ x‖ + ‖ER s₀ x‖ := by
          refine (norm_sub_le _ _).trans ?_
          linarith [norm_add_le (dirPoly s₀ x) (zeroSum s₀ x)]
      _ ≤ C + 5 / 4 * (W / η) := by rw [hC, Chalf]; linarith
  have hxi : deriv xiZeta s₀ / xiZeta s₀ =
      deriv riemannZeta s₀ / riemannZeta s₀ + archR s₀ := by
    rw [logDeriv_riemannZeta_eq_archR (by linarith) hne1 hζ]; ring
  have hWle : W ≤ ‖deriv riemannZeta s₀ / riemannZeta s₀‖ + ‖archR s₀‖ := by
    rw [hW, hxi, add_re]
    linarith [re_le_norm (deriv riemannZeta s₀ / riemannZeta s₀), re_le_norm (archR s₀)]
  -- `(5/4) W/η ≤ (5/6) L W`
  have hk : 5 / 4 * (W / η) ≤ 5 / 6 * (L * W) := by
    have hinv : 1 / η ≤ 2 / 3 * L := by
      rw [div_le_iff₀ hη0]; nlinarith
    have : W / η = W * (1 / η) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hinv hW0
    nlinarith
  have hLW : L * W ≤ L * ‖deriv riemannZeta s₀ / riemannZeta s₀‖ + L * ‖archR s₀‖ := by
    have := mul_le_mul_of_nonneg_left hWle hL.le
    linarith
  have hmain : L * W ≤ 6 * C + 6 * L * ‖archR s₀‖ := by linarith
  rw [div_add' _ _ _ hL.ne', le_div_iff₀ hL]
  linarith

/-- **The lower bound on the half line, for large `t`** (RH): for `t ≥ 1`, `x ≥ e²`,
`σ₀ ≤ 2` and `(σ₀ - 1/2) log x ≥ 3/2`,
`1/|ζ(σ₀+it)| ≤ exp(A + (8 C(x) + 12 log(3+t) + 60)/log x)`. -/
theorem norm_inv_zeta_le_large_half (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ t x σ₀ : ℝ, 1 ≤ t → Real.exp 2 ≤ x → 1 / 2 < σ₀ → σ₀ ≤ 2 →
      3 / 2 ≤ (σ₀ - 1 / 2) * Real.log x →
      ‖(riemannZeta ((σ₀ : ℂ) + t * I))⁻¹‖ ≤
        Real.exp (A + (8 * Chalf x + 12 * Real.log (3 + t) + 60) / Real.log x) := by
  obtain ⟨A₀, hA₀, hA₀t⟩ := log_norm_zeta_two_ge
  refine ⟨A₀, hA₀, fun t x σ₀ ht hx h0 h2 h32 => ?_⟩
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.add_one_le_exp (2 : ℝ); linarith) hx
  have hL2 : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  set L := Real.log x with hLdef
  have hL : 0 < L := by linarith
  set C := Chalf x with hC
  have hC0 : 0 ≤ C := Chalf_nonneg
  have hηL : 1 ≤ (σ₀ - 1 / 2) * L := by linarith
  set s₀ : ℂ := (σ₀ : ℂ) + t * I with hs₀
  set W := (deriv xiZeta s₀ / xiZeta s₀).re with hW
  have hWb := re_logDeriv_xi_le_half hRH ht hx1 h0 h32
  have hR := norm_archR_le (s := s₀) (by simp [hs₀]; linarith) (by simp [hs₀]; exact h2)
    (by simpa [hs₀, abs_of_pos (by linarith : (0 : ℝ) < t)] using ht)
  have him : s₀.im = t := by simp [hs₀]
  rw [him, abs_of_pos (by linarith : (0 : ℝ) < t)] at hR
  -- the integrated lower bound
  have hint : -(2 * C) - 2 * W ≤
      L * (Real.log ‖riemannZeta (σ₀ + t * I)‖ - Real.log ‖riemannZeta (2 + t * I)‖) := by
    rw [log_norm_zeta_sub_eq hRH ht h0 h2, ← intervalIntegral.integral_const_mul]
    obtain ⟨hZi, hZ⟩ := integral_zeroSum_ge hRH (t := t) hx1 h0 h2 hηL
    have hg : IntervalIntegrable (fun σ : ℝ => L * (-(deriv riemannZeta (σ + t * I) /
        riemannZeta (σ + t * I))).re) volume σ₀ 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      have := continuousOn_re_logDeriv_zeta hRH ht h0 h2
      simp only [neg_re]
      exact continuousOn_const.mul this.neg
    have hpt : ∀ σ ∈ Set.Icc σ₀ 2, -C + (zeroSum ((σ : ℂ) + t * I) x).re ≤
        L * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re := by
      intro σ hσ
      have hσ0 : 1 / 2 < ((σ : ℂ) + t * I).re := by simp; linarith [hσ.1]
      have hne1 : (σ : ℂ) + t * I ≠ 1 := fun h => by
        have := congrArg im h; simp at this; linarith
      have hE := explicit_formula hRH hσ0 hne1 hx1.le
      have hre := congrArg re hE
      rw [re_ofReal_mul, sub_re, add_re] at hre
      rw [hre]
      have hD := (neg_le_of_abs_le (abs_re_le_norm _)).trans' (neg_le_neg (norm_dirPoly_le_half
        (s := (σ : ℂ) + t * I) (by simp; linarith [hσ.1]) hx1.le))
      have hER := (re_le_norm (ER ((σ : ℂ) + t * I) x)).trans
        (norm_ER_le_half (s := (σ : ℂ) + t * I) (by simp; linarith [hσ.1])
          (by simpa [abs_of_pos (by linarith : (0 : ℝ) < t)] using ht) hx1.le)
      have : -(2 * Real.sqrt x * L ^ 2) ≤ (dirPoly ((σ : ℂ) + t * I) x).re := hD
      rw [hC, Chalf]; linarith
    calc -(2 * C) - 2 * W ≤ (2 - σ₀) * (-C) + -(2 * W) := by
          have : (2 - σ₀) * C ≤ 2 * C := mul_le_mul_of_nonneg_right (by linarith) hC0
          linarith
      _ ≤ (2 - σ₀) * (-C) + ∫ σ in σ₀..2, (zeroSum ((σ : ℂ) + t * I) x).re := by linarith
      _ = ∫ σ in σ₀..2, (-C + (zeroSum ((σ : ℂ) + t * I) x).re) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
            intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ σ in σ₀..2, L * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re :=
          intervalIntegral.integral_mono_on h2 (intervalIntegrable_const.add hZi) hg hpt
  -- assemble
  have h2t := hA₀t t
  have hne1 : s₀ ≠ 1 := fun h => by have := congrArg im h; simp [hs₀] at this; linarith
  have hζ : riemannZeta s₀ ≠ 0 :=
    Lindelof.riemannZeta_ne_zero_of_RH hRH (by simp [hs₀]; linarith) hne1
  have h6C : 6 * C / L ≤ 3 * C := by
    rw [div_le_iff₀ hL]; nlinarith
  have hW2 : 2 * W ≤ 6 * C + 12 * (Real.log (3 + t) + 5) := by
    have : 2 * (6 * C / L + 6 * ‖archR s₀‖) = 2 * (6 * C / L) + 12 * ‖archR s₀‖ := by ring
    have hR' : ‖archR s₀‖ ≤ Real.log (3 + t) + 5 := hR
    linarith
  have hlow : -(A₀ + (8 * C + 12 * Real.log (3 + t) + 60) / L) ≤
      Real.log ‖riemannZeta s₀‖ := by
    have hint' : -(2 * C) - 2 * W ≤
        L * (Real.log ‖riemannZeta s₀‖ - Real.log ‖riemannZeta (2 + t * I)‖) := by
      have := hint; simp only [hs₀] at this ⊢; linarith
    have hfin : -(8 * C + 12 * Real.log (3 + t) + 60) ≤
        L * (Real.log ‖riemannZeta s₀‖ - Real.log ‖riemannZeta (2 + t * I)‖) := by linarith
    have hdiv : -(8 * C + 12 * Real.log (3 + t) + 60) / L ≤
        Real.log ‖riemannZeta s₀‖ - Real.log ‖riemannZeta (2 + t * I)‖ := by
      rw [div_le_iff₀ hL]; linarith
    rw [neg_div] at hdiv
    linarith
  have hpos : 0 < ‖(riemannZeta s₀)⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hζ)
  rw [← Real.exp_log hpos, norm_inv, Real.log_inv]
  exact Real.exp_le_exp.2 (by linarith)

set_option maxHeartbeats 800000 in
/-- **Littlewood–Titchmarsh (RH)**: `1/|ζ(s)| ≤ exp(9 log t / log log t)` on
`σ ≥ 1/2 + 1/log log t`, `t = |Im s|` large. -/
theorem invZetaSharp_of_RH (hRH : RiemannHypothesis) : InvZetaSharpBound := by
  obtain ⟨A, hA0, hA⟩ := norm_inv_zeta_le_large_half hRH
  obtain ⟨C₂, hC₂⟩ := norm_inv_zeta_le_of_two_le
  set S := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hlC : 0 ≤ Real.log (max C₂ 1) := Real.log_nonneg (le_max_right _ _)
  set B := A + 8 * S + 22 + Real.log (max C₂ 1) with hB
  obtain ⟨U, hU⟩ := eventually_atTop.1
    (eventually_le_div_log_rpow 40 B (α := 3 / 4) (by norm_num) (by norm_num))
  set U' := max U (Real.exp 4) with hU'
  show InvZetaSharpBoundWith 1
  refine ⟨9, Real.exp U', fun s hts hre => ?_⟩
  set t := |s.im| with htdef
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) hts
  set u := Real.log t with hudef
  have hu : U' ≤ u := by rw [hudef, Real.le_log_iff_exp_le ht0]; exact hts
  have hu4 : Real.exp 4 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 4) hu4
  have hu1 : 1 ≤ u := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hu4
  set v := Real.log u with hvdef
  have hv4 : 4 ≤ v := by rw [hvdef, Real.le_log_iff_exp_le hu0]; exact hu4
  have hv0 : 0 < v := by linarith
  have hkey := hU u (le_trans (le_max_left _ _) hu)
  have ht1 : 1 ≤ t := by
    rw [hudef] at hu1
    by_contra h; push Not at h
    have := Real.log_lt_log ht0 h
    rw [Real.log_one] at this; linarith
  set r := u ^ (3 / 4 : ℝ) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hu1 (by norm_num)
  have hfin_pos : 0 ≤ u / v := by positivity
  rcases le_or_gt s.re 2 with h2 | h2
  · rw [norm_inv_zeta_abs_im]
    set L := 3 / 2 * v with hL
    have hL6 : 6 ≤ L := by rw [hL]; linarith
    have hL0 : 0 < L := by linarith
    have hx : Real.exp 2 ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
    have hre' : 1 / 2 < s.re := by
      have : 0 < 1 / v := by positivity
      linarith
    have h32 : 3 / 2 ≤ (s.re - 1 / 2) * Real.log (Real.exp L) := by
      rw [Real.log_exp]
      have h1 : 1 / v ≤ s.re - 1 / 2 := by linarith
      have := mul_le_mul_of_nonneg_right h1 hL0.le
      have e : 1 / v * L = 3 / 2 := by rw [hL]; field_simp
      linarith
    have hb := hA t (Real.exp L) s.re ht1 hx hre' h2 h32
    refine hb.trans (Real.exp_le_exp.2 ?_)
    have hsq : Real.sqrt (Real.exp L) = r := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul, hr, Real.rpow_def_of_pos hu0, ← hvdef, hL]
      ring_nf
    have hCh : Chalf (Real.exp L) = 2 * r * L ^ 2 + (r + 1 + S) := by
      rw [Chalf, Real.log_exp, hsq]
    rw [hCh, Real.log_exp]
    have hlogt3 : Real.log (3 + t) ≤ u + 2 := by
      have h1 : Real.log (3 + t) ≤ Real.log (4 * t) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) ht0.ne'] at h1
      have : Real.log 4 ≤ 2 := by
        have h2' : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have := Real.log_two_lt_d9
        linarith
      linarith
    have hR0 : 0 ≤ r + 1 + S := by linarith
    have hQ : (8 * (2 * r * L ^ 2 + (r + 1 + S)) + 12 * Real.log (3 + t) + 60) / L ≤
        24 * r * v + 8 * (r + 1 + S) + 8 * (u / v) + 14 := by
      rw [div_le_iff₀ hL0]
      have e : (24 * r * v + 8 * (r + 1 + S) + 8 * (u / v) + 14) * L =
          36 * r * v ^ 2 + 12 * v * (r + 1 + S) + 12 * u + 21 * v := by
        rw [hL]; field_simp; ring
      have e2 : 8 * (2 * r * L ^ 2) = 36 * r * v ^ 2 := by rw [hL]; ring
      have p1 : 8 * (r + 1 + S) ≤ 12 * v * (r + 1 + S) := by
        have := mul_le_mul_of_nonneg_right (show (8 : ℝ) ≤ 12 * v by linarith) hR0
        linarith
      rw [e]
      linarith only [e2, p1, hlogt3, hv4]
    have hrv : 24 * r * v + 8 * r ≤ 32 * (v ^ 2 * r) := by
      have hrv0 : 0 ≤ r * v := by positivity
      have h1 : r * v * 1 ≤ r * v * v := mul_le_mul_of_nonneg_left (by linarith) hrv0
      have hv2 : 1 ≤ v ^ 2 := by nlinarith
      have h2 : r * 1 ≤ r * v ^ 2 := mul_le_mul_of_nonneg_left hv2 (by linarith)
      have e1 : v ^ 2 * r = r * v * v := by ring
      have e2 : v ^ 2 * r = r * v ^ 2 := by ring
      linarith
    have hk : 40 * (v ^ 2 * r + 1) + B ≤ u / v := hkey
    have hvr0 : 0 ≤ v ^ 2 * r := by positivity
    have e9 : 9 * u / v = 9 * (u / v) := by ring
    rw [e9]
    rw [hB] at hk
    linarith only [hQ, hrv, hk, hlC, hvr0]
  · have hb := hC₂ s h2.le
    refine hb.trans ?_
    have hk : Real.log (max C₂ 1) ≤ u / v := by
      have hA' : 0 ≤ 40 * (v ^ 2 * r + 1) := by positivity
      have := hkey; rw [hB] at this; linarith
    calc C₂ ≤ max C₂ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max C₂ 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (9 * u / v) := by
          apply Real.exp_le_exp.2
          have : 9 * u / v = 9 * (u / v) := by ring
          rw [this]; linarith

/-- Every `c ≥ 1` (in particular the `c = 8` of `invZetaSharpWith_of_RH`). -/
theorem invZetaSharpWith_of_RH_of_one_le (hRH : RiemannHypothesis) {c : ℝ} (hc : 1 ≤ c) :
    InvZetaSharpBoundWith c :=
  (invZetaSharp_of_RH hRH).mono hc

end Mertens
