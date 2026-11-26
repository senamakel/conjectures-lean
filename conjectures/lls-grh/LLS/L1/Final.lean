import LLS.L1.Weak
import LLS.Numerics.Interval

/-!
# The `L(1, χ)` bounds with explicit constants (numerical part)

With `x = 10^5` when `log² q < 10^5` and `x = ⌊log² q⌋` otherwise, the zero sum satisfies
`Z ≤ Zb = (log q + 2 log x)/(1 − 2/√x)` (`Z2_le_general`), and the `c` of
`log_norm_L1_le_c`/`neg_log_norm_L1_le_c` is at most `2.9 + 1.095 Zb/√x`. Then
`|L(1,χ)|^{±1} ≤ e^γ l e^{c/l} ≤ e^γ (l + c + c²/l)` with `l = log x`, which is at most
`2 e^γ (log log q + 5)` in both ranges.
-/

namespace LLS

open Erdos985 Erdos985.Analytic
open Real (exp log eulerMascheroniConstant)

lemma final_exp {lg l c cm : ℝ} (hl : 11 ≤ l) (hcm0 : 0 ≤ cm) (hcml : cm ≤ l) (hc : c ≤ cm)
    (h : lg ≤ log l + eulerMascheroniConstant + c / l) :
    exp lg ≤ exp eulerMascheroniConstant * (l + cm + cm ^ 2 / l) := by
  have hl0 : 0 < l := by linarith
  have h1 : lg ≤ log l + eulerMascheroniConstant + cm / l := by
    have : c / l ≤ cm / l := div_le_div_of_nonneg_right hc hl0.le
    linarith
  have ht0 : 0 ≤ cm / l := div_nonneg hcm0 hl0.le
  have ht1 : cm / l ≤ 1 := by rw [div_le_one hl0]; exact hcml
  calc exp lg ≤ exp (log l + eulerMascheroniConstant + cm / l) := Real.exp_le_exp.2 h1
    _ = l * exp eulerMascheroniConstant * exp (cm / l) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hl0]
    _ ≤ l * exp eulerMascheroniConstant * (1 + cm / l + (cm / l) ^ 2) := by
        gcongr; exact exp_le_quad ht0 ht1
    _ = exp eulerMascheroniConstant * (l + cm + cm ^ 2 / l) := by field_simp

/-- The numerical bound for `c` (both directions). -/
lemma c_le {l x s Zb Nn G : ℝ} (hl : 11 ≤ l) (hx : 100000 ≤ x) (hxl : l ≤ x / 100)
    (hs : 316 ≤ s) (hss : s ^ 2 = x) (hZb : 0 ≤ Zb) {eE eG : ℝ} (hG : G ≤ eG)
    (heE : -3 ≤ eE) (heE' : eE ≤ 3) (k : ℝ) (hk0 : 0 ≤ k) (hk : k ≤ 1 / x + 1 / s)
    (hNn : Nn ≤ l - 1 + 1 / x + Zb * k + eE) :
    3 - l + Nn / (1 - 1 / x) + G + (Zb / s + 2 / x) / l
      ≤ 2.03 + eE + eG + 1.095 * (Zb / s) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < l := by linarith
  have hsx : 1 / x = (1 / s) * (1 / s) := by rw [← hss]; field_simp
  have hb : 1 / s ≤ 1 / 316 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hb0 : 0 < 1 / s := by positivity
  have ha1 : 1 / x ≤ 1 / 100000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have ha0 : 0 < 1 / x := by positivity
  have hr0 : 0 ≤ Zb / s := by positivity
  have hZk : Zb * k ≤ Zb / s * (1 + 1 / 316) := by
    have h1 : Zb * k ≤ Zb * (1 / x + 1 / s) := mul_le_mul_of_nonneg_left hk hZb
    have h2 : Zb * (1 / x + 1 / s) = Zb / s * (1 / s + 1) := by rw [hsx]; field_simp
    have h3 : Zb / s * (1 / s + 1) ≤ Zb / s * (1 + 1 / 316) :=
      mul_le_mul_of_nonneg_left (by linarith) hr0
    linarith
  have hla : l * (1 / x) ≤ 1 / 100 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have hden : 0 < 1 - 1 / x := by linarith
  have hNnub : Nn ≤ l - 1 + 1 / 100000 + eE + Zb / s * (1 + 1 / 316) := by linarith
  set B := l - 1 + 1 / 100000 + eE + Zb / s * (1 + 1 / 316) with hBdef
  have hB0 : 0 ≤ B := by simp only [B]; nlinarith
  have hBa : B * (1 / x) ≤ 0.0101 + 0.0000101 * (Zb / s) := by
    have e1 : (1 / x) * eE ≤ (1 / 100000) * 3 := by nlinarith
    have e2 : (1 / x) * (Zb / s * (1 + 1 / 316)) ≤ (1 / 100000) * (Zb / s * (1 + 1 / 316)) :=
      mul_le_mul_of_nonneg_right ha1 (by positivity)
    have e3 : (1 / x) * (1 / 100000) ≤ 1 / 100000 * (1 / 100000) :=
      mul_le_mul_of_nonneg_right ha1 (by norm_num)
    simp only [B]; nlinarith
  have hdiv : Nn / (1 - 1 / x) ≤ B + (0.0201 + 0.00002 * (Zb / s)) := by
    rw [div_le_iff₀ hden]
    have : (0.0201 + 0.00002 * (Zb / s)) * (1 / x) ≤ (0.0201 + 0.00002 * (Zb / s)) * (1 / 100000) :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    nlinarith
  have hlast : (Zb / s + 2 / x) / l ≤ Zb / s / 11 + 2 / 1100000 := by
    rw [div_le_iff₀ hl0]
    have h1 : Zb / s ≤ Zb / s / 11 * l := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; nlinarith
    have h2 : 2 / x ≤ 2 / 1100000 * l := by
      have : 2 / x = 2 * (1 / x) := by ring
      nlinarith
    linarith
  rw [hBdef] at hdiv
  linarith

/-! ### Numerical facts -/

lemma log_1e5_bounds : 11.51 ≤ Real.log (100000 : ℕ) ∧ Real.log (100000 : ℕ) ≤ 11.53 := by
  have h1 := log_ge_of_pow 100000 1063 64 (by norm_num) (by decide +kernel)
  have h2 := log_le_of_pow 100000 1064 64 (by norm_num) (by norm_num) (by decide +kernel)
  constructor
  · calc (11.51 : ℝ) ≤ ((1063 : ℕ) : ℝ) / ((64 : ℕ) : ℝ) * 0.6931471803 := by norm_num
      _ ≤ _ := h1
  · calc Real.log (100000 : ℕ) ≤ ((1064 : ℕ) : ℝ) / ((64 : ℕ) : ℝ) * 0.6931471808 := h2
      _ ≤ 11.53 := by norm_num

lemma log_ge_of_ge {y : ℝ} {n k : ℕ} (hn : (n : ℝ) ≤ y) (hn0 : 0 < n) (hk : 2 ^ k ≤ n ^ 64) :
    (k : ℝ) / 64 * 0.6931471803 ≤ Real.log y :=
  (log_ge_of_pow n k 64 (by norm_num) hk).trans (Real.log_le_log (by exact_mod_cast hn0) hn)

/-- `-EshiftLo x ≤ 1.7197` and `-(γ-part at 1) ≤ 1.7197`, `G1hi ≤ -0.856`. -/
lemma gamma_consts (x : ℝ) (hx : 100000 ≤ x) :
    -EshiftLo x ≤ 1.7197 ∧
      (1 / 2) * Real.log Real.pi + eulerMascheroniConstant / 2 + Real.log 2 ≤ 1.7197 ∧
      -(1 / 2) * Real.log Real.pi - eulerMascheroniConstant / 2 ≤ -0.856 := by
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_lt_d9
  have hpi4 : Real.log Real.pi ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log Real.pi_pos (by have := Real.pi_lt_d2; norm_num; linarith)
  have hx0 : 0 < x := by linarith
  have h1x : 1 / x ≤ 1 / 100000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h1x0 : 0 ≤ 1 / x := by positivity
  refine ⟨?_, by linarith, by linarith⟩
  unfold EshiftLo
  have : 0 ≤ (1 / x) * Real.log Real.pi := mul_nonneg h1x0 (by linarith)
  nlinarith

lemma regimeA_num {lq l cm : ℝ} (h23 : 23 ≤ lq) (hlq : lq ≤ 316.3) (hl1 : 11.51 ≤ l)
    (hl2 : l ≤ 11.53) (hcm : cm ≤ 2.91 + 1.095 * ((lq + 23.06) / 314.2)) (hcm0 : 0 ≤ cm) :
    l + cm + cm ^ 2 / l ≤ 2 * (Real.log lq + 5) := by
  have hl0 : 0 < l := by linarith
  have hcm1 : cm ≤ 4.1 := by
    have : (lq + 23.06) / 314.2 ≤ (316.3 + 23.06) / 314.2 := by gcongr
    norm_num at this hcm ⊢; linarith
  have hsq : cm ^ 2 / l ≤ cm ^ 2 / 11.51 := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hl1
  rcases le_or_gt lq 100 with h | h
  · have hlog := log_ge_of_ge (n := 23) (k := 289) (by exact_mod_cast h23) (by norm_num)
      (by decide +kernel)
    have hcm2 : cm ≤ 3.34 := by
      have : (lq + 23.06) / 314.2 ≤ (100 + 23.06) / 314.2 := by gcongr
      norm_num at this hcm ⊢; linarith
    have : cm ^ 2 ≤ 3.34 ^ 2 := by nlinarith
    have h3 : cm ^ 2 / 11.51 ≤ 3.34 ^ 2 / 11.51 := by gcongr
    have hlog' : (289 : ℝ) / 64 * 0.6931471803 ≤ Real.log lq := by exact_mod_cast hlog
    have h4 := hsq.trans h3
    norm_num at h4 hlog' ⊢
    linarith
  · have hlog := log_ge_of_ge (n := 100) (k := 425) (by exact_mod_cast h.le) (by norm_num)
      (by decide +kernel)
    have : cm ^ 2 ≤ 4.1 ^ 2 := by nlinarith
    have h3 : cm ^ 2 / 11.51 ≤ 4.1 ^ 2 / 11.51 := by gcongr
    have hlog' : (425 : ℝ) / 64 * 0.6931471803 ≤ Real.log lq := by exact_mod_cast hlog
    have h4 := hsq.trans h3
    norm_num at h4 hlog' ⊢
    linarith

lemma Eshift_le (x : ℝ) (hx : 100000 ≤ x) (hl : Real.log x ≤ x / 100 - 2) : Eshift x ≤ -0.846 := by
  unfold Eshift
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hx0 : 0 < x := by linarith
  have h1x : 1 / x ≤ 1 / 100000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h1x0 : 0 ≤ 1 / x := by positivity
  have hlx : (Real.log x + 2) / x ≤ 0.01 := by rw [div_le_iff₀ hx0]; linarith
  set a := 1 - 1 / x
  have ha : 0.99999 ≤ a := by simp only [a]; linarith
  have h3 : 1.1364 * a ≤ Real.log Real.pi * a := mul_le_mul_of_nonneg_right hpi.le (by linarith)
  have h4 : 0.57688 * a ≤ eulerMascheroniConstant * a :=
    mul_le_mul_of_nonneg_right hγ.le (by linarith)
  have e : -(1 / 2) * a * Real.log Real.pi - eulerMascheroniConstant / 2 * a
      = -(1 / 2) * (Real.log Real.pi * a) - (eulerMascheroniConstant * a) / 2 := by ring
  rw [e]
  linarith

lemma log_le_div_hundred {x : ℝ} (hx : 100000 ≤ x) : Real.log x ≤ x / 100 - 2 := by
  have hx0 : 0 < x := by linarith
  have hs : 316 ≤ √x := by
    rw [show (316 : ℝ) = √(316 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hss : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have h1 : Real.log x = 2 * Real.log √x := by
    conv_lhs => rw [← hss]
    rw [Real.log_pow]; norm_num
  have h2 := Real.log_le_sub_one_of_pos (show 0 < √x by linarith)
  nlinarith

/-- The choice of `x` and the bound `Zb` for the zero sum, with the numerical conclusion. -/
lemma setup (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q] (hq : (10 : ℝ) ^ 10 ≤ q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ x : ℕ, 100000 ≤ x ∧ ∃ Zb : ℝ, Z2 χ ≤ Zb ∧ 0 ≤ Zb ∧
      let cm := 2.91 + 1.095 * (Zb / √(x : ℝ))
      cm ≤ 4.11 ∧ Real.log x + cm + cm ^ 2 / Real.log x ≤ 2 * (Real.log (Real.log q) + 5) := by
  have hq0 : (0 : ℝ) < q := by linarith [show (0 : ℝ) < 10 ^ 10 by norm_num]
  set lq := Real.log q with hlqdef
  have hlq : 23 ≤ lq := by
    rw [hlqdef, Real.le_log_iff_exp_le hq0]
    have := Real.exp_one_lt_d9
    calc Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 23 := by gcongr
      _ ≤ 10 ^ 10 := by norm_num
      _ ≤ q := hq
  -- the zero-sum bound, for any admissible `x`
  have hZgen : ∀ x : ℕ, 100000 ≤ x →
      Z2 χ ≤ (lq + 2 * Real.log x) / (1 - 2 / √(x : ℝ)) := by
    intro x hx
    have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
    have h := Z2_le_general hGRH hprim hχ x (by omega)
    have hP := vonMangoldt_ces_le x (by omega)
    have hE := Eshift_le x hxR (log_le_div_hundred hxR)
    have hs : 316 ≤ √(x : ℝ) := by
      rw [show (316 : ℝ) = √(316 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2s : 2 / √(x : ℝ) ≤ 2 / 316 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have hden : 0 < 1 - 2 / √(x : ℝ) := by linarith
    have h1x : 0 ≤ 1 / (x : ℝ) := by positivity
    have h1x' : 1 / (x : ℝ) ≤ 1 / 100000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hxR
    have hZ0 := Z2_nonneg χ
    have hlq0 : 0 ≤ lq := by linarith
    rw [le_div_iff₀ hden]
    have : Z2 χ * (1 - 2 / √(x : ℝ)) ≤ Z2 χ * (1 + 1 / x - 2 / √(x : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hZ0
    have hP2 : P2sum x ≤ Real.log x - 1 + 1 / x := hP
    have : lq * (1 - 1 / x) ≤ lq := by nlinarith
    rw [← hlqdef] at h
    linarith
  rcases lt_or_ge (lq ^ 2) 100000 with hA | hB
  · -- `x = 10^5`
    refine ⟨100000, le_rfl, _, hZgen 100000 le_rfl, ?_⟩
    obtain ⟨hl1, hl2⟩ := log_1e5_bounds
    have hs1 : (316.2 : ℝ) ≤ √((100000 : ℕ) : ℝ) := by
      rw [show (316.2 : ℝ) = √(316.2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hlqA : lq ≤ 316.3 := by nlinarith
    set s := √((100000 : ℕ) : ℝ)
    set l := Real.log ((100000 : ℕ) : ℝ)
    have hden : 0 < 1 - 2 / s := by
      have : 2 / s ≤ 2 / 316.2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1
      linarith
    have hZb0 : 0 ≤ (lq + 2 * l) / (1 - 2 / s) := div_nonneg (by linarith) hden.le
    have hr : (lq + 2 * l) / (1 - 2 / s) / s ≤ (lq + 23.06) / 314.2 := by
      have hsne : s ≠ 0 := by linarith
      have e : (lq + 2 * l) / (1 - 2 / s) / s = (lq + 2 * l) / (s - 2) := by
        rw [div_div]; congr 1; field_simp
      rw [e, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have hlog : Real.log lq = Real.log (Real.log q) := rfl
    refine ⟨hZb0, ?_⟩
    intro cm
    have hcm : cm ≤ 2.91 + 1.095 * ((lq + 23.06) / 314.2) := by
      simp only [cm]; nlinarith
    have hcm0 : 0 ≤ cm := by simp only [cm]; positivity
    refine ⟨?_, ?_⟩
    · have : (lq + 23.06) / 314.2 ≤ (316.3 + 23.06) / 314.2 := by gcongr
      norm_num at this hcm ⊢; linarith
    · rw [← hlog]; exact regimeA_num hlq hlqA hl1 hl2 hcm hcm0
  · -- `x = ⌊log² q⌋`
    have hlq316 : 316 ≤ lq := by nlinarith
    set x := ⌊lq ^ 2⌋₊ with hxdef
    have hx1 : (x : ℝ) ≤ lq ^ 2 := Nat.floor_le (by positivity)
    have hx2 : lq ^ 2 < x + 1 := Nat.lt_floor_add_one _
    have hx : 100000 ≤ x := Nat.le_floor (by exact_mod_cast hB)
    have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
    refine ⟨x, hx, _, hZgen x hx, ?_⟩
    set s := √(x : ℝ)
    set l := Real.log (x : ℝ)
    have hss : s ^ 2 = x := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : lq - 1 ≤ s := by nlinarith
    have hl1 : 11.51 ≤ l := (log_1e5_bounds.1).trans (Real.log_le_log (by norm_num) (by exact_mod_cast hx))
    have hl2 : l ≤ 2 * Real.log lq := by
      have := Real.log_le_log (by positivity) hx1
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hloglq : Real.log lq ≤ lq / 50 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < lq / 316 by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at h
      have h316 : Real.log 316 ≤ 5.8 := by
        have := log_le_of_pow 316 532 64 (by norm_num) (by norm_num) (by decide +kernel)
        have h' : Real.log (316 : ℝ) ≤ (532 : ℝ) / 64 * 0.6931471808 := by exact_mod_cast this
        linarith
      nlinarith
    have hden : 0 < 1 - 2 / s := by
      have : 2 / s ≤ 2 / 315 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith
    have hZb0 : 0 ≤ (lq + 2 * l) / (1 - 2 / s) := div_nonneg (by linarith) hden.le
    have hr : (lq + 2 * l) / (1 - 2 / s) / s ≤ 1.091 := by
      have hsne : s ≠ 0 := by linarith
      have e : (lq + 2 * l) / (1 - 2 / s) / s = (lq + 2 * l) / (s - 2) := by
        rw [div_div]; congr 1; field_simp
      rw [e, div_le_iff₀ (by linarith)]
      nlinarith
    refine ⟨hZb0, ?_⟩
    intro cm
    have hcm : cm ≤ 4.11 := by simp only [cm]; nlinarith
    have hcm0 : 0 ≤ cm := by simp only [cm]; positivity
    refine ⟨hcm, ?_⟩
    have hl0 : 0 < l := by linarith
    have : cm ^ 2 / l ≤ 4.11 ^ 2 / 11.51 := by
      apply div_le_div₀ (by norm_num) (by nlinarith) (by norm_num) hl1
    have hlog : Real.log lq = Real.log (Real.log q) := rfl
    rw [← hlog]
    nlinarith

lemma chi_ne_one {q : ℕ} [NeZero q] (hq : (10 : ℝ) ^ 10 ≤ q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  have h := hprim
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at h
  have : (q : ℝ) = 1 := by exact_mod_cast h.symm
  linarith [show (1 : ℝ) < 10 ^ 10 by norm_num]

/-- **Upper bound of LLS Theorem 1.5's shape, under GRH**, with additive constant `5`. -/
theorem l1UpperBoundWith_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : L1UpperBoundWith 5 := by
  intro q _ hq χ hprim
  have hχ := chi_ne_one hq hprim
  obtain ⟨x, hx, Zb, hZb, hZb0, hcm4, hfin⟩ := setup hGRH hq hprim hχ
  have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
  have hl1 : 11.51 ≤ Real.log x :=
    (log_1e5_bounds.1).trans (Real.log_le_log (by norm_num) (by exact_mod_cast hx))
  have hs : 316 ≤ √(x : ℝ) := by
    rw [show (316 : ℝ) = √(316 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hss : √(x : ℝ) ^ 2 = x := Real.sq_sqrt (by positivity)
  obtain ⟨hE, -, hG⟩ := gamma_consts x hxR
  have hxl : Real.log x ≤ x / 100 := by linarith [log_le_div_hundred hxR]
  have hc := c_le (eE := 1.7197) (by linarith) hxR hxl hs hss hZb0 hG (by norm_num) (by norm_num)
    (1 / x + 1 / √(x : ℝ)) (by positivity) le_rfl
    (Nn := Real.log x - 1 + 1 / x + Zb * (1 / x + 1 / √(x : ℝ)) - EshiftLo x) (by linarith)
  have hlg := log_norm_L1_le_c hGRH hprim hχ x hx Zb hZb
  have hL0 : 0 < ‖DirichletCharacter.LFunction χ 1‖ := norm_pos_iff.2
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  have key := final_exp (lg := Real.log ‖DirichletCharacter.LFunction χ 1‖)
    (cm := 2.91 + 1.095 * (Zb / √(x : ℝ))) (by linarith)
    (by positivity) (by linarith) (le_trans hc (by linarith)) hlg
  rw [Real.exp_log hL0] at key
  calc ‖DirichletCharacter.LFunction χ 1‖ ≤ _ := key
    _ ≤ exp eulerMascheroniConstant * (2 * (Real.log (Real.log q) + 5)) :=
        mul_le_mul_of_nonneg_left hfin (Real.exp_pos _).le
    _ = _ := by ring

/-- **Lower bound of LLS Theorem 1.5's shape, under GRH**, with leading constant `2e^γ` and
additive constant `5`. -/
theorem l1LowerBoundWith_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : L1LowerBoundWith 5 := by
  intro q _ hq χ hprim
  have hχ := chi_ne_one hq hprim
  obtain ⟨x, hx, Zb, hZb, hZb0, hcm4, hfin⟩ := setup hGRH hq hprim hχ
  have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
  have hl1 : 11.51 ≤ Real.log x :=
    (log_1e5_bounds.1).trans (Real.log_le_log (by norm_num) (by exact_mod_cast hx))
  have hs : 316 ≤ √(x : ℝ) := by
    rw [show (316 : ℝ) = √(316 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hss : √(x : ℝ) ^ 2 = x := Real.sq_sqrt (by positivity)
  obtain ⟨-, hG, -⟩ := gamma_consts x hxR
  have hxl : Real.log x ≤ x / 100 := by linarith [log_le_div_hundred hxR]
  have hE := Eshift_le x hxR (log_le_div_hundred hxR)
  have hk0 : 0 ≤ 1 / √(x : ℝ) - 1 / x := by
    have hsx : √(x : ℝ) ≤ x := by nlinarith
    have : 1 / (x : ℝ) ≤ 1 / √(x : ℝ) := one_div_le_one_div_of_le (by linarith) hsx
    linarith
  have hk : 1 / √(x : ℝ) - 1 / x ≤ 1 / x + 1 / √(x : ℝ) := by
    have : 0 ≤ 1 / (x : ℝ) := by positivity
    linarith
  have hc := c_le (eE := -0.846) (by linarith) hxR hxl hs hss hZb0 hG (by norm_num) (by norm_num)
    (1 / √(x : ℝ) - 1 / x) hk0 hk
    (Nn := Real.log x - 1 + 1 / x + Zb * (1 / √(x : ℝ) - 1 / x) + Eshift x) (by linarith)
  have hlg := neg_log_norm_L1_le_c hGRH hprim hχ x hx Zb hZb
  have hL0 : 0 < ‖DirichletCharacter.LFunction χ 1‖ := norm_pos_iff.2
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  have key := final_exp (lg := -Real.log ‖DirichletCharacter.LFunction χ 1‖)
    (cm := 2.91 + 1.095 * (Zb / √(x : ℝ))) (by linarith)
    (by positivity) (by linarith) (le_trans hc (by linarith)) hlg
  rw [Real.exp_neg, Real.exp_log hL0] at key
  rw [one_div]
  calc (‖DirichletCharacter.LFunction χ 1‖)⁻¹ ≤ _ := key
    _ ≤ exp eulerMascheroniConstant * (2 * (Real.log (Real.log q) + 5)) :=
        mul_le_mul_of_nonneg_left hfin (Real.exp_pos _).le
    _ = _ := by ring

end LLS
