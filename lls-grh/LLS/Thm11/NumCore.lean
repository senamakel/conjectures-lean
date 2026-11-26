import LLS.Thm11.Elim
import LLS.Numerics.Interval
import LLS.Sharp.NumBasic

/-!
# The one-variable bounds `F₁`, `F₂(·, 8)`, `F₂(·, M)` on a box

With `s = √x`, `l = log x`, `δ = K − s` and `ε = κ − s`,

* `ε = (3s + 1)/(s − 1) + l s/(s − 1)`, `δ = s(s(3 + l/2) − 1)/(s − 1)²`;
* `F₁ = s (W − 0.15 − ε) + δ W + V` with `W = l − 2E(x) + 2(Pc − l) + 6.2 − 2ρ − log 2 (1 + 1/x)`,
  `ρ = log ν − l/2` (`LLS.Thm11.F1_eq`);

so the cancellation `x − κν` is exact and every remaining term moves little on a box
`x ∈ [X_a, X_b]`. `LLS.Thm11.F1_ge` bounds `F₁` below by `F1Lo`, a rational expression in the
box data; similarly `F2a_ge`, `F2b_ge` and `R5_of`.
-/

set_option exponentiation.threshold 1024

namespace LLS.Thm11

open Real

/-! ### Constants -/

lemma log3_gt : (405 : ℝ) / 256 * 0.6931471803 ≤ Real.log 3 := by
  have := log_ge_of_pow 3 405 256 (by norm_num) (by norm_num)
  simpa using this

lemma log5_gt : (594 : ℝ) / 256 * 0.6931471803 ≤ Real.log 5 := by
  have := log_ge_of_pow 5 594 256 (by norm_num) (by norm_num)
  simpa using this

lemma log8_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num

/-- `min (a q) (b q) ≤ s Q` for `s ∈ [a, b]`, `s ≥ 0`, `q ≤ Q`. -/
lemma mul_lo {a b s q Q : ℝ} (ha : a ≤ s) (hb : s ≤ b) (hs : 0 ≤ s) (hq : q ≤ Q) :
    min (a * q) (b * q) ≤ s * Q := by
  have h1 : s * q ≤ s * Q := mul_le_mul_of_nonneg_left hq hs
  rcases le_total 0 q with h | h
  · exact (min_le_left _ _).trans ((mul_le_mul_of_nonneg_right ha h).trans h1)
  · exact (min_le_right _ _).trans ((mul_le_mul_of_nonpos_right hb h).trans h1)

/-! ### The atoms -/

section Atoms

variable {x : ℕ}

lemma sq_sqrt_x (x : ℕ) : √(x : ℝ) ^ 2 = x := Real.sq_sqrt (Nat.cast_nonneg _)

lemma Kc_eq (hx : 64 ≤ x) :
    Kc x = √(x : ℝ) + √(x : ℝ) * (√(x : ℝ) * (3 + Real.log x / 2) - 1) / (√(x : ℝ) - 1) ^ 2 := by
  have hs := sqrt_ge_eight (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hsq := sq_sqrt_x x
  unfold Kc
  set l := Real.log x
  set s := √(x : ℝ)
  have hs1 : s - 1 ≠ 0 := by linarith
  have hs0 : s ≠ 0 := by linarith
  rw [← hsq]
  have hden : 1 + 1 / s ^ 2 - 2 / s = (s - 1) ^ 2 / s ^ 2 := by field_simp; ring
  rw [hden]
  field_simp
  ring

lemma kap_eq (hx : 64 ≤ x) :
    kap x = √(x : ℝ) + ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1)
      + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1)) := by
  have hs := sqrt_ge_eight (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hsq := sq_sqrt_x x
  have hK := Kc_eq hx
  unfold kap
  rw [hK]
  set l := Real.log x
  set s := √(x : ℝ)
  have hs1 : s - 1 ≠ 0 := by linarith
  have hs0 : s ≠ 0 := by linarith
  rw [← hsq]
  field_simp
  ring

end Atoms

/-! ### `F₁` -/

lemma F1_eq (x : ℕ) (hx : 64 ≤ x) :
    F1 x = √(x : ℝ) * (((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
          - 2 * (Real.log x + 2) / x + 2 * (PcF x - Real.log x) + 6.05
          - 2 * (Real.log (nu x) - Real.log x / 2) - Real.log 2 * (1 + 1 / (x : ℝ)))
        - ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x / (√(x : ℝ) - 1)))
      + (Kc x - √(x : ℝ)) * (Real.log x + ((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
          - 2 * (Real.log x + 2) / x + 2 * (PcF x - Real.log x) + 6.2
          - 2 * (Real.log (nu x) - Real.log x / 2) - Real.log 2 * (1 + 1 / (x : ℝ))))
      + (-3 * Real.log x - 3.5 + 1 / 2 * Real.log π * Real.log x
          - (π ^ 2 / 6 - eulerMascheroniConstant / 2 * Real.log x)
          - ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1))
            / (2 * √(x : ℝ))
          - (Real.log x - Real.log 2 / 2) ^ 2 / 2 + Real.log 2 * Real.log x / 2
          - (Real.log x - Real.log 3 / 2) ^ 2 / 2) := by
  have hs := sqrt_ge_eight (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hsq := sq_sqrt_x x
  have hk := kap_eq hx
  unfold F1 base0 RC nu Eshift Etil
  rw [hk]
  set l := Real.log x
  set P := PcF x
  set K := Kc x
  set s := √(x : ℝ)
  set lν := Real.log (s + 1 / (2 * s))
  have hs1 : s - 1 ≠ 0 := by linarith
  have hs0 : s ≠ 0 := by linarith
  rw [← hsq]
  field_simp
  ring

/-! ### Shared box facts -/

/-- Data of a box: `X_a ≤ x`, `s_a ≤ √x ≤ s_b`, `l_a ≤ log x ≤ l_b`. -/
structure InBox (x : ℕ) (Xa sa sb la lb : ℝ) : Prop where
  hXa : Xa ≤ x
  hXa64 : 64 ≤ Xa
  hsa8 : 8 ≤ sa
  hsa : sa ≤ √(x : ℝ)
  hsb : √(x : ℝ) ≤ sb
  hla : la ≤ Real.log x
  hlb : Real.log x ≤ lb
  hla4 : 4 ≤ la

lemma ratio_anti {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : b ^ 2 / (b - 1) ^ 2 ≤ a ^ 2 / (a - 1) ^ 2 := by
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ b - a) (by nlinarith : 0 ≤ a * b - a - b)]

lemma frac_anti {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : b / (b - 1) ^ 2 ≤ a / (a - 1) ^ 2 := by
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ b - a) (by nlinarith : 0 ≤ a * b - 1)]

section BoxFacts

variable {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
include B

lemma InBox.x64 : 64 ≤ x := by have := B.hXa64.trans B.hXa; exact_mod_cast this

lemma InBox.inv_le : 1 / (x : ℝ) ≤ 1 / Xa :=
  one_div_le_one_div_of_le (by linarith [B.hXa64]) B.hXa

lemma InBox.one_sub_ge : 1 - 1 / Xa ≤ 1 - 1 / (x : ℝ) := by linarith [B.inv_le]

lemma InBox.one_sub_nonneg : 0 ≤ 1 - 1 / Xa := by
  have : 1 / Xa ≤ 1 := by rw [div_le_one (by linarith [B.hXa64])]; linarith [B.hXa64]
  linarith

lemma InBox.mE_ge :
    (1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa
      ≤ (1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
        - 2 * (Real.log x + 2) / x := by
  have hpi := Erdos985.Analytic.PrincipalAux.log_pi_gt'
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hX0 : 0 < Xa := by linarith [B.hXa64]
  have hx0 : (0 : ℝ) < x := by linarith [B.hXa64, B.hXa]
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have h1 : (1 - 1 / Xa) * (1.144 + 0.57688)
      ≤ (1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant) :=
    mul_le_mul B.one_sub_ge (by linarith) (by norm_num) (by linarith [B.one_sub_nonneg, B.one_sub_ge])
  have h2 : 2 * (Real.log x + 2) / x ≤ 2 * (lb + 2) / Xa :=
    div_le_div₀ (by linarith [B.hlb]) (by linarith [B.hlb]) hX0 B.hXa
  linarith

lemma InBox.rho_le : 2 * (Real.log (nu x) - Real.log x / 2) ≤ 1 / Xa := by
  have hx0 : (0 : ℝ) < x := by linarith [B.hXa64, B.hXa]
  have hs0 : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  have hsq := sq_sqrt_x x
  have hls : Real.log x / 2 = Real.log √(x : ℝ) := by rw [Real.log_sqrt hx0.le]
  have hν0 : 0 < nu x := by unfold nu; positivity
  have h := Real.log_le_sub_one_of_pos (show 0 < nu x / √(x : ℝ) by positivity)
  rw [Real.log_div hν0.ne' hs0.ne'] at h
  have e : nu x / √(x : ℝ) - 1 = 1 / (2 * x) := by
    unfold nu
    rw [← hsq]
    field_simp
    ring_nf
    rw [Real.sq_sqrt hx0.le, Real.sq_sqrt (by positivity)]
  rw [hls]
  have : 1 / (2 * (x : ℝ)) ≤ 1 / (2 * Xa) :=
    one_div_le_one_div_of_le (by linarith [B.hXa64]) (by linarith [B.hXa])
  have e2 : 2 * (1 / (2 * Xa)) = 1 / Xa := by field_simp
  linarith

lemma InBox.log2_le : Real.log 2 * (1 + 1 / (x : ℝ)) ≤ 0.6931471808 * (1 + 1 / Xa) := by
  have := Real.log_two_lt_d9
  have h0 : 0 ≤ 1 / (x : ℝ) := by
    have : (0 : ℝ) ≤ x := Nat.cast_nonneg _
    positivity
  exact mul_le_mul this.le (by linarith [B.inv_le]) (by positivity)
    (by norm_num)

lemma InBox.frac_le : (3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) ≤ 3 + 4 / (sa - 1) := by
  have hs := B.hsa
  have hs8 := B.hsa8
  have hs1 : √(x : ℝ) - 1 ≠ 0 := by linarith
  have e : (3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) = 3 + 4 / (√(x : ℝ) - 1) := by
    field_simp; ring
  rw [e]
  have : 4 / (√(x : ℝ) - 1) ≤ 4 / (sa - 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  linarith

lemma InBox.lfrac_le : Real.log x / (√(x : ℝ) - 1) ≤ lb / (sa - 1) := by
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  exact div_le_div₀ (by linarith [B.hlb]) B.hlb (by linarith [B.hsa8]) (by linarith [B.hsa])

lemma InBox.delta_eq :
    Kc x - √(x : ℝ) = (3 + Real.log x / 2) * (√(x : ℝ) ^ 2 / (√(x : ℝ) - 1) ^ 2)
      - √(x : ℝ) / (√(x : ℝ) - 1) ^ 2 := by
  rw [Kc_eq B.x64]
  have : √(x : ℝ) - 1 ≠ 0 := by linarith [B.hsa, B.hsa8]
  field_simp; ring

lemma InBox.delta_ge :
    (3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2 ≤ Kc x - √(x : ℝ) := by
  rw [B.delta_eq]
  have hs := B.hsa; have hs8 := B.hsa8; have hsb := B.hsb
  have h1 := ratio_anti (by linarith) hsb
  have h2 := frac_anti (by linarith) hs
  have hla := B.hla
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have h0 : 0 ≤ sb ^ 2 / (sb - 1) ^ 2 := by positivity
  have := mul_le_mul (by linarith : 3 + la / 2 ≤ 3 + Real.log x / 2) h1 h0 (by linarith)
  linarith

lemma InBox.delta_le : Kc x - √(x : ℝ) ≤ (3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2) := by
  rw [B.delta_eq]
  have hs := B.hsa; have hs8 := B.hsa8
  have h1 := ratio_anti (by linarith) hs
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have h0 : 0 ≤ √(x : ℝ) / (√(x : ℝ) - 1) ^ 2 := by
    have : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
    positivity
  have := mul_le_mul (by linarith [B.hlb] : 3 + Real.log x / 2 ≤ 3 + lb / 2) h1
    (by positivity) (by linarith [B.hlb])
  linarith

lemma InBox.delta_nonneg : 0 ≤ Kc x - √(x : ℝ) := by
  have hden := den_pos (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have hs : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
  have hx64 : (64 : ℝ) ≤ x := by linarith [B.hXa64, B.hXa]
  have hsx : √(x : ℝ) ≤ x := by
    have := Real.sqrt_le_sqrt (show (x : ℝ) ≤ x ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have hsx1 : √(x : ℝ) * (1 / (x : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]; exact hsx
  have : √(x : ℝ) ≤ Kc x := by
    unfold Kc
    rw [le_div_iff₀ (by linarith)]
    have : 0 ≤ √(x : ℝ) * (2 / √(x : ℝ)) := by positivity
    have e : √(x : ℝ) * (1 + 1 / (x : ℝ) - 2 / √(x : ℝ))
        = √(x : ℝ) + √(x : ℝ) * (1 / (x : ℝ)) - √(x : ℝ) * (2 / √(x : ℝ)) := by ring
    rw [e]
    linarith
  linarith

lemma InBox.eps_le :
    ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1))
        / (2 * √(x : ℝ)) ≤ (4 + lb) / (2 * (sa - 1)) := by
  have hs := B.hsa; have hs8 := B.hsa8
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have hs1 : 0 < √(x : ℝ) - 1 := by linarith
  have hs0 : √(x : ℝ) ≠ 0 := by linarith
  have hs0' : 0 < √(x : ℝ) := by linarith
  have hs1' : √(x : ℝ) - 1 ≠ 0 := by linarith
  have e : ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1))
        / (2 * √(x : ℝ))
      = (3 * √(x : ℝ) + 1) / (2 * √(x : ℝ) * (√(x : ℝ) - 1)) + Real.log x / (2 * (√(x : ℝ) - 1)) := by
    field_simp
  rw [e]
  have h1 : (3 * √(x : ℝ) + 1) / (2 * √(x : ℝ) * (√(x : ℝ) - 1)) ≤ 4 / (2 * (√(x : ℝ) - 1)) := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos two_pos hs0') hs1) (by positivity)]
    nlinarith
  have h2 : (4 + Real.log x) / (2 * (√(x : ℝ) - 1)) ≤ (4 + lb) / (2 * (sa - 1)) :=
    div_le_div₀ (by linarith [B.hlb]) (by linarith [B.hlb]) (by linarith) (by linarith)
  have e2 : 4 / (2 * (√(x : ℝ) - 1)) + Real.log x / (2 * (√(x : ℝ) - 1))
      = (4 + Real.log x) / (2 * (√(x : ℝ) - 1)) := by field_simp
  linarith

lemma InBox.V_ge :
    (-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * lb - 3.5 - 3.1416 ^ 2 / 6
        - (lb - 0.6931471803 / 2) ^ 2 / 2 - (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2
      ≤ -3 * Real.log x - 3.5 + 1 / 2 * Real.log π * Real.log x
          - (π ^ 2 / 6 - eulerMascheroniConstant / 2 * Real.log x)
          - (Real.log x - Real.log 2 / 2) ^ 2 / 2 + Real.log 2 * Real.log x / 2
          - (Real.log x - Real.log 3 / 2) ^ 2 / 2 := by
  have hpi := Erdos985.Analytic.PrincipalAux.log_pi_gt'
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h3 := log3_gt
  have h3' : Real.log 3 < 1.104 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / Real.exp 1 by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
    have := Real.exp_one_gt_d9
    have : 3 / Real.exp 1 < 1.1037 := by rw [div_lt_iff₀ (Real.exp_pos 1)]; nlinarith
    linarith
  have hl4 := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have hlb := B.hlb
  set l := Real.log x
  have ec : -3 * l + 1 / 2 * Real.log π * l + eulerMascheroniConstant / 2 * l + Real.log 2 * l / 2
      ≥ (-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * lb := by
    have : (-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * lb
        ≤ (-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * l :=
      mul_le_mul_of_nonpos_left hlb (by norm_num)
    nlinarith
  have e1 : (l - Real.log 2 / 2) ^ 2 ≤ (lb - 0.6931471803 / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have e2 : (l - Real.log 3 / 2) ^ 2 ≤ (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have e3 : π ^ 2 ≤ 3.1416 ^ 2 := by nlinarith
  linarith

end BoxFacts

/-! ### `F₁` on a box -/

/-- The lower bound for `F₁` on a box; `P0` is a lower bound for `Pc − log x`. -/
noncomputable def F1Lo (Xa sa sb la lb P0 : ℝ) : ℝ :=
  min (sa * ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa + 2 * P0 + 6.05 - 1 / Xa
        - 0.6931471808 * (1 + 1 / Xa) - (3 + 4 / (sa - 1)) - lb / (sa - 1)))
      (sb * ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa + 2 * P0 + 6.05 - 1 / Xa
        - 0.6931471808 * (1 + 1 / Xa) - (3 + 4 / (sa - 1)) - lb / (sa - 1)))
    + min (((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2)
          * (la + ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa) + 2 * P0 + 6.2 - 1 / Xa
            - 0.6931471808 * (1 + 1 / Xa)))
        ((3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2)
          * (la + ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa) + 2 * P0 + 6.2 - 1 / Xa
            - 0.6931471808 * (1 + 1 / Xa)))
    + ((-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * lb - 3.5 - 3.1416 ^ 2 / 6
        - (lb - 0.6931471803 / 2) ^ 2 / 2 - (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2
        - (4 + lb) / (2 * (sa - 1)))

theorem F1_ge {x : ℕ} {Xa sa sb la lb P0 : ℝ} (B : InBox x Xa sa sb la lb)
    (hP : P0 ≤ PcF x - Real.log x) : F1Lo Xa sa sb la lb P0 ≤ F1 x := by
  rw [F1_eq x B.x64]
  have hmE := B.mE_ge
  have hρ := B.rho_le
  have h2 := B.log2_le
  have hf := B.frac_le
  have hlf := B.lfrac_le
  have hV := B.V_ge
  have hε := B.eps_le
  have hs0 : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
  have hQ := mul_lo B.hsa B.hsb hs0 (q := (1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa
      + 2 * P0 + 6.05 - 1 / Xa - 0.6931471808 * (1 + 1 / Xa) - (3 + 4 / (sa - 1)) - lb / (sa - 1))
    (Q := (1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
          - 2 * (Real.log x + 2) / x + 2 * (PcF x - Real.log x) + 6.05
          - 2 * (Real.log (nu x) - Real.log x / 2) - Real.log 2 * (1 + 1 / (x : ℝ))
        - ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x / (√(x : ℝ) - 1))) (by linarith)
  have hW := mul_lo B.delta_ge B.delta_le B.delta_nonneg
    (q := la + ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa) + 2 * P0 + 6.2 - 1 / Xa
      - 0.6931471808 * (1 + 1 / Xa))
    (Q := Real.log x + ((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
          - 2 * (Real.log x + 2) / x + 2 * (PcF x - Real.log x) + 6.2
          - 2 * (Real.log (nu x) - Real.log x / 2) - Real.log 2 * (1 + 1 / (x : ℝ))))
    (by linarith [B.hla])
  unfold F1Lo
  linarith

/-! ### Box data -/

theorem inBox_of_data (x Xa Xb ka kb : ℕ) (sa sb : ℝ) (h1 : Xa ≤ x) (h2 : x ≤ Xb)
    (hka : 2 ^ ka ≤ Xa ^ 64) (hkb : Xb ^ 64 ≤ 2 ^ kb) (hsa0 : 0 ≤ sa) (hsa : sa ^ 2 ≤ Xa)
    (hsb0 : 0 ≤ sb) (hsb : (Xb : ℝ) ≤ sb ^ 2) (h64 : 64 ≤ Xa) (h8 : 8 ≤ sa)
    (h4 : (4 : ℝ) ≤ (ka : ℝ) / 64 * 0.6931471803) :
    InBox x Xa sa sb ((ka : ℝ) / 64 * 0.6931471803) ((kb : ℝ) / 64 * 0.6931471808) := by
  have hXa0 : 0 < Xa := by omega
  have hx0 : 0 < x := by omega
  have hXR : (Xa : ℝ) ≤ x := by exact_mod_cast h1
  have hXbR : (x : ℝ) ≤ Xb := by exact_mod_cast h2
  refine ⟨hXR, by exact_mod_cast h64, h8, ?_, ?_, ?_, ?_, h4⟩
  · exact Real.le_sqrt_of_sq_le (hsa.trans hXR)
  · rw [show sb = √(sb ^ 2) from (Real.sqrt_sq hsb0).symm]
    exact Real.sqrt_le_sqrt (hXbR.trans hsb)
  · exact (log_ge_of_pow Xa ka 64 (by norm_num) hka).trans
      (Real.log_le_log (by exact_mod_cast hXa0) hXR)
  · exact (Real.log_le_log (by exact_mod_cast hx0) hXbR).trans
      (log_le_of_pow Xb kb 64 (by norm_num) (by omega) hkb)

lemma PcF_sub_small {x : ℕ} (hx : x < 100) : -2 ≤ PcF x - Real.log x := by
  unfold PcF
  rw [if_neg (by have : (x : ℝ) < 100 := by exact_mod_cast hx
                 linarith)]
  linarith

lemma PcF_sub_big {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb) (h100 : 100 ≤ Xa) :
    -1 - 0.5774 - 0.25 / sa - 12 / Xa ≤ PcF x - Real.log x := by
  unfold PcF
  rw [if_pos (h100.trans B.hXa)]
  have hγ := Erdos985.Analytic.PrincipalAux.eulerMascheroniConstant_lt'
  have h1 : 0.25 / √(x : ℝ) ≤ 0.25 / sa :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith [B.hsa8]) B.hsa
  have h2 : 12 / (x : ℝ) ≤ 12 / Xa :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith [B.hXa64]) B.hXa
  linarith

/-! ### `F₂` -/

lemma muB_eq (x : ℕ) (hx : 64 ≤ x) :
    muB x = nu x * (1 - Real.log 2 / 2 / Real.log x) ^ 2 := by
  have hl4 := log_ge_four (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  unfold muB mC
  field_simp

lemma F2a_eq (x : ℕ) (hx : 64 ≤ x) :
    F2 x 8 = (√(x : ℝ) ^ 2 * (Real.log 2 / 2 / Real.log x) * (2 - Real.log 2 / 2 / Real.log x)
        - (1 + 1 / (4 * x)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2)
      + (-(3 / 20) * √(x : ℝ) - 3 * Real.log x - 3
        + Kc x * ((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant) - 2 * (Real.log x + 2) / x)
        + 1 / 2 * Real.log π * Real.log x - (π ^ 2 / 6 - eulerMascheroniConstant / 2 * Real.log x)
        - RC x + muB x * (11 + 2 * Real.log 8) - 8 * kap x) := by
  have hs := sqrt_ge_eight (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hsq := sq_sqrt_x x
  have hl4 := log_ge_four (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hμ := muB_eq x hx
  unfold F2 base0 Eshift Etil
  rw [hμ]
  unfold nu
  set l := Real.log x
  set K := Kc x
  set k := kap x
  set R := RC x
  set s := √(x : ℝ)
  have hs0 : s ≠ 0 := by linarith
  rw [← hsq]
  field_simp
  ring

lemma F2b_eq (x : ℕ) (hx : 64 ≤ x) :
    F2 x (nu x - 3 - 2 * Real.log 8)
      = √(x : ℝ) * ((((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
            - 2 * (Real.log x + 2) / x) - Real.log 2 * (1 + 1 / (x : ℝ)))
          - 3 / 20 + (3 + 2 * Real.log 8)
          - ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x / (√(x : ℝ) - 1))
          + nu x / √(x : ℝ) * (-(2 * (Real.log 2 / 2)) + (Real.log 2 / 2) ^ 2 / Real.log x)
          + 2 * (nu x / √(x : ℝ)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2
            * (Real.log (nu x - 3 - 2 * Real.log 8) - Real.log x / 2 - Real.log 8))
        + (Kc x - √(x : ℝ)) * (((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
            - 2 * (Real.log x + 2) / x) - Real.log 2 * (1 + 1 / (x : ℝ)))
        + (-3 * Real.log x - 3.5 + 1 / 2 * Real.log π * Real.log x
          - (π ^ 2 / 6 - eulerMascheroniConstant / 2 * Real.log x)
          - (Real.log x - Real.log 2 / 2) ^ 2 / 2 + Real.log 2 * Real.log x / 2
          - (Real.log x - Real.log 3 / 2) ^ 2 / 2
          - ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1))
            / (2 * √(x : ℝ))
          + (3 + 2 * Real.log 8)
            * ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1))
          + Real.log x / (2 * √(x : ℝ))) := by
  have hs := sqrt_ge_eight (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hsq := sq_sqrt_x x
  have hl4 := log_ge_four (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hμ := muB_eq x hx
  have hk := kap_eq hx
  unfold F2 base0 RC Eshift Etil
  rw [hμ, hk]
  unfold nu
  set l := Real.log x
  set K := Kc x
  set s := √(x : ℝ)
  set lM := Real.log (s + 1 / (2 * s) - 3 - 2 * Real.log 8)
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  rw [← hsq]
  field_simp
  ring

section BoxFacts2

variable {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
include B

lemma InBox.l4 : 4 ≤ Real.log x := log_ge_four (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)

lemma InBox.eta_ge : 0.6931471803 / 2 / lb ≤ Real.log 2 / 2 / Real.log x := by
  have := Real.log_two_gt_d9
  have := B.l4
  exact div_le_div₀ (by positivity) (by linarith) (by linarith) B.hlb

lemma InBox.eta_le : Real.log 2 / 2 / Real.log x ≤ 0.6931471808 / 2 / la := by
  have := Real.log_two_lt_d9
  have := Real.log_two_gt_d9
  have hla0 : 0 < la := by linarith [B.hla4]
  exact div_le_div₀ (by norm_num) (by linarith) hla0 B.hla

lemma InBox.eta_le_one : Real.log 2 / 2 / Real.log x ≤ 1 := by
  have := Real.log_two_lt_d9
  have := B.l4
  rw [div_le_one (by linarith)]; linarith

lemma InBox.eta_nonneg : 0 ≤ Real.log 2 / 2 / Real.log x := by
  have := Real.log_two_gt_d9
  have := B.l4
  positivity

lemma InBox.nus_eq : nu x / √(x : ℝ) = 1 + 1 / (2 * x) := by
  have hs := B.hsa; have hs8 := B.hsa8
  have hsq := sq_sqrt_x x
  have hs0 : √(x : ℝ) ≠ 0 := by linarith
  unfold nu
  rw [← hsq]
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

lemma InBox.nus_ge : 1 ≤ nu x / √(x : ℝ) := by
  rw [B.nus_eq]
  have : 0 ≤ 1 / (2 * (x : ℝ)) := by positivity
  linarith

lemma InBox.nus_le : nu x / √(x : ℝ) ≤ 1 + 1 / (2 * Xa) := by
  rw [B.nus_eq]
  have : 1 / (2 * (x : ℝ)) ≤ 1 / (2 * Xa) :=
    one_div_le_one_div_of_le (by linarith [B.hXa64]) (by linarith [B.hXa])
  linarith

lemma InBox.s_le_nu : √(x : ℝ) ≤ nu x := by
  have hs := B.hsa; have hs8 := B.hsa8
  unfold nu
  have : 0 < 1 / (2 * √(x : ℝ)) := div_pos one_pos (by linarith)
  linarith

lemma InBox.eps_le' :
    (3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1)
      ≤ 3 + 4 / (sa - 1) + lb * (sa / (sa - 1)) := by
  have hf := B.frac_le
  have hs := B.hsa; have hs8 := B.hsa8
  have hl := B.l4
  have h1 : √(x : ℝ) / (√(x : ℝ) - 1) ≤ sa / (sa - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have e : Real.log x * √(x : ℝ) / (√(x : ℝ) - 1) = Real.log x * (√(x : ℝ) / (√(x : ℝ) - 1)) := by
    ring
  rw [e]
  have h0 : 0 ≤ √(x : ℝ) / (√(x : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
  have := mul_le_mul B.hlb h1 h0 (by linarith [B.hlb])
  linarith

lemma InBox.eps_ge :
    3 + Real.log x ≤ (3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1) := by
  have hs := B.hsa; have hs8 := B.hsa8
  have hl := B.l4
  have h1 : 3 ≤ (3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : Real.log x ≤ Real.log x * √(x : ℝ) / (√(x : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  linarith

lemma InBox.K_ge : sa + ((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2) ≤ Kc x := by
  have := B.delta_ge; have := B.hsa; linarith

lemma InBox.K_le : Kc x ≤ sb + (3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2) := by
  have := B.delta_le; have := B.hsb; linarith

lemma InBox.K_ge' : sa + 1 + la / 2 ≤ Kc x := by
  have hden := den_pos (by linarith [B.hXa64, B.hXa] : (64 : ℝ) ≤ x)
  have hs := B.hsa
  have hs0 : 0 < √(x : ℝ) := by linarith [B.hsa8]
  have hl := B.l4
  have hd1 : 1 + 1 / (x : ℝ) - 2 / √(x : ℝ) ≤ 1 := by
    have hsx : √(x : ℝ) ≤ x := by
      have := Real.sqrt_le_sqrt (show (x : ℝ) ≤ x ^ 2 by nlinarith [B.hXa64, B.hXa])
      rwa [Real.sqrt_sq (by linarith [B.hXa64, B.hXa])] at this
    have : 1 / (x : ℝ) ≤ 2 / √(x : ℝ) := by
      rw [div_le_div_iff₀ (by linarith [B.hXa64, B.hXa]) hs0]; linarith
    linarith
  have : √(x : ℝ) + 1 + Real.log x / 2 ≤ Kc x := by
    unfold Kc
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  linarith [B.hla]

end BoxFacts2


section BoxFacts3

variable {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
include B

lemma InBox.A_ge (hη1' : 0.6931471808 / 2 / la ≤ 1) :
    sa ^ 2 * (0.6931471803 / 2 / lb) * (2 - 0.6931471808 / 2 / la) - (1 + 1 / (4 * Xa))
      ≤ √(x : ℝ) ^ 2 * (Real.log 2 / 2 / Real.log x) * (2 - Real.log 2 / 2 / Real.log x)
        - (1 + 1 / (4 * x)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2 := by
  have hηlo := B.eta_ge
  have hηhi := B.eta_le
  have hη0 := B.eta_nonneg
  have hη1 := B.eta_le_one
  have hs := B.hsa; have hs8 := B.hsa8
  have hA1 : sa ^ 2 * (0.6931471803 / 2 / lb) * (2 - 0.6931471808 / 2 / la)
      ≤ √(x : ℝ) ^ 2 * (Real.log 2 / 2 / Real.log x) * (2 - Real.log 2 / 2 / Real.log x) := by
    have e1 : sa ^ 2 ≤ √(x : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hs 2
    have e2 : 0 ≤ 0.6931471803 / 2 / lb := div_nonneg (by norm_num) (by linarith [B.hlb, B.l4])
    have := mul_le_mul e1 hηlo e2 (by positivity)
    exact mul_le_mul this (by linarith) (by linarith) (by positivity)
  have hA2 : (1 + 1 / (4 * (x : ℝ))) * (1 - Real.log 2 / 2 / Real.log x) ^ 2 ≤ 1 + 1 / (4 * Xa) := by
    have e1 : (1 - Real.log 2 / 2 / Real.log x) ^ 2 ≤ 1 := by nlinarith
    have e2 : 1 / (4 * (x : ℝ)) ≤ 1 / (4 * Xa) :=
      one_div_le_one_div_of_le (by linarith [B.hXa64]) (by linarith [B.hXa])
    have e3 : 0 ≤ 1 / (4 * (x : ℝ)) := by positivity
    calc (1 + 1 / (4 * (x : ℝ))) * (1 - Real.log 2 / 2 / Real.log x) ^ 2
        ≤ (1 + 1 / (4 * (x : ℝ))) * 1 := mul_le_mul_of_nonneg_left e1 (by linarith)
      _ ≤ 1 + 1 / (4 * Xa) := by linarith
  linarith

lemma InBox.Km_ge
    (hm0 : 0 ≤ (1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa)
    (hK0 : 0 ≤ sa + ((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2)) :
    (sa + ((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2))
        * ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa)
      ≤ Kc x * ((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
        - 2 * (Real.log x + 2) / x) :=
  mul_le_mul B.K_ge B.mE_ge hm0 (by linarith [B.K_ge])

lemma InBox.RC_le : RC x ≤ (lb - 0.6931471803 / 2) ^ 2 / 2
      + 0.6931471808 * ((sb + (3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2)) * (1 + 1 / Xa) - la / 2)
      + (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2 := by
  unfold RC
  have hlb := B.hlb
  have hl := B.l4
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h3 := log3_gt
  have e1 : (Real.log x - Real.log 2 / 2) ^ 2 ≤ (lb - 0.6931471803 / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h3' : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have e2 : (Real.log x - Real.log 3 / 2) ^ 2 ≤ (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hK := B.K_ge'
  have hKx : 0 ≤ Kc x * (1 / (x : ℝ)) := by
    have : 0 ≤ 1 / (x : ℝ) := by positivity
    exact mul_nonneg (by linarith [B.hla, B.hla4, B.hsa8]) this
  have hKl : Real.log x / 2 ≤ Kc x * (1 + 1 / (x : ℝ)) := by
    have e : Kc x * (1 + 1 / (x : ℝ)) = Kc x + Kc x * (1 / (x : ℝ)) := by ring
    rw [e]
    have : Real.log x / 2 ≤ Kc x := by
      have := B.hsa8; have := B.hsa
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < √(x : ℝ) by linarith)
      have hlx : Real.log x = 2 * Real.log √(x : ℝ) := by
        rw [Real.log_sqrt (by positivity)]; ring
      linarith [B.delta_nonneg]
    linarith
  have e3 : Kc x * (1 + 1 / (x : ℝ)) ≤ (sb + (3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2)) * (1 + 1 / Xa) :=
    mul_le_mul B.K_le (by linarith [B.inv_le]) (by positivity)
      (add_nonneg (by linarith [B.hsb, B.hsa, B.hsa8])
        (mul_nonneg (by linarith [B.hlb, B.l4]) (by positivity)))
  have e4 : Real.log 2 * (Kc x * (1 + 1 / (x : ℝ)) - Real.log x / 2)
      ≤ 0.6931471808 * ((sb + (3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2)) * (1 + 1 / Xa) - la / 2) :=
    mul_le_mul h2'.le (by linarith [B.hla]) (by linarith) (by norm_num)
  linarith

lemma InBox.mu_ge (hη1 : 0.6931471808 / 2 / la ≤ 1) :
    sa * (1 - 0.6931471808 / 2 / la) ^ 2 * (11 + 6 * 0.6931471803)
      ≤ muB x * (11 + 2 * Real.log 8) := by
  rw [muB_eq x B.x64, log8_eq]
  have h2 := Real.log_two_gt_d9
  have hηhi := B.eta_le
  have hη1' := B.eta_le_one
  have e1 : (1 - 0.6931471808 / 2 / la) ^ 2 ≤ (1 - Real.log 2 / 2 / Real.log x) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have e2 : sa ≤ nu x := B.hsa.trans B.s_le_nu
  have := mul_le_mul e2 e1 (by positivity) (by linarith [B.hsa8])
  exact mul_le_mul this (by linarith) (by norm_num)
    (mul_nonneg (by linarith [B.s_le_nu, B.hsa, B.hsa8]) (sq_nonneg _))

lemma InBox.kap_le : kap x ≤ sb + (3 + 4 / (sa - 1) + lb * (sa / (sa - 1))) := by
  rw [kap_eq B.x64]; have := B.eps_le'; have := B.hsb; linarith

lemma InBox.misc_ge :
    -(3 / 20) * sb - 3 * lb - 3 + 1 / 2 * 1.144 * la - (3.1416 ^ 2 / 6 - 0.57688 / 2 * la)
      ≤ -(3 / 20) * √(x : ℝ) - 3 * Real.log x - 3 + 1 / 2 * Real.log π * Real.log x
        - (π ^ 2 / 6 - eulerMascheroniConstant / 2 * Real.log x) := by
  have hpi := Erdos985.Analytic.PrincipalAux.log_pi_gt'
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have hla := B.hla; have hla4 := B.hla4; have hlb := B.hlb; have hsb := B.hsb
  have e1 : 1 / 2 * 1.144 * la ≤ 1 / 2 * Real.log π * Real.log x := by nlinarith
  have e2 : 0.57688 / 2 * la ≤ eulerMascheroniConstant / 2 * Real.log x := by nlinarith
  have e3 : π ^ 2 ≤ 3.1416 ^ 2 := by nlinarith
  linarith

end BoxFacts3

/-- Lower bound for `F₂(x, 8)` on a box. -/
noncomputable def F2aLo (Xa sa sb la lb : ℝ) : ℝ :=
  (sa ^ 2 * (0.6931471803 / 2 / lb) * (2 - 0.6931471808 / 2 / la) - (1 + 1 / (4 * Xa)))
    + (-(3 / 20) * sb - 3 * lb - 3
      + (sa + ((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2))
        * ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa)
      + 1 / 2 * 1.144 * la - (3.1416 ^ 2 / 6 - 0.57688 / 2 * la)
      - ((lb - 0.6931471803 / 2) ^ 2 / 2
        + 0.6931471808 * ((sb + (3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2)) * (1 + 1 / Xa) - la / 2)
        + (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2)
      + sa * (1 - 0.6931471808 / 2 / la) ^ 2 * (11 + 6 * 0.6931471803)
      - 8 * (sb + (3 + 4 / (sa - 1) + lb * (sa / (sa - 1)))))

/-- The side conditions for `F2aLo`. -/
def F2aSide (Xa sa sb la lb : ℝ) : Prop :=
  0 ≤ (1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa ∧
    0 ≤ sa + ((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2) ∧
    0.6931471808 / 2 / la ≤ 1

theorem F2a_ge {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
    (hS : F2aSide Xa sa sb la lb) : F2aLo Xa sa sb la lb ≤ F2 x 8 := by
  obtain ⟨hm0, hK0, hη1⟩ := hS
  rw [F2a_eq x B.x64]
  have h1 := B.A_ge hη1
  have h2 := B.Km_ge hm0 hK0
  have h3 := B.RC_le
  have h4 := B.mu_ge hη1
  have h5 := B.kap_le
  have h6 := B.misc_ge
  unfold F2aLo
  linarith only [h1, h2, h3, h4, h5, h6]


section BoxFacts4

variable {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
include B

lemma InBox.lam_le (hc : 3 + 6 * 0.6931471808 < sa) :
    Real.log (nu x - 3 - 2 * Real.log 8) - Real.log x / 2 - Real.log 8 ≤ -Real.log 8 := by
  have hs := B.hsa; have hs8 := B.hsa8
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h8' := log8_eq
  have h2 := Real.log_two_lt_d9
  have hls : Real.log x / 2 = Real.log √(x : ℝ) := by rw [Real.log_sqrt (by positivity)]
  rw [hls]
  have hpos : 0 < nu x - 3 - 2 * Real.log 8 := by
    have := B.s_le_nu; rw [h8']; linarith
  have : Real.log (nu x - 3 - 2 * Real.log 8) ≤ Real.log √(x : ℝ) := by
    apply Real.log_le_log hpos
    unfold nu
    have : 1 / (2 * √(x : ℝ)) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  linarith

lemma InBox.lam_ge (hc : 3 + 6 * 0.6931471808 < sa) :
    -(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808
      ≤ Real.log (nu x - 3 - 2 * Real.log 8) - Real.log x / 2 - Real.log 8 := by
  have hs := B.hsa; have hs8 := B.hsa8
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have h8 := log8_eq
  set c := 3 + 2 * Real.log 8 with hc_def
  have hcle : c ≤ 3 + 6 * 0.6931471808 := by rw [hc_def, h8]; linarith
  have hc0 : 0 < c := by rw [hc_def, h8]; linarith
  have hls : Real.log x / 2 = Real.log √(x : ℝ) := by rw [Real.log_sqrt (by positivity)]
  have hs0 : 0 < √(x : ℝ) := by linarith
  set M := nu x - 3 - 2 * Real.log 8 with hM
  have hMeq : M = √(x : ℝ) + 1 / (2 * √(x : ℝ)) - c := by rw [hM, hc_def]; unfold nu; ring
  have hMlo : √(x : ℝ) - c ≤ M := by
    rw [hMeq]; have : 0 < 1 / (2 * √(x : ℝ)) := div_pos one_pos (by linarith); linarith
  have hM0 : 0 < √(x : ℝ) - c := by linarith
  have hMpos : 0 < M := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < M / √(x : ℝ) by positivity)
  rw [Real.log_div hMpos.ne' hs0.ne', inv_div] at hlog
  -- `1 − s/M ≥ −c/(s − c)`
  have h1 : -c / (√(x : ℝ) - c) ≤ 1 - √(x : ℝ) / M := by
    have e : 1 - √(x : ℝ) / M = (M - √(x : ℝ)) / M := by field_simp
    rw [e]
    have hMs : -c ≤ M - √(x : ℝ) := by
      rw [hMeq]; have : 0 < 1 / (2 * √(x : ℝ)) := div_pos one_pos (by linarith); linarith
    rw [div_le_div_iff₀ hM0 hMpos]
    nlinarith
  have h2c : -(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) ≤ -c / (√(x : ℝ) - c) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div₀ (by linarith) hcle (by linarith) (by linarith)
  rw [hls, h8]
  have : Real.log 8 = 3 * Real.log 2 := h8
  linarith

end BoxFacts4

/-- Lower bound for `F₂(x, ν − 3 − 2 log 8)` on a box. -/
noncomputable def F2bLo (Xa sa sb la lb : ℝ) : ℝ :=
  min (sa * (((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa - 0.6931471808 * (1 + 1 / Xa))
        - 3 / 20 + (3 + 6 * 0.6931471803) - (3 + 4 / (sa - 1)) - lb / (sa - 1)
        + (-(0.6931471808 * (1 + 1 / (2 * Xa))) + (0.6931471803 / 2) ^ 2 / lb)
        + 2 * (1 + 1 / (2 * Xa)) * (1 - 0.6931471803 / 2 / lb) ^ 2
          * (-(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808)))
      (sb * (((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa - 0.6931471808 * (1 + 1 / Xa))
        - 3 / 20 + (3 + 6 * 0.6931471803) - (3 + 4 / (sa - 1)) - lb / (sa - 1)
        + (-(0.6931471808 * (1 + 1 / (2 * Xa))) + (0.6931471803 / 2) ^ 2 / lb)
        + 2 * (1 + 1 / (2 * Xa)) * (1 - 0.6931471803 / 2 / lb) ^ 2
          * (-(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808)))
    + min (((3 + la / 2) * (sb ^ 2 / (sb - 1) ^ 2) - sa / (sa - 1) ^ 2)
          * ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa - 0.6931471808 * (1 + 1 / Xa)))
        ((3 + lb / 2) * (sa ^ 2 / (sa - 1) ^ 2)
          * ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa - 0.6931471808 * (1 + 1 / Xa)))
    + ((-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * lb - 3.5 - 3.1416 ^ 2 / 6
        - (lb - 0.6931471803 / 2) ^ 2 / 2 - (lb - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2
        - (4 + lb) / (2 * (sa - 1)) + (3 + 6 * 0.6931471803) * (3 + la))

theorem F2b_ge {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
    (hc : 3 + 6 * 0.6931471808 < sa) :
    F2bLo Xa sa sb la lb ≤ F2 x (nu x - 3 - 2 * Real.log 8) := by
  rw [F2b_eq x B.x64]
  have hmE := B.mE_ge
  have h2 := B.log2_le
  have hf := B.frac_le
  have hlf := B.lfrac_le
  have hV := B.V_ge
  have hε := B.eps_le
  have hε' := B.eps_ge
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have h8 := log8_eq
  have hs0 : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
  have hla := B.hla
  have hl4 := B.l4
  -- the `ν/s` terms
  have hnus := B.nus_ge
  have hnus' := B.nus_le
  have ht1 : -(0.6931471808 * (1 + 1 / (2 * Xa))) + (0.6931471803 / 2) ^ 2 / lb
      ≤ nu x / √(x : ℝ) * (-(2 * (Real.log 2 / 2)) + (Real.log 2 / 2) ^ 2 / Real.log x) := by
    have e1 : (0.6931471803 / 2) ^ 2 / lb ≤ (Real.log 2 / 2) ^ 2 / Real.log x :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by linarith) 2)
        (by linarith) B.hlb
    have e2 : 0 ≤ (Real.log 2 / 2) ^ 2 / Real.log x := by positivity
    have e3 : (Real.log 2 / 2) ^ 2 / Real.log x ≤ nu x / √(x : ℝ) * ((Real.log 2 / 2) ^ 2 / Real.log x) := by
      nlinarith
    have e4 : -(0.6931471808 * (1 + 1 / (2 * Xa))) ≤ nu x / √(x : ℝ) * (-(2 * (Real.log 2 / 2))) := by
      have : nu x / √(x : ℝ) * Real.log 2 ≤ (1 + 1 / (2 * Xa)) * 0.6931471808 :=
        mul_le_mul hnus' hl2'.le (by linarith)
          (by have : 0 ≤ 1 / (2 * Xa) := div_nonneg zero_le_one (by linarith [B.hXa64]); linarith)
      nlinarith
    nlinarith
  have hlam := B.lam_ge hc
  have hlam' := B.lam_le hc
  have ht2 : 2 * (1 + 1 / (2 * Xa)) * (1 - 0.6931471803 / 2 / lb) ^ 2
        * (-(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808)
      ≤ 2 * (nu x / √(x : ℝ)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2
        * (Real.log (nu x - 3 - 2 * Real.log 8) - Real.log x / 2 - Real.log 8) := by
    have hηlo := B.eta_ge
    have hη1 := B.eta_le_one
    have hη0 := B.eta_nonneg
    set d := Real.log (nu x - 3 - 2 * Real.log 8) - Real.log x / 2 - Real.log 8
    have hd : d ≤ 0 := by have : 0 < Real.log 8 := Real.log_pos (by norm_num); linarith
    have ec : (1 - Real.log 2 / 2 / Real.log x) ^ 2 ≤ (1 - 0.6931471803 / 2 / lb) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have ea : 2 * (nu x / √(x : ℝ)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2
        ≤ 2 * (1 + 1 / (2 * Xa)) * (1 - 0.6931471803 / 2 / lb) ^ 2 :=
      mul_le_mul (by linarith) ec (sq_nonneg _)
        (by have : 0 ≤ 1 / (2 * Xa) := div_nonneg zero_le_one (by linarith [B.hXa64]); linarith)
    have ea0 : 0 ≤ 2 * (nu x / √(x : ℝ)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2 := by
      have : 0 ≤ nu x / √(x : ℝ) := by linarith
      positivity
    have hdlo : -(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808 ≤ d := hlam
    have hdlo0 : -(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808 ≤ 0 :=
      hdlo.trans hd
    calc 2 * (1 + 1 / (2 * Xa)) * (1 - 0.6931471803 / 2 / lb) ^ 2
          * (-(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808)
        ≤ 2 * (nu x / √(x : ℝ)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2
          * (-(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808) :=
          mul_le_mul_of_nonpos_right ea hdlo0
      _ ≤ _ := mul_le_mul_of_nonneg_left hdlo ea0
  have hQ := mul_lo B.hsa B.hsb hs0
    (q := ((1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa - 0.6931471808 * (1 + 1 / Xa))
        - 3 / 20 + (3 + 6 * 0.6931471803) - (3 + 4 / (sa - 1)) - lb / (sa - 1)
        + (-(0.6931471808 * (1 + 1 / (2 * Xa))) + (0.6931471803 / 2) ^ 2 / lb)
        + 2 * (1 + 1 / (2 * Xa)) * (1 - 0.6931471803 / 2 / lb) ^ 2
          * (-(3 + 6 * 0.6931471808) / (sa - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808))
    (Q := (((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
            - 2 * (Real.log x + 2) / x) - Real.log 2 * (1 + 1 / (x : ℝ)))
          - 3 / 20 + (3 + 2 * Real.log 8)
          - ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x / (√(x : ℝ) - 1))
          + nu x / √(x : ℝ) * (-(2 * (Real.log 2 / 2)) + (Real.log 2 / 2) ^ 2 / Real.log x)
          + 2 * (nu x / √(x : ℝ)) * (1 - Real.log 2 / 2 / Real.log x) ^ 2
            * (Real.log (nu x - 3 - 2 * Real.log 8) - Real.log x / 2 - Real.log 8))
    (by
      have hc8 : (3 + 6 * 0.6931471803 : ℝ) ≤ 3 + 2 * Real.log 8 := by rw [h8]; linarith
      linarith only [hmE, h2, hf, hlf, ht1, ht2, hc8])
  have hW := mul_lo B.delta_ge B.delta_le B.delta_nonneg
    (q := (1 - 1 / Xa) * (1.144 + 0.57688) - 2 * (lb + 2) / Xa - 0.6931471808 * (1 + 1 / Xa))
    (Q := ((1 - 1 / (x : ℝ)) * (Real.log π + eulerMascheroniConstant)
            - 2 * (Real.log x + 2) / x) - Real.log 2 * (1 + 1 / (x : ℝ)))
    (by linarith only [hmE, h2])
  have hc2 : (3 + 6 * 0.6931471803) * (3 + la)
      ≤ (3 + 2 * Real.log 8)
        * ((3 * √(x : ℝ) + 1) / (√(x : ℝ) - 1) + Real.log x * √(x : ℝ) / (√(x : ℝ) - 1)) := by
    rw [h8]
    have h4 := B.hla4
    exact mul_le_mul (by linarith only [hl2]) (by linarith only [hε', hla]) (by linarith only [h4])
      (by linarith only [hl2])
  have hls : 0 ≤ Real.log x / (2 * √(x : ℝ)) := by positivity
  unfold F2bLo
  linarith only [hQ, hW, hV, hε, hc2, hls]

lemma R5_of {x : ℕ} {Xa sa sb la lb : ℝ} (B : InBox x Xa sa sb la lb)
    (h : (lb - 594 / 256 * 0.6931471803 / 2) ^ 2 / 2
      ≤ 594 / 256 * 0.6931471803 * ((sa + 1 + la / 2) * (1 / 2 - 1 / Xa) + la / 2)) :
    R5OK x := by
  unfold R5OK
  have h5 := log5_gt
  have h5' : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num); linarith
  have hl := B.l4
  have hK := B.K_ge'
  have e1 : (Real.log x - Real.log 5 / 2) ^ 2 ≤ (lb - 594 / 256 * 0.6931471803 / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith [B.hlb]) 2
  have hX : 1 / 2 - 1 / Xa ≤ 1 / 2 - 1 / (x : ℝ) := by linarith [B.inv_le]
  have hX0 : 0 ≤ 1 / 2 - 1 / Xa := by
    have : 1 / Xa ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) B.hXa64
    linarith
  have e2 : (sa + 1 + la / 2) * (1 / 2 - 1 / Xa) ≤ Kc x / 2 - Kc x / x := by
    have : Kc x / 2 - Kc x / x = Kc x * (1 / 2 - 1 / (x : ℝ)) := by ring
    rw [this]
    exact mul_le_mul hK hX hX0 (by linarith [B.hsa8, B.hla4])
  have e3 : 594 / 256 * 0.6931471803 * ((sa + 1 + la / 2) * (1 / 2 - 1 / Xa) + la / 2)
      ≤ Real.log 5 * (Kc x / 2 - Kc x / x + Real.log x / 2) :=
    mul_le_mul h5 (by linarith [B.hla]) (add_nonneg (mul_nonneg (by linarith [B.hsa8, B.hla4]) hX0)
      (by linarith [B.hla4])) (by linarith)
  linarith

end LLS.Thm11
