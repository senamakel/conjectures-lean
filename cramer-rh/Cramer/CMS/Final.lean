import Cramer.CMS.PrimeSide
import Cramer.CMS.FinalPoly

/-!
# The final inequality, for `x ≥ 10⁸`

With `u = √x`, `t = log x`, `q = (22/25) u t`, a natural `y` (the piece length `s'`) with
`q/128 − 1.02 ≤ y ≤ q/128` and `x + 64y ≤ m ≤ x + 1 + 64y`, the zero sum, the prime side and the
small terms are below the main term (`final_ineq`):

`64y² m^{−1/2} Zc(8y/m) + 1110972 + y² log(m+128y)·18838744/W + y·8388608·PP < 64y²·11989718`.

The proof bounds each term by an explicit function of `t`, using `u = 10⁴ e^{(t − log 10⁸)/2}`
(so `u ≥ 29 t²` and `u^{1/3} ≥ 3.3 (t − 12)`), and compares: the main term is
`≈ 1.0672·10⁷ (1 − 2(log t + 0.736)/t)`, the Brun–Titchmarsh term
`≈ 1.1774·10⁶ · t/(t + 2 log t − 11.7)`, the rest is `O(1/t)` or smaller, against
`11989718`; the margin is `≈ 10⁵` as `t → ∞` and grows like `5·10⁷/t` below.
-/

namespace Cramer.CMS

open Real

/-- The prime-power bound, for real endpoints. -/
noncomputable def PPr (a b : ℝ) : ℝ := Real.log b * ((√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1))

lemma exp_eighteen_le : Real.exp 18 ≤ 1e8 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 18
    _ ≤ 1e8 := by norm_num

lemma log_1e8_le : Real.log 1e8 ≤ 18.44 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 18.44 = Real.exp 1 ^ 18 * Real.exp 0.44 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_gt_d9
  have h3 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.44 by norm_num)
  rw [h1]
  have : (2.7182818283 : ℝ) ^ 18 ≤ Real.exp 1 ^ 18 := pow_le_pow_left₀ (by norm_num) h2.le 18
  nlinarith [Real.exp_pos 0.44]

lemma log_ge_of_sixteen {t : ℝ} (ht : 16 ≤ t) : 2.7725 ≤ Real.log t := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have := Real.log_le_log (by norm_num) ht
  have := Real.log_two_gt_d9
  linarith

/-- `u = √x` and `t = log x` for `x ≥ 10⁸`: the growth facts. -/
lemma growth {x : ℝ} (hx : 1e8 ≤ x) :
    1e4 ≤ √x ∧ 18 ≤ Real.log x ∧ 29 * Real.log x ^ 2 ≤ √x ∧
      3.3 * (Real.log x - 12) ≤ (√x) ^ ((1 : ℝ) / 3) ∧ Real.log (√x) = Real.log x / 2 := by
  have hx0 : 0 < x := by linarith
  have hu : (1e4 : ℝ) ≤ √x := by
    rw [show (1e4 : ℝ) = √(1e8) by rw [show (1e8 : ℝ) = (1e4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have ht : 18 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact exp_eighteen_le.trans hx
  have hlu : Real.log (√x) = Real.log x / 2 := by
    rw [Real.log_sqrt hx0.le]
  -- `√x = 10⁴ e^{d/2}`, `d = log x − log 10⁸`
  set d := Real.log x - Real.log 1e8
  have hd : 0 ≤ d := by
    have := Real.log_le_log (by norm_num) hx; simp only [d]; linarith
  have hsx : √x = 1e4 * Real.exp (d / 2) := by
    have e1 : √x = Real.exp (Real.log x / 2) := by
      rw [← hlu, Real.exp_log (Real.sqrt_pos.2 hx0)]
    have e2 : Real.exp (Real.log 1e8 / 2) = 1e4 := by
      rw [← Real.log_sqrt (by norm_num), Real.exp_log (by positivity)]
      rw [show (1e8 : ℝ) = (1e4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e1, show Real.log x / 2 = Real.log 1e8 / 2 + d / 2 by simp only [d]; ring, Real.exp_add, e2]
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ d / 2 by positivity)
  have hL := log_1e8_le
  have htd : Real.log x ≤ 18.44 + d := by simp only [d]; linarith
  refine ⟨hu, ht, ?_, ?_, hlu⟩
  · rw [hsx]
    have : 29 * Real.log x ^ 2 ≤ 29 * (18.44 + d) ^ 2 := by
      have : 0 ≤ Real.log x := by linarith
      gcongr
    nlinarith
  · -- `(√x)^{1/3} = 10^{4/3} e^{d/6} ≥ 21.54 (1 + d/6)`
    have e3 : (√x) ^ ((1 : ℝ) / 3) = Real.exp (Real.log x / 6) := by
      rw [Real.rpow_def_of_pos (Real.sqrt_pos.2 hx0), hlu]; ring_nf
    have e4 : Real.exp (Real.log x / 6) = Real.exp (Real.log 1e8 / 6) * Real.exp (d / 6) := by
      rw [← Real.exp_add]; congr 1; simp only [d]; ring
    have e5 : (21.54 : ℝ) ≤ Real.exp (Real.log 1e8 / 6) := by
      rw [show Real.log 1e8 / 6 = Real.log ((1e8 : ℝ) ^ ((1 : ℝ) / 6)) by
        rw [Real.log_rpow (by norm_num)]; ring, Real.exp_log (by positivity)]
      rw [show (21.54 : ℝ) = ((21.54 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) by
        rw [← Real.rpow_mul (by norm_num)]; norm_num]
      exact Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    have e6 := Real.add_one_le_exp (d / 6)
    rw [e3, e4]
    have : 21.54 * (1 + d / 6) ≤ Real.exp (Real.log 1e8 / 6) * Real.exp (d / 6) := by
      have : 0 ≤ 1 + d / 6 := by positivity
      calc 21.54 * (1 + d / 6) ≤ Real.exp (Real.log 1e8 / 6) * (1 + d / 6) := by gcongr
        _ ≤ _ := by gcongr; linarith
    nlinarith

/-- `log(0.11 π) ≥ −1.063`. -/
lemma log_pi_ge : -1.063 ≤ Real.log (0.11 * π) := by
  rw [neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (by positivity)]
  have h1 : Real.exp 1.063 = Real.exp 1 * Real.exp 0.063 := by rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_gt_d9
  have h3 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.063 by norm_num)
  have h4 := Real.pi_gt_d6
  rw [h1, inv_le_iff_one_le_mul₀ (by positivity)]
  have : (2.7182818283 : ℝ) * (1 + 0.063 + 0.063 ^ 2 / 2) ≤ Real.exp 1 * Real.exp 0.063 := by
    gcongr
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.063]

/-- `√(u² + δ) ≤ u + δ/(2u)`. -/
lemma sqrt_add_le {u δ : ℝ} (hu : 0 < u) (hδ : 0 ≤ δ) : √(u ^ 2 + δ) ≤ u + δ / (2 * u) := by
  rw [Real.sqrt_le_left (by positivity)]
  have : (u + δ / (2 * u)) ^ 2 = u ^ 2 + δ + (δ / (2 * u)) ^ 2 := by field_simp; ring
  rw [this]; nlinarith [sq_nonneg (δ / (2 * u))]

/-! ### The zero-sum term -/

/-- The bracket of the main term of `Zc`. -/
noncomputable def Xz (Λ h : ℝ) : ℝ :=
  Λ * (4252035564110250469740648 / (1099511627776 * 1048576) +
          h * (760852761666848834989 / (1048576 * 1048576))) +
        l2u / 4 * (463585232095674405339284 / (1099511627776 * 1048576) +
          h * (5587348473184294079485 / (1048576 * 1048576))) -
        l2l / 4 * (44601726036410213767724532 / (1099511627776 * 1048576) +
          h * (1037532018656752372080 / (1048576 * 1048576)))

/-- The Rosser factor of `Zc`. -/
noncomputable def Vz (h : ℝ) : ℝ :=
  (13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
      h * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576)

lemma Zc_split {h sm : ℝ} (hh : 0 < h) (hsm : 0 < sm) :
    sm⁻¹ * Zc h = 2 / (2 * π * h * sm) * Xz (Real.log (1 / (2 * π * h))) h +
      2 * sm⁻¹ * (Ero (120 / h) * Vz h) +
      2 * 740648 / 120 * (1 / (h * sm)) * ((1 + 16 * h) ^ (3 / 2 : ℝ) * tau (120 / h)) := by
  have hpi := Real.pi_pos
  unfold Zc Xz Vz
  generalize Real.log (1 / (2 * π * h)) = Λ
  generalize Ero (120 / h) = E
  generalize tau (120 / h) = τ
  generalize (1 + 16 * h) ^ (3 / 2 : ℝ) = P
  field_simp

lemma k29 {c d t : ℝ} (ht : 0 < t) (h : c ≤ 29 * d) : c * (1 / (29 * t)) ≤ d / t := by
  rw [mul_one_div, div_le_div_iff₀ (by positivity) ht]; nlinarith

lemma t3 {t : ℝ} (ht : 18 ≤ t) : 149 / (29 * t ^ 3) ≤ 0.01586 / t := by
  have ht0 : 0 < t := by linarith
  rw [div_le_div_iff₀ (by positivity) ht0]
  have : 324 ≤ t ^ 2 := by nlinarith
  nlinarith

/-- The setting: `u = √x`, `t = log x`, the piece length `y` and the centre `m`. -/
structure Setting (u t y m : ℝ) : Prop where
  hu4 : 1e4 ≤ u
  ht : 18 ≤ t
  hu29 : 29 * t ^ 2 ≤ u
  hlu : Real.log u = t / 2
  hy1 : y ≤ 22 / 25 * u * t / 128
  hy2 : 22 / 25 * u * t / 128 - 1.02 ≤ y
  hm1 : u ^ 2 + 64 * y ≤ m
  hm2 : m ≤ u ^ 2 + 1 + 64 * y

lemma log_c0_ge : -5.4 ≤ Real.log 0.00457 := by
  rw [neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 5.4 = Real.exp 1 ^ 5 * Real.exp 0.4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_gt_d9
  have h3 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.4 by norm_num)
  rw [h1]
  have : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h2.le 5
  nlinarith [Real.exp_pos 0.4, pow_pos (Real.exp_pos 1) 5]

namespace Setting

variable {u t y m : ℝ} (S : Setting u t y m)
include S

lemma u_pos : 0 < u := by linarith [S.hu4]
lemma t_pos : 0 < t := by linarith [S.ht]
lemma q_ge : 158400 ≤ 22 / 25 * u * t := by nlinarith [S.hu4, S.ht]
lemma y_ge : 1236 ≤ y := by have := S.q_ge; linarith [S.hy2]
lemma y_pos : 0 < y := by linarith [S.y_ge]
lemma m_ge : 1e8 ≤ m := by nlinarith [S.hm1, S.hu4, S.y_pos]
lemma m_pos : 0 < m := by linarith [S.m_ge]
/-- `t/u ≤ 1/(29 t)`. -/
lemma t_div_u : t / u ≤ 1 / (29 * t) := by
  rw [div_le_div_iff₀ S.u_pos (by linarith [S.t_pos])]; nlinarith [S.hu29]
lemma inv_tu : 1 / (u * t) ≤ 1 / (29 * t ^ 3) := by
  rw [div_le_div_iff₀ (by have := S.u_pos; have := S.t_pos; positivity) (by have := S.t_pos; positivity)]
  nlinarith [S.hu29, S.t_pos]

/-- `√m ≤ u (1 + 0.23 t/u)`. -/
lemma sqrt_m_le : √m ≤ u * (1 + 0.23 * (t / u)) := by
  have hu := S.u_pos
  have h1 : m ≤ u ^ 2 + (1 + 22 / 25 * u * t / 2) := by nlinarith [S.hm2, S.hy1]
  have h2 : √m ≤ √(u ^ 2 + (1 + 22 / 25 * u * t / 2)) := Real.sqrt_le_sqrt h1
  have h3 := sqrt_add_le hu (show 0 ≤ 1 + 22 / 25 * u * t / 2 by have := S.t_pos; positivity)
  have h4 : (1 + 22 / 25 * u * t / 2) / (2 * u) ≤ 0.23 * t := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [S.ht, S.hu4]
  have : u * (1 + 0.23 * (t / u)) = u + 0.23 * t := by field_simp
  rw [this]; linarith

/-- `8πy ≥ 0.055 π u t (1 − 149/(u t))`. -/
lemma eight_pi_y_ge : 0.055 * π * u * t * (1 - 149 / (u * t)) ≤ 8 * π * y := by
  have hpi := Real.pi_pos
  have hut : 0 < u * t := mul_pos S.u_pos S.t_pos
  have e : 0.055 * π * u * t * (1 - 149 / (u * t)) = π * (0.055 * u * t - 0.055 * 149) := by
    have : u * t * (1 - 149 / (u * t)) = u * t - 149 := by rw [mul_sub, mul_one, mul_div_cancel₀ _ hut.ne']
    linear_combination (0.055 * π) * this
  rw [e]
  have : 0.055 * u * t - 0.055 * 149 ≤ 8 * y := by nlinarith [S.hy2]
  nlinarith

/-- `√m/(8πy) ≤ (1/(0.055π t)) (1 + 0.024/t)`. -/
lemma rho_le : √m / (8 * π * y) ≤ 1 / (0.055 * π * t) * (1 + 0.024 / t) := by
  have hpi := Real.pi_pos
  have hu := S.u_pos
  have ht0 := S.t_pos
  have hy := S.y_pos
  have hA : 0.23 * (t / u) ≤ 0.00794 / t := by
    have := S.t_div_u
    calc 0.23 * (t / u) ≤ 0.23 * (1 / (29 * t)) := by gcongr
      _ ≤ 0.00794 / t := k29 ht0 (by norm_num)
  have hB : 149 / (u * t) ≤ 0.01586 / t := by
    have := S.inv_tu
    have h1 : 149 / (u * t) ≤ 149 / (29 * t ^ 3) := by
      rw [show 149 / (u * t) = 149 * (1 / (u * t)) by ring,
        show 149 / (29 * t ^ 3) = 149 * (1 / (29 * t ^ 3)) by ring]; gcongr
    exact h1.trans (t3 S.ht)
  have hB1 : 149 / (u * t) ≤ 1 / 2 := by
    refine hB.trans ?_; rw [div_le_iff₀ ht0]; nlinarith [S.ht]
  have hden : 0 < 0.055 * π * u * t * (1 - 149 / (u * t)) := by
    have : 0 < 1 - 149 / (u * t) := by linarith
    positivity
  calc √m / (8 * π * y) ≤ u * (1 + 0.23 * (t / u)) / (0.055 * π * u * t * (1 - 149 / (u * t))) :=
        div_le_div₀ (by positivity) S.sqrt_m_le hden S.eight_pi_y_ge
    _ = 1 / (0.055 * π * t) * ((1 + 0.23 * (t / u)) / (1 - 149 / (u * t))) := by
        field_simp
    _ ≤ 1 / (0.055 * π * t) * (1 + 0.024 / t) := by
        gcongr
        rw [div_le_iff₀ (by linarith)]
        have hb0 : 0 ≤ 149 / (u * t) := by positivity
        have hb1 : 149 / (u * t) ≤ 0.001 := by
          refine hB.trans ?_; rw [div_le_iff₀ ht0]; nlinarith [S.ht]
        have : 0.024 / t * (149 / (u * t)) ≤ 0.024 / t * 0.001 :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
        have h3 : 0.024 / t * 0.001 = 0.000024 / t := by ring
        have e : (1 + 0.024 / t) * (1 - 149 / (u * t)) =
            1 + 0.024 / t - 149 / (u * t) - 0.024 / t * (149 / (u * t)) := by ring
        have h5 : 0.00794 / t + 0.01586 / t + 0.000024 / t ≤ 0.024 / t := by
          rw [← add_div, ← add_div]
          exact div_le_div_of_nonneg_right (by norm_num) ht0.le
        rw [e]; linarith

/-- `h = 8y/m ≤ 0.055 t/u`. -/
lemma h_le : 8 * y / m ≤ 0.055 * (t / u) := by
  have hu := S.u_pos
  rw [div_le_iff₀ S.m_pos]
  have : 0.055 * (t / u) * (u ^ 2) = 0.055 * u * t := by field_simp
  have htu : 0 < t / u := div_pos S.t_pos hu
  have h2 : 0.055 * (t / u) * u ^ 2 ≤ 0.055 * (t / u) * m := by
    gcongr; nlinarith [S.hm1, S.y_pos]
  nlinarith [S.hy1]

lemma h_pos : 0 < 8 * y / m := div_pos (by linarith [S.y_pos]) S.m_pos

/-- `h ≤ 0.0019/t`. -/
lemma h_le' : 8 * y / m ≤ 0.0019 / t := by
  refine S.h_le.trans ?_
  have := S.t_div_u
  have ht0 := S.t_pos
  calc 0.055 * (t / u) ≤ 0.055 * (1 / (29 * t)) := by gcongr
    _ ≤ 0.0019 / t := k29 ht0 (by norm_num)

/-- `log(1/(2πh)) ≤ t/2 − log t + 1.063 + 0.05/t`. -/
lemma Lam_le : Real.log (1 / (2 * π * (8 * y / m))) ≤ t / 2 - Real.log t + 1.063 + 0.05 / t := by
  have hpi := Real.pi_pos
  have hu := S.u_pos
  have ht0 := S.t_pos
  have hy := S.y_pos
  have hm := S.m_pos
  have e1 : 1 / (2 * π * (8 * y / m)) = m / (16 * π * y) := by field_simp; ring
  rw [e1]
  -- `m ≤ u²(1 + 0.45 t/u)`, `16πy ≥ 0.11 π u t (1 − b)`
  have hmU : m ≤ u ^ 2 * (1 + 0.45 * (t / u)) := by
    have : u ^ 2 * (1 + 0.45 * (t / u)) = u ^ 2 + 0.45 * u * t := by field_simp
    rw [this]; nlinarith [S.hm2, S.hy1, S.hu4, S.ht]
  have hB : 149 / (u * t) ≤ 0.01586 / t := by
    have := S.inv_tu
    have h1 : 149 / (u * t) ≤ 149 / (29 * t ^ 3) := by
      rw [show 149 / (u * t) = 149 * (1 / (u * t)) by ring,
        show 149 / (29 * t ^ 3) = 149 * (1 / (29 * t ^ 3)) by ring]; gcongr
    exact h1.trans (t3 S.ht)
  have hB1 : 149 / (u * t) ≤ 1 / 2 := by
    refine hB.trans ?_; rw [div_le_iff₀ ht0]; nlinarith [S.ht]
  have h16 : 2 * (0.055 * π * u * t * (1 - 149 / (u * t))) ≤ 16 * π * y := by
    have := S.eight_pi_y_ge; linarith
  have hb0 : 0 < 1 - 149 / (u * t) := by linarith
  have hpos : 0 < 2 * (0.055 * π * u * t * (1 - 149 / (u * t))) := by positivity
  have hle : m / (16 * π * y) ≤ u ^ 2 * (1 + 0.45 * (t / u)) / (2 * (0.055 * π * u * t * (1 - 149 / (u * t)))) :=
    div_le_div₀ (by positivity) hmU hpos h16
  have hval : u ^ 2 * (1 + 0.45 * (t / u)) / (2 * (0.055 * π * u * t * (1 - 149 / (u * t)))) =
      u / t * (1 / (0.11 * π)) * ((1 + 0.45 * (t / u)) / (1 - 149 / (u * t))) := by
    field_simp; ring
  have hlog := Real.log_le_log (by positivity) hle
  rw [hval, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div hu.ne' ht0.ne', Real.log_div (by positivity) hb0.ne', S.hlu, one_div, Real.log_inv] at hlog
  have hpi' := log_pi_ge
  have h1 : Real.log (1 + 0.45 * (t / u)) ≤ 0.45 * (t / u) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 0.45 * (t / u) by positivity); linarith
  have h2 : -Real.log (1 - 149 / (u * t)) ≤ 2 * (149 / (u * t)) := by
    have := Real.one_sub_inv_le_log_of_pos hb0
    have : (1 - 149 / (u * t))⁻¹ ≤ 1 + 2 * (149 / (u * t)) := by
      have : 0 ≤ 149 / (u * t) := by positivity
      rw [inv_le_iff_one_le_mul₀ hb0]; nlinarith
    linarith
  have h3 : 0.45 * (t / u) ≤ 0.0156 / t := by
    have := S.t_div_u
    calc 0.45 * (t / u) ≤ 0.45 * (1 / (29 * t)) := by gcongr
      _ ≤ 0.0156 / t := k29 ht0 (by norm_num)
  have h4 : 2 * (149 / (u * t)) ≤ 0.0318 / t := by
    have := hB; rw [show (0.0318 : ℝ) / t = 2 * (0.01586 / t) + 0.00008 / t by ring]
    have : 0 ≤ 0.00008 / t := by positivity
    linarith
  have h5 : 0.0156 / t + 0.0318 / t ≤ 0.05 / t := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) ht0.le
  linarith

lemma log_t_ge : 2.88 ≤ Real.log t := by
  have h1 := Real.log_le_log (by norm_num) S.ht
  have h18 : Real.log 18 = 4 * Real.log 2 + Real.log (18 / 16) := by
    rw [show (18 : ℝ) = 2 ^ 4 * (18 / 16) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 18 / 16 by norm_num)
  have h3 := Real.log_two_gt_d9
  norm_num at h2
  linarith

/-- `h ≥ 0.82/u`. -/
lemma h_ge : 0.82 / u ≤ 8 * y / m := by
  have hu := S.u_pos
  have ht0 := S.t_pos
  have h8 : 0.05 * u * t ≤ 8 * y := by nlinarith [S.hy2, S.hu4, S.ht]
  have hm : m ≤ 1.001 * u ^ 2 := by
    have : 0.44 * t ≤ 0.0009 * u := by nlinarith [S.hu29, S.ht]
    nlinarith [S.hm2, S.hy1, S.hu4]
  rw [div_le_div_iff₀ hu S.m_pos]
  nlinarith [S.ht]

lemma T_le : 120 / (8 * y / m) ≤ 148 * u := by
  have hu := S.u_pos
  have hh := S.h_ge
  rw [div_le_iff₀ S.h_pos]
  calc (120 : ℝ) ≤ 148 * u * (0.82 / u) := by field_simp; norm_num
    _ ≤ 148 * u * (8 * y / m) := by gcongr

lemma T_ge : 1e6 ≤ 120 / (8 * y / m) := by
  have hh := S.h_le'
  have ht0 := S.t_pos
  rw [le_div_iff₀ S.h_pos]
  have : 0.0019 / t ≤ 0.0019 / 18 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) S.ht
  nlinarith

lemma logT_le : Real.log (120 / (8 * y / m)) ≤ t / 2 + 5 := by
  have hu := S.u_pos
  have h1 := Real.log_le_log (by linarith [S.T_ge]) S.T_le
  rw [Real.log_mul (by norm_num) hu.ne', S.hlu] at h1
  have h2 : Real.log 148 ≤ 5 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (148 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 5
  linarith

lemma logT_pos : 0 < Real.log (120 / (8 * y / m)) := Real.log_pos (by linarith [S.T_ge])

lemma Ero_le : Ero (120 / (8 * y / m)) ≤ t + 7 := by
  unfold Ero
  have h1 := S.logT_pos
  have h2 := Real.log_le_sub_one_of_pos h1
  have h3 := S.logT_le
  nlinarith [S.ht]

lemma tau_le : π * tau (120 / (8 * y / m)) ≤ (t / 2 + 5) + 0.31 * 3.141593 := by
  have hT := S.T_ge
  have hLT := S.logT_le
  have hLp := S.logT_pos
  unfold tau
  generalize 120 / (8 * y / m) = T at hT hLT hLp ⊢
  have hT0 : 0 < T := by linarith
  have hpi := Real.pi_pos
  have hpi' := Real.pi_lt_d6
  have hl := Real.log_le_sub_one_of_pos hT0
  have h2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have e : π * ((Real.log T - Real.log (2 * π)) / π + (2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T) =
      Real.log T - Real.log (2 * π) + π * ((2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T) := by
    field_simp; ring
  rw [e]
  have h1 : (2.463 + 0.3 / 2) / T ≤ 0.01 := by rw [div_le_iff₀ hT0]; linarith
  have h2 : 0.3 * Real.log T / T ≤ 0.3 := by rw [div_le_iff₀ hT0]; linarith
  have h3 : 0 ≤ (2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T := by positivity
  have h4 : π * ((2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T) ≤ 3.141593 * 0.31 :=
    mul_le_mul hpi'.le (by linarith) h3 (by norm_num)
  linarith

lemma tau_nonneg : 0 ≤ tau (120 / (8 * y / m)) := by
  have hT := S.T_ge
  have hLp := S.logT_pos
  unfold tau
  generalize 120 / (8 * y / m) = T at hT hLp ⊢
  have hT0 : 0 < T := by linarith
  have hpi := Real.pi_pos
  have h1 : Real.log (2 * π) ≤ Real.log T :=
    Real.log_le_log (by positivity) (by linarith [Real.pi_lt_four])
  have : 0 ≤ (Real.log T - Real.log (2 * π)) / π := div_nonneg (by linarith) hpi.le
  positivity

lemma P_le : (1 + 16 * (8 * y / m)) ^ (3 / 2 : ℝ) ≤ 1.005 := by
  have hh := S.h_le'
  have hh0 := S.h_pos
  have ht0 := S.t_pos
  have h1 : 0.0019 / t ≤ 0.0019 / 18 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) S.ht
  have hb : 1 ≤ 1 + 16 * (8 * y / m) := by linarith
  calc (1 + 16 * (8 * y / m)) ^ (3 / 2 : ℝ) ≤ (1 + 16 * (8 * y / m)) ^ ((2 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
    _ = (1 + 16 * (8 * y / m)) ^ 2 := Real.rpow_natCast _ 2
    _ ≤ 1.005 := by nlinarith

/-- **The zero-sum term**, normalised by `s² = 64y²`. -/
lemma zero_term : m ^ (-(1 / 2) : ℝ) * Zc (8 * y / m) ≤ Mb t + EVb t + Cb t := by
  have hm := S.m_pos
  have hu := S.u_pos
  have ht0 := S.t_pos
  have hy := S.y_pos
  have hpi := Real.pi_pos
  have hh0 := S.h_pos
  have hsm : 0 < √m := Real.sqrt_pos.2 hm
  have hsq : √m * √m = m := Real.mul_self_sqrt hm.le
  have hmr : m ^ (-(1 / 2) : ℝ) = (√m)⁻¹ := by
    rw [Real.rpow_neg hm.le, ← Real.sqrt_eq_rpow]
  rw [hmr, Zc_split hh0 hsm]
  have key : ∀ r : ℝ, 0 < r → r * r = m →
      2 / (2 * π * (8 * y / m) * r) = r / (8 * π * y) ∧ 1 / (8 * y / m * r) = π * (r / (8 * π * y)) := by
    intro r hr hrm
    subst hrm
    constructor
    · field_simp
    · field_simp
  obtain ⟨c1, c2⟩ := key (√m) hsm hsq
  rw [c1, c2]
  -- the coefficient
  have hco : √m / (8 * π * y) ≤ (1 + 0.024 / t) / (0.055 * 3.141592 * t) := by
    refine S.rho_le.trans ?_
    rw [one_div_mul_eq_div]
    have : 0 ≤ 1 + 0.024 / t := by positivity
    exact div_le_div_of_nonneg_left this (by positivity)
      (by have := Real.pi_gt_d6; nlinarith)
  have hco0 : 0 ≤ √m / (8 * π * y) := by positivity
  -- the main bracket
  have hX : Xz (Real.log (1 / (2 * π * (8 * y / m)))) (8 * y / m) ≤
      (t / 2 - 2.88 + 1.063 + 0.05 / t) *
        (4252035564110250469740648 / (1099511627776 * 1048576) +
          0.0019 / t * (760852761666848834989 / (1048576 * 1048576))) +
      0.6931471808 / 4 * (463585232095674405339284 / (1099511627776 * 1048576) +
          0.0019 / t * (5587348473184294079485 / (1048576 * 1048576))) -
      0.6931471803 / 4 * (44601726036410213767724532 / (1099511627776 * 1048576)) := by
    unfold Xz l2u l2l
    have hL := S.Lam_le
    have hl := S.log_t_ge
    have hh := S.h_le'
    have hLU : Real.log (1 / (2 * π * (8 * y / m))) ≤ t / 2 - 2.88 + 1.063 + 0.05 / t := by linarith
    have hLU0 : 0 ≤ t / 2 - 2.88 + 1.063 + 0.05 / t := by
      have : 0 ≤ 0.05 / t := by positivity
      linarith [S.ht]
    have e1 : Real.log (1 / (2 * π * (8 * y / m))) *
        (4252035564110250469740648 / (1099511627776 * 1048576) +
          8 * y / m * (760852761666848834989 / (1048576 * 1048576))) ≤
        (t / 2 - 2.88 + 1.063 + 0.05 / t) *
        (4252035564110250469740648 / (1099511627776 * 1048576) +
          0.0019 / t * (760852761666848834989 / (1048576 * 1048576))) := by
      calc _ ≤ (t / 2 - 2.88 + 1.063 + 0.05 / t) *
          (4252035564110250469740648 / (1099511627776 * 1048576) +
            8 * y / m * (760852761666848834989 / (1048576 * 1048576))) := by
            gcongr
        _ ≤ _ := by gcongr
    have e2 : 0 ≤ 8 * y / m * (1037532018656752372080 / (1048576 * 1048576)) := by positivity
    have e3 : 8 * y / m * (5587348473184294079485 / (1048576 * 1048576)) ≤
        0.0019 / t * (5587348473184294079485 / (1048576 * 1048576)) := by gcongr
    linarith
  have hXU0 : 0 ≤ (t / 2 - 2.88 + 1.063 + 0.05 / t) *
        (4252035564110250469740648 / (1099511627776 * 1048576) +
          0.0019 / t * (760852761666848834989 / (1048576 * 1048576))) +
      0.6931471808 / 4 * (463585232095674405339284 / (1099511627776 * 1048576) +
          0.0019 / t * (5587348473184294079485 / (1048576 * 1048576))) -
      0.6931471803 / 4 * (44601726036410213767724532 / (1099511627776 * 1048576)) := by
    have h1 : 0 ≤ 0.05 / t := by positivity
    have h2 : 0 ≤ 0.0019 / t := by positivity
    have h3 : (9 - 2.88 + 1.063 : ℝ) ≤ t / 2 - 2.88 + 1.063 + 0.05 / t := by linarith [S.ht]
    have h4 : (9 - 2.88 + 1.063 : ℝ) * (4252035564110250469740648 / (1099511627776 * 1048576)) ≤
        (t / 2 - 2.88 + 1.063 + 0.05 / t) *
        (4252035564110250469740648 / (1099511627776 * 1048576) +
          0.0019 / t * (760852761666848834989 / (1048576 * 1048576))) := by
      gcongr <;> nlinarith
    nlinarith
  have hM : √m / (8 * π * y) * Xz (Real.log (1 / (2 * π * (8 * y / m)))) (8 * y / m) ≤ Mb t := by
    unfold Mb
    calc _ ≤ √m / (8 * π * y) * _ := mul_le_mul_of_nonneg_left hX hco0
      _ ≤ _ := mul_le_mul_of_nonneg_right hco hXU0
  -- Rosser's error term
  have hEV : 2 * (√m)⁻¹ * (Ero (120 / (8 * y / m)) * Vz (8 * y / m)) ≤ EVb t := by
    unfold EVb Vz
    have hsu : 29 * t ^ 2 ≤ √m := by
      refine S.hu29.trans ?_
      rw [show u = √(u ^ 2) from (Real.sqrt_sq hu.le).symm]
      exact Real.sqrt_le_sqrt (by linarith [S.hm1, S.y_pos])
    have hinv : (√m)⁻¹ ≤ 1 / (29 * t ^ 2) := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by positivity) hsu
    have hE := S.Ero_le
    have hE0 : 0 ≤ Ero (120 / (8 * y / m)) := by
      have := Ero_ge (show (4.4 : ℝ) ≤ 120 / (8 * y / m) by linarith [S.T_ge]); linarith
    have hV : (13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
        8 * y / m * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576) ≤
        (13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
        0.0019 / t * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576) := by
      have := S.h_le'; gcongr
    have hV0 : 0 ≤ (13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
        8 * y / m * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576) := by positivity
    calc 2 * (√m)⁻¹ * (Ero (120 / (8 * y / m)) * _) ≤ 2 * (1 / (29 * t ^ 2)) * ((t + 7) *
          ((13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
        0.0019 / t * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576))) := by
          gcongr
      _ = _ := by ring
  -- the tail
  have hC : 2 * 740648 / 120 * (π * (√m / (8 * π * y))) *
      ((1 + 16 * (8 * y / m)) ^ (3 / 2 : ℝ) * tau (120 / (8 * y / m))) ≤ Cb t := by
    unfold Cb
    have hP := S.P_le
    have hP0 : 0 ≤ (1 + 16 * (8 * y / m)) ^ (3 / 2 : ℝ) := by positivity
    have hτ := S.tau_le
    have hτ0 := S.tau_nonneg
    have e : 2 * 740648 / 120 * (π * (√m / (8 * π * y))) *
        ((1 + 16 * (8 * y / m)) ^ (3 / 2 : ℝ) * tau (120 / (8 * y / m))) =
        2 * 740648 / 120 * (√m / (8 * π * y)) * (1 + 16 * (8 * y / m)) ^ (3 / 2 : ℝ) *
          (π * tau (120 / (8 * y / m))) := by ring
    rw [e]
    have : 0 ≤ π * tau (120 / (8 * y / m)) := by positivity
    gcongr
  linarith

/-! ### The prime side -/

/-- The Brun–Titchmarsh denominator: `W(√(2y/3)) ≥ t/4 − 3/2`. -/
lemma W_lower : t / 4 - 1.5 ≤ W (√(2 * y / 3)) := by
  have hu := S.u_pos
  have ht0 := S.t_pos
  have hy := S.y_pos
  have hy3 : 0.00457 * u * t ≤ 2 * y / 3 := by nlinarith [S.hy2, S.hu4, S.ht]
  have hR2 : 28 ≤ √(2 * y / 3) := by
    rw [show (28 : ℝ) = √(28 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [S.hu4, S.ht])
  have hW := W_ge (show (2 : ℝ) ≤ √(2 * y / 3) by linarith)
  set R := √(2 * y / 3) with hR
  have hR0 : 0 < R := by linarith
  -- `log R ≥ t/4 − 1.26`
  have hlR : t / 4 - 1.26 ≤ Real.log R := by
    rw [hR, Real.log_sqrt (by positivity)]
    have h1 := Real.log_le_log (by positivity) hy3
    rw [Real.log_mul (by positivity) ht0.ne', Real.log_mul (by norm_num) hu.ne', S.hlu] at h1
    have := log_c0_ge
    have := S.log_t_ge
    linarith
  -- `log(R − 1) ≥ log R − 1/(R − 1)`
  have hl1 : Real.log R - 1 / (R - 1) ≤ Real.log (R - 1) := by
    have hR1 : R - 1 ≠ 0 := by intro h; linarith
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < (R - 1) / R by
      apply div_pos <;> linarith)
    rw [Real.log_div hR1 hR0.ne'] at h1
    have : 1 - ((R - 1) / R)⁻¹ = -(1 / (R - 1)) := by
      rw [inv_div]; field_simp; ring
    linarith
  have h27 : 1 / (R - 1) ≤ 0.04 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hl2 := Real.log_two_lt_d9
  linarith

/-- `log b ≤ t + 0.003` for `b ≤ u² + 1 + 192y`. -/
lemma log_b_le {b : ℝ} (hb0 : 0 < b) (hb : b ≤ u ^ 2 + 1 + 192 * y) : Real.log b ≤ t + 0.003 := by
  have hu := S.u_pos
  have hb' : b ≤ u ^ 2 * 1.003 := by
    have : 1.32 * t ≤ 0.0029 * u := by nlinarith [S.hu29, S.ht]
    nlinarith [S.hy1, S.hu4]
  have h1 := Real.log_le_log hb0 hb'
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, S.hlu] at h1
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.003 by norm_num)
  push_cast at h1
  linarith

/-- **The prime side**, normalised by `s² = 64y²`. -/
lemma prime_term (hc : 3.3 * (t - 12) ≤ u ^ ((1 : ℝ) / 3)) {a b : ℝ} (ha : u ^ 2 - 64 * y ≤ a)
    (hb : b ≤ u ^ 2 + 1 + 192 * y) (hba : b - a = 256 * y) :
    (y ^ 2 * Real.log b * 18838744 / W (√(2 * y / 3)) + y * 8388608 * PPr a b) / (64 * y ^ 2) ≤
      BTb t + PPt t := by
  have hu := S.u_pos
  have ht0 := S.t_pos
  have hy := S.y_pos
  have ha0 : 0.9995 ^ 2 * u ^ 2 ≤ a := by
    have : 0.44 * t ≤ 0.0009 * u := by nlinarith [S.hu29, S.ht]
    nlinarith [S.hy1, S.hu4]
  have ha0' : 0 < a := lt_of_lt_of_le (by positivity) ha0
  have hb0 : 0 < b := by linarith
  have hlb := S.log_b_le hb0 hb
  have ht3 : (0 : ℝ) ≤ t + 0.003 := by linarith [S.ht]
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by nlinarith [S.hu4, S.y_pos])
  have hW := S.W_lower
  have hW0 : 0 < W (√(2 * y / 3)) := by linarith [S.ht]
  have e : (y ^ 2 * Real.log b * 18838744 / W (√(2 * y / 3)) + y * 8388608 * PPr a b) / (64 * y ^ 2) =
      18838744 * Real.log b / (64 * W (√(2 * y / 3))) + 131072 * (PPr a b / y) := by
    field_simp; ring
  rw [e]
  unfold BTb PPt
  gcongr ?_ + ?_
  · -- Brun–Titchmarsh
    have : 16 * t - 96 ≤ 64 * W (√(2 * y / 3)) := by linarith
    calc 18838744 * Real.log b / (64 * W (√(2 * y / 3))) ≤ 18838744 * (t + 0.003) / (64 * W (√(2 * y / 3))) := by
          gcongr
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by positivity) (by linarith [S.ht]) this
  · -- prime powers
    unfold PPr
    -- `√b − √a ≤ 128.1 y / u`
    have hsa : 0.9995 * u ≤ √a := by
      rw [show 0.9995 * u = √((0.9995 * u) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsab : √b - √a ≤ 128.1 * y / u := by
      have hsb : √a ≤ √b := Real.sqrt_le_sqrt (by linarith)
      have h1 : (√b - √a) * (√b + √a) = 256 * y := by
        rw [← hba]; ring_nf; rw [Real.sq_sqrt hb0.le, Real.sq_sqrt ha0'.le]
      rw [le_div_iff₀ hu]
      nlinarith
    -- `b^{1/3} ≤ 1.001 c²`, `c = u^{1/3}`
    obtain ⟨c, hcdef⟩ : ∃ c, c = u ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have hc0 : 0 < c := by rw [hcdef]; positivity
    have hc3 : c ^ 3 = u := by
      rw [hcdef, show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hu.le (by norm_num)
    have hc21 : 21.52 ≤ c := by
      by_contra hlt; push_neg at hlt
      have : c ^ 3 < 21.52 ^ 3 := by gcongr
      nlinarith [S.hu4]
    have hb3 : b ^ ((1 : ℝ) / 3) ≤ 1.001 * c ^ 2 := by
      have hb' : b ≤ (1.001 * c ^ 2) ^ 3 := by
        have : (1.001 * c ^ 2) ^ 3 = 1.001 ^ 3 * u ^ 2 := by rw [← hc3]; ring
        rw [this]
        have : 1.32 * t ≤ 0.0029 * u := by nlinarith [S.hu29, S.ht]
        nlinarith [S.hy1, S.hu4]
      calc b ^ ((1 : ℝ) / 3) ≤ ((1.001 * c ^ 2) ^ 3) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow hb0.le hb' (by norm_num)
        _ = 1.001 * c ^ 2 := by
            rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
            exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    have hy68 : 0.0068 * c ^ 3 * t ≤ y := by rw [hc3]; nlinarith [S.hy2, S.hu4, S.ht]
    have hct : 3.3 * (t - 12) ≤ c := hc
    have ht12 : 0 < 3.3 * (t - 12) := by linarith [S.ht]
    -- the two pieces
    have p1 : (√b - √a) / y ≤ 128.1 / (29 * t ^ 2) := by
      rw [div_le_iff₀ hy]
      calc √b - √a ≤ 128.1 * y / u := hsab
        _ ≤ 128.1 * y / (29 * t ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) S.hu29
        _ = 128.1 / (29 * t ^ 2) * y := by ring
    have p2 : (1 + (b ^ ((1 : ℝ) / 3) + 1)) / y ≤ 148 / (3.3 * (t - 12) * t) := by
      rw [div_le_div_iff₀ hy (by positivity)]
      have hc2 : 463 ≤ c ^ 2 := by nlinarith
      have h1 : 1 + (b ^ ((1 : ℝ) / 3) + 1) ≤ 1.00532 * c ^ 2 := by linarith
      have h2 : 1.00532 * c ^ 2 * (3.3 * (t - 12) * t) ≤ 1.00532 * c ^ 2 * (c * t) := by
        gcongr
      have h3 : 1.00532 * c ^ 2 * (c * t) ≤ 148 * (0.0068 * c ^ 3 * t) := by
        have : 0 ≤ c ^ 3 * t := by positivity
        nlinarith
      have h0 : 0 ≤ 1 + (b ^ ((1 : ℝ) / 3) + 1) := by positivity
      calc (1 + (b ^ ((1 : ℝ) / 3) + 1)) * (3.3 * (t - 12) * t)
          ≤ 1.00532 * c ^ 2 * (3.3 * (t - 12) * t) := by gcongr
        _ ≤ 148 * (0.0068 * c ^ 3 * t) := h2.trans h3
        _ ≤ 148 * y := by gcongr
    have e2 : Real.log b * ((√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1)) / y =
        Real.log b * ((√b - √a) / y + (1 + (b ^ ((1 : ℝ) / 3) + 1)) / y) := by
      ring
    rw [e2]
    have hsab0 : 0 ≤ (√b - √a) / y := by
      have : √a ≤ √b := Real.sqrt_le_sqrt (by linarith only [hba, hy])
      exact div_nonneg (sub_nonneg.2 this) hy.le
    have hQ0 : 0 ≤ (1 + (b ^ ((1 : ℝ) / 3) + 1)) / y := by positivity
    have hPQ : (√b - √a) / y + (1 + (b ^ ((1 : ℝ) / 3) + 1)) / y ≤
        128.1 / (29 * t ^ 2) + 148 / (3.3 * (t - 12) * t) := add_le_add p1 p2
    have hm : Real.log b * ((√b - √a) / y + (1 + (b ^ ((1 : ℝ) / 3) + 1)) / y) ≤
        (t + 0.003) * (128.1 / (29 * t ^ 2) + 148 / (3.3 * (t - 12) * t)) :=
      mul_le_mul hlb hPQ (add_nonneg hsab0 hQ0) ht3
    calc 131072 * (Real.log b * ((√b - √a) / y + (1 + (b ^ ((1 : ℝ) / 3) + 1)) / y))
        ≤ 131072 * ((t + 0.003) * (128.1 / (29 * t ^ 2) + 148 / (3.3 * (t - 12) * t))) :=
          mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by ring

/-- **The final inequality.** -/
theorem final_ineq (hc : 3.3 * (t - 12) ≤ u ^ ((1 : ℝ) / 3)) {a b : ℝ} (ha : u ^ 2 - 64 * y ≤ a)
    (hb : b ≤ u ^ 2 + 1 + 192 * y) (hba : b - a = 256 * y) :
    y ^ 2 * Real.log b * 18838744 / W (√(2 * y / 3)) + y * 8388608 * PPr a b <
      (8 * y) ^ 2 * 11989718 - (8 * y) ^ 2 * m ^ (-(1 / 2) : ℝ) * Zc (8 * y / m) - 3 / 2 * 740648 := by
  have hy := S.y_pos
  have hY : 0 < 64 * y ^ 2 := by positivity
  have hZ := S.zero_term
  have hP := S.prime_term hc ha hb hba
  have hF := final_poly S.ht
  have hE : 3 / 2 * 740648 ≤ 64 * y ^ 2 * 11 := by nlinarith [S.y_ge]
  rw [div_le_iff₀ hY] at hP
  have hZ' : 64 * y ^ 2 * (m ^ (-(1 / 2) : ℝ) * Zc (8 * y / m)) ≤ 64 * y ^ 2 * (Mb t + EVb t + Cb t) :=
    mul_le_mul_of_nonneg_left hZ hY.le
  have hF' : 64 * y ^ 2 * (Mb t + EVb t + Cb t + BTb t + PPt t + 11) < 64 * y ^ 2 * 11989718 :=
    mul_lt_mul_of_pos_left hF hY
  nlinarith

end Setting

end Cramer.CMS
