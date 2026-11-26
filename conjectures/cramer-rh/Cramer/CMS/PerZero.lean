import Cramer.CMS.Weight

/-!
# The weight at one zero

Real knots `t_j = m + (j − L)s`, `j = 0, …, J`, and second differences `a_j` of `c_j`
(`Cramer.CMS.aco`). For a zero `ρ = 1/2 + iγ`, `γ ≠ 0`, write `h = s/m`, `θ = γh` and
`A(θ) = ‖Σ_j a_j e^{ijθ}‖`. Two bounds for `T_ρ = Σ_j a_j g_ρ(t_j)`, `g_ρ(t) = t^{ρ+1}/(ρ(ρ+1))`:

* `norm_T_le_small` (good for small `θ`): with `E(t) = −m^{ρ+1}γ^{−2} e^{iγ(t−m)/m}`, whose
  second derivative is `m^{ρ−1}e^{iγ(t−m)/m}`, summation by parts and two mean-value steps give
  `‖T_ρ‖ ≤ m^{3/2}γ^{−2} A(θ) + s² m^{−1/2} Σ_j |c_j| (u_j + 2|γ| u_j²)`, `u_j = (|j−L|+1)h`;
* `norm_T_le_large` (decays like `θ^{−2}`): with `Ẽ(t) = m^{ρ+1}e^{iγ(t−m)/m}/(ρ(ρ+1))`,
  `‖T_ρ‖ ≤ m^{3/2}‖ρ(ρ+1)‖^{−1} (A(θ) + Σ_j |a_j| (2 v_j + 2|γ| v_j²))`, `v_j = |j−L| h`.

Both use `‖x^z − e^{iγ(x−1)}‖ ≤ |x^σ − 1| + |γ| |log x − (x−1)|` for `x > 0`, `z = σ + iγ`
(`norm_cpow_sub_exp_le`).
-/

namespace Cramer.CMS

open Finset Complex Real Cramer Set

/-- **Second differences.** If `f'' ` is bounded by `S` on `[p, p+2h]`, the second difference
is at most `h² S`. -/
lemma norm_second_diff_le {f f' f'' : ℝ → ℂ} {p h S : ℝ} (hh : 0 ≤ h)
    (hf : ∀ t ∈ Icc p (p + 2 * h), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc p (p + 2 * h), HasDerivAt f' (f'' t) t)
    (hS : ∀ t ∈ Icc p (p + 2 * h), ‖f'' t‖ ≤ S) :
    ‖f (p + 2 * h) - 2 * f (p + h) + f p‖ ≤ h ^ 2 * S := by
  set F : ℝ → ℂ := fun u => f (p + h + u) - f (p + u)
  have hF : ∀ u ∈ Icc (0 : ℝ) h, HasDerivWithinAt F (f' (p + h + u) - f' (p + u)) (Icc 0 h) u := by
    intro u hu
    have h1 := (hf (p + h + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add (p + h) u
    have h2 := (hf (p + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add p u
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) h, ‖f' (p + h + u) - f' (p + u)‖ ≤ S * h := by
    intro u hu
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := f') (f' := f'')
      (a := p + u) (b := p + h + u) (C := S)
      (fun t ht => (hf' t ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩).hasDerivWithinAt)
      (fun t ht => hS t ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩)
      (p + h + u) ⟨by linarith, le_rfl⟩
    rw [show p + h + u - (p + u) = h by ring] at key
    exact key
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hF hb h ⟨hh, le_rfl⟩
  have e : F h - F 0 = f (p + 2 * h) - 2 * f (p + h) + f p := by
    simp only [F, add_zero]
    rw [show p + h + h = p + 2 * h by ring]
    ring
  rw [e] at key
  calc _ ≤ S * h * (h - 0) := key
    _ = h ^ 2 * S := by ring

/-- `x^z = x^{Re z} e^{i Im z log x}` for `x > 0`. -/
lemma ofReal_cpow_eq {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = ((x ^ z.re : ℝ) : ℂ) * exp (I * ((z.im * Real.log x : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im z]
  push_cast; ring

/-- `‖x^z − e^{iγ(x−1)}‖ ≤ |x^σ − 1| + |γ| |log x − (x − 1)|`, `σ = Re z`, `γ = Im z`, `x > 0`. -/
lemma norm_cpow_sub_exp_le {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ‖(x : ℂ) ^ z - exp (I * ((z.im * (x - 1) : ℝ) : ℂ))‖ ≤
      |x ^ z.re - 1| + |z.im| * |Real.log x - (x - 1)| := by
  rw [ofReal_cpow_eq hx]
  set E1 := exp (I * ((z.im * Real.log x : ℝ) : ℂ))
  set E2 := exp (I * ((z.im * (x - 1) : ℝ) : ℂ))
  have hE1 : ‖E1‖ = 1 := by
    simp only [E1]
    rw [show I * ((z.im * Real.log x : ℝ) : ℂ) = ((z.im * Real.log x : ℝ) : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h1 : ‖((x ^ z.re : ℝ) : ℂ) * E1 - E1‖ = |x ^ z.re - 1| := by
    rw [show ((x ^ z.re : ℝ) : ℂ) * E1 - E1 = (((x ^ z.re - 1 : ℝ)) : ℂ) * E1 by push_cast; ring,
      norm_mul, hE1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖E1 - E2‖ ≤ |z.im| * |Real.log x - (x - 1)| := by
    have e : E1 - E2 = E2 * (exp (I * ((z.im * (Real.log x - (x - 1)) : ℝ) : ℂ)) - 1) := by
      simp only [E1, E2, mul_sub, mul_one, ← Complex.exp_add]
      congr 2; push_cast; ring
    have hE2 : ‖E2‖ = 1 := by
      simp only [E2]
      rw [show I * ((z.im * (x - 1) : ℝ) : ℂ) = ((z.im * (x - 1) : ℝ) : ℂ) * I by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [e, norm_mul, hE2, one_mul]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul]
  calc _ = ‖(((x ^ z.re : ℝ) : ℂ) * E1 - E1) + (E1 - E2)‖ := by ring_nf
    _ ≤ ‖((x ^ z.re : ℝ) : ℂ) * E1 - E1‖ + ‖E1 - E2‖ := norm_add_le _ _
    _ ≤ _ := by rw [h1]; linarith

/-! ### Real bounds for `|x − 1| ≤ u ≤ 1/2` -/

lemma abs_sqrt_sub_one_le {x : ℝ} (hx : 0 ≤ x) : |Real.sqrt x - 1| ≤ |x - 1| := by
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx
  have : x - 1 = (Real.sqrt x - 1) * (Real.sqrt x + 1) := by nlinarith
  rw [this, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt x + 1)]
  nlinarith [abs_nonneg (Real.sqrt x - 1)]

lemma rpow_three_halves_sub_one_le {x u : ℝ} (hxu : |x - 1| ≤ u) (hu : u ≤ 1 / 2) :
    |x ^ (3 / 2 : ℝ) - 1| ≤ 2 * u := by
  have hx : 0 < x := by have := (abs_le.1 hxu).1; linarith
  have e : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [e]
  set r := Real.sqrt x with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg x
  have hr2 : r ^ 2 = x := Real.sq_sqrt hx.le
  have hx1 := abs_le.1 hxu
  have hrx : x * r = r ^ 3 := by rw [← hr2]; ring
  rw [hrx, abs_le]
  have hrle : r ≤ 3 / 2 := by nlinarith
  have hq : 0 ≤ 1 + r - r ^ 2 := by nlinarith
  rcases le_total 1 r with h1 | h1
  · have hp := mul_nonneg (sub_nonneg.2 h1) hq
    have hfac : r ^ 3 - 1 ≤ 2 * (r ^ 2 - 1) := by nlinarith
    have h3 : 0 ≤ r ^ 3 - 1 := by nlinarith
    constructor <;> nlinarith
  · have hp := mul_nonneg (sub_nonneg.2 h1) hq
    have hfac : 1 - r ^ 3 ≤ 2 * (1 - r ^ 2) := by nlinarith
    have h3 : r ^ 3 - 1 ≤ 0 := by nlinarith
    constructor <;> nlinarith

lemma rpow_neg_half_sub_one_le {x u : ℝ} (hxu : |x - 1| ≤ u) (hu : u ≤ 1 / 2) :
    |x ^ (-(1 / 2) : ℝ) - 1| ≤ u := by
  have hx1 := abs_le.1 hxu
  have hx : 0 < x := by linarith
  have e : x ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]; simp [one_div]
  rw [e]
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs := abs_le.1 ((abs_sqrt_sub_one_le hx.le).trans hxu)
  have hsq := Real.sq_sqrt hx.le
  have hs2 : 1 / 2 ≤ Real.sqrt x := by nlinarith
  rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add]
  constructor
  · rw [le_div_iff₀ hs0]; nlinarith
  · rw [div_le_iff₀ hs0]; nlinarith

lemma abs_log_sub_le {x u : ℝ} (hxu : |x - 1| ≤ u) (hu : u ≤ 1 / 2) :
    |Real.log x - (x - 1)| ≤ 2 * u ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 - x) (by
    rw [abs_sub_comm]; linarith) 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one, sub_sub_cancel] at h
  have hx1 : |1 - x| = |x - 1| := abs_sub_comm _ _
  rw [hx1] at h
  have e : Real.log x - (x - 1) = 1 - x + Real.log x := by ring
  rw [e]
  have hden : 1 / 2 ≤ 1 - |x - 1| := by linarith
  have hsq : |x - 1| ^ (1 + 1) ≤ u ^ 2 := by
    rw [show (1 + 1 : ℕ) = 2 by rfl]; exact pow_le_pow_left₀ (abs_nonneg _) hxu 2
  calc _ ≤ |x - 1| ^ (1 + 1) / (1 - |x - 1|) := h
    _ ≤ u ^ 2 / (1 / 2) := by
        gcongr
    _ = 2 * u ^ 2 := by ring

/-! ### The two comparison functions -/

section Zero

variable {ρ : ℂ} (hρ : ρ.re = 1 / 2) {m : ℝ} (hm : 0 < m)
include hρ hm

/-- `E(t) = −m^{ρ+1} γ^{−2} e^{iγ(t−m)/m}`. -/
noncomputable def Ef (ρ : ℂ) (m : ℝ) (t : ℝ) : ℂ :=
  -((m : ℂ) ^ (ρ + 1) / (ρ.im : ℂ) ^ 2) * exp (I * ((ρ.im * (t - m) / m : ℝ) : ℂ))

/-- `E'(t)`. -/
noncomputable def Ef' (ρ : ℂ) (m : ℝ) (t : ℝ) : ℂ :=
  -((m : ℂ) ^ (ρ + 1) / (ρ.im : ℂ) ^ 2) * (I * (ρ.im / m : ℝ)) *
    exp (I * ((ρ.im * (t - m) / m : ℝ) : ℂ))

/-- `E''(t) = m^{ρ−1} e^{iγ(t−m)/m}`. -/
noncomputable def Ef'' (ρ : ℂ) (m : ℝ) (t : ℝ) : ℂ :=
  (m : ℂ) ^ (ρ - 1) * exp (I * ((ρ.im * (t - m) / m : ℝ) : ℂ))

omit hρ hm in
lemma hasDerivAt_phase (γ : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp (I * ((γ * (t - m) / m : ℝ) : ℂ)))
      (I * ((γ / m : ℝ) : ℂ) * exp (I * ((γ * (t - m) / m : ℝ) : ℂ))) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((γ * (t - m) / m : ℝ) : ℂ)) ((γ / m : ℝ) : ℂ) t := by
    have : HasDerivAt (fun t : ℝ => γ * (t - m) / m) (γ / m) t := by
      have := ((hasDerivAt_id t).sub_const m).const_mul γ |>.div_const m
      simpa using this
    exact this.ofReal_comp
  have h2 := (h1.const_mul I).cexp
  convert h2 using 1
  ring

omit hρ hm in
lemma hasDerivAt_Ef (t : ℝ) : HasDerivAt (Ef ρ m) (Ef' ρ m t) t := by
  have := (hasDerivAt_phase (m := m) ρ.im t).const_mul (-((m : ℂ) ^ (ρ + 1) / (ρ.im : ℂ) ^ 2))
  unfold Ef Ef'
  convert this using 1
  ring

omit hρ in
lemma hasDerivAt_Ef' (hγ : ρ.im ≠ 0) (t : ℝ) : HasDerivAt (Ef' ρ m) (Ef'' ρ m t) t := by
  have := (hasDerivAt_phase (m := m) ρ.im t).const_mul
    (-((m : ℂ) ^ (ρ + 1) / (ρ.im : ℂ) ^ 2) * (I * (ρ.im / m : ℝ)))
  unfold Ef' Ef''
  convert this using 1
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hγ0 : (ρ.im : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hpow : (m : ℂ) ^ (ρ + 1) = (m : ℂ) ^ (ρ - 1) * (m : ℂ) ^ 2 := by
    rw [show ρ + 1 = (ρ - 1) + 2 by ring, Complex.cpow_add _ _ hm0]
    norm_cast
  rw [hpow]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

omit hρ in
lemma norm_m_cpow (z : ℂ) : ‖(m : ℂ) ^ z‖ = m ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hm z

/-- `‖g_ρ'' − E''‖ ≤ m^{−1/2}(u + 2|γ|u²)` when `|t/m − 1| ≤ u ≤ 1/2`. -/
lemma norm_gpp_sub_Epp_le {t u : ℝ} (htu : |t / m - 1| ≤ u) (hu : u ≤ 1 / 2) :
    ‖(t : ℂ) ^ (ρ - 1) - Ef'' ρ m t‖ ≤ m ^ (-(1 / 2) : ℝ) * (u + 2 * |ρ.im| * u ^ 2) := by
  have hx : 0 < t / m := by have := (abs_le.1 htu).1; linarith
  have ht : 0 < t := by have := (div_pos_iff_of_pos_right hm).1 hx; exact this
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : (t : ℂ) ^ (ρ - 1) = (m : ℂ) ^ (ρ - 1) * ((t / m : ℝ) : ℂ) ^ (ρ - 1) := by
    rw [show (t : ℂ) = ((m * (t / m) : ℝ) : ℂ) by field_simp, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hm.le hx.le]
  have e2 : Ef'' ρ m t = (m : ℂ) ^ (ρ - 1) *
      exp (I * ((((ρ - 1).im) * (t / m - 1) : ℝ) : ℂ)) := by
    unfold Ef''
    congr 3
    simp only [sub_im, one_im, sub_zero]
    field_simp
  rw [e, e2, ← mul_sub, norm_mul, norm_m_cpow hm]
  have hre : (ρ - 1).re = -(1 / 2) := by simp [hρ]; norm_num
  rw [hre]
  gcongr
  refine (norm_cpow_sub_exp_le hx (ρ - 1)).trans ?_
  rw [hre, show (ρ - 1).im = ρ.im by simp]
  have h1 := rpow_neg_half_sub_one_le htu hu
  have h2 := abs_log_sub_le htu hu
  nlinarith [abs_nonneg ρ.im]

end Zero

/-- Real knots `t_j = m + (j − L)s`. -/
def tk (m s : ℝ) (L j : ℕ) : ℝ := m + ((j : ℝ) - L) * s

lemma tk_succ (m s : ℝ) (L j : ℕ) : tk m s L (j + 1) = tk m s L j + s := by
  unfold tk; push_cast; ring

lemma abs_tk_div_sub_one {m s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (L j : ℕ) {t : ℝ}
    (ht : |t - tk m s L j| ≤ s) : |t / m - 1| ≤ (|(j : ℝ) - L| + 1) * (s / m) := by
  have e : t / m - 1 = ((t - tk m s L j) + ((j : ℝ) - L) * s) / m := by
    unfold tk; field_simp; ring
  rw [e, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc |t - tk m s L j + ((j : ℝ) - L) * s| ≤ |t - tk m s L j| + |((j : ℝ) - L) * s| :=
        abs_add_le _ _
    _ ≤ s + |(j : ℝ) - L| * s := by rw [abs_mul, abs_of_nonneg hs]; linarith
    _ = (|(j : ℝ) - L| + 1) * (s / m) * m := by field_simp; ring

/-- `Σ_j a_j e^{iγ(t_j−m)/m}` has the norm of `Σ_j a_j e^{ijθ}`, `θ = γ s/m`. -/
lemma norm_sum_phase (c : ℕ → ℤ) (J L : ℕ) (m s γ : ℝ) (hm : 0 < m) :
    ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * ((γ * (tk m s L j - m) / m : ℝ) : ℂ))‖ =
      ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * (((j : ℝ) * (γ * s / m) : ℝ) : ℂ))‖ := by
  have e : ∀ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * ((γ * (tk m s L j - m) / m : ℝ) : ℂ)) =
      exp (I * ((-(L : ℝ) * (γ * s / m) : ℝ) : ℂ)) *
        ((aco c j : ℂ) * exp (I * (((j : ℝ) * (γ * s / m) : ℝ) : ℂ))) := by
    intro j _
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    unfold tk; push_cast; field_simp; ring
  rw [sum_congr rfl e, ← mul_sum, norm_mul]
  rw [show I * ((-(L : ℝ) * (γ * s / m) : ℝ) : ℂ) = ((-(L : ℝ) * (γ * s / m) : ℝ) : ℂ) * I by ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **First bound** (small `θ`). -/
theorem norm_T_le_small {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : ρ.im ≠ 0) {m s : ℝ} (hm : 0 < m)
    (hs : 0 ≤ s) (c : ℕ → ℤ) {J L : ℕ} (hc0 : c 0 = 0) (hcJ : ∀ j, J ≤ j → c j = 0)
    (hJL : J ≤ 2 * L) (hsmall : ((L : ℝ) + 1) * (s / m) ≤ 1 / 2) :
    ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (tk m s L j)‖ ≤
      m ^ (3 / 2 : ℝ) / ρ.im ^ 2 *
        ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * (((j : ℝ) * (ρ.im * s / m) : ℝ) : ℂ))‖
      + s ^ 2 * m ^ (-(1 / 2) : ℝ) * ∑ j ∈ range (J + 1), |(c j : ℝ)| *
          ((|(j : ℝ) - L| + 1) * (s / m) + 2 * |ρ.im| * ((|(j : ℝ) - L| + 1) * (s / m)) ^ 2) := by
  set D : ℝ → ℂ := fun t => gρ ρ t - Ef ρ m t
  have hsplit : ∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (tk m s L j) =
      ∑ j ∈ range (J + 1), (aco c j : ℂ) * Ef ρ m (tk m s L j) +
        ∑ j ∈ range (J + 1), (aco c j : ℂ) * D (tk m s L j) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun j _ => ?_; simp only [D]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the main term
    have e : ∑ j ∈ range (J + 1), (aco c j : ℂ) * Ef ρ m (tk m s L j) =
        -((m : ℂ) ^ (ρ + 1) / (ρ.im : ℂ) ^ 2) *
          ∑ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * ((ρ.im * (tk m s L j - m) / m : ℝ) : ℂ)) := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; unfold Ef; ring
    rw [e, norm_mul, norm_sum_phase c J L m s ρ.im hm, norm_neg, norm_div, norm_m_cpow hm,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [add_re, one_re, hρ]
    norm_num
  · -- the error term, by summation by parts
    have hbp := sum_aco_mul (R := ℂ) c hc0 hcJ (fun j => D (tk m s L j))
    rw [hbp]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [norm_mul, Complex.norm_intCast]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hc0]
    by_cases hjJ : J ≤ j
    · simp [hcJ j hjJ]
    push Not at hjJ
    have hjL : |(j : ℝ) - L| ≤ L := by
      rw [abs_le]
      have : (j : ℝ) ≤ 2 * L := by exact_mod_cast (by omega : j ≤ 2 * L)
      constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    set u := (|(j : ℝ) - L| + 1) * (s / m)
    have hu : u ≤ 1 / 2 := by
      have : u ≤ ((L : ℝ) + 1) * (s / m) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hs hm.le)
      linarith
    simp only [Nat.pos_iff_ne_zero.1 hj0, if_false]
    set p := tk m s L (j - 1)
    have hp1 : tk m s L j = p + s := by
      simp only [p]; rw [← tk_succ, Nat.sub_add_cancel (by omega)]
    have hp2 : tk m s L (j + 1) = p + 2 * s := by rw [tk_succ, hp1]; ring
    rw [hp1, hp2]
    have hrange : ∀ t ∈ Icc p (p + 2 * s), |t - tk m s L j| ≤ s := by
      intro t ht; rw [hp1, abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hpos : ∀ t ∈ Icc p (p + 2 * s), 0 < t := by
      intro t ht
      have h1 := abs_tk_div_sub_one hm hs L j (hrange t ht)
      have h2 : |t / m - 1| ≤ 1 / 2 := h1.trans hu
      have h3 : 0 < t / m := by have := (abs_le.1 h2).1; linarith
      exact (div_pos_iff_of_pos_right hm).1 h3
    have hρ1 : ρ ≠ -1 := fun h => by rw [h] at hρ; norm_num at hρ
    have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
    have key := norm_second_diff_le (f := D) (f' := fun t => gρ' ρ t - Ef' ρ m t)
      (f'' := fun t => (t : ℂ) ^ (ρ - 1) - Ef'' ρ m t) (p := p) (h := s)
      (S := m ^ (-(1 / 2) : ℝ) * (u + 2 * |ρ.im| * u ^ 2)) hs
      (fun t ht => (hasDerivAt_gρ hρ1 (hpos t ht).ne').sub (hasDerivAt_Ef t))
      (fun t ht => (hasDerivAt_gρ' hρ0 (hpos t ht).ne').sub (hasDerivAt_Ef' hm hγ t))
      (fun t ht => norm_gpp_sub_Epp_le hρ hm ((abs_tk_div_sub_one hm hs L j (hrange t ht))) hu)
    calc |(c j : ℝ)| * ‖D (p + 2 * s) - 2 * D (p + s) + D p‖
        ≤ |(c j : ℝ)| * (s ^ 2 * (m ^ (-(1 / 2) : ℝ) * (u + 2 * |ρ.im| * u ^ 2))) :=
          mul_le_mul_of_nonneg_left (by simpa [two_mul, add_assoc] using key) (abs_nonneg _)
      _ = _ := by ring

/-- **Second bound** (decays like `θ^{−2}`). -/
theorem norm_T_le_large {ρ : ℂ} (hρ : ρ.re = 1 / 2) {m s : ℝ} (hm : 0 < m)
    (hs : 0 ≤ s) (c : ℕ → ℤ) {J L : ℕ} (hJL : J ≤ 2 * L) (hsmall : (L : ℝ) * (s / m) ≤ 1 / 2) :
    ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (tk m s L j)‖ ≤
      m ^ (3 / 2 : ℝ) / ‖ρ * (ρ + 1)‖ *
        (‖∑ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * (((j : ℝ) * (ρ.im * s / m) : ℝ) : ℂ))‖
          + ∑ j ∈ range (J + 1), |(aco c j : ℝ)| *
            (2 * (|(j : ℝ) - L| * (s / m)) + 2 * |ρ.im| * (|(j : ℝ) - L| * (s / m)) ^ 2)) := by
  have hρ1 : ρ + 1 ≠ 0 := fun h => by
    have : (ρ + 1).re = 0 := by rw [h]; simp
    simp [hρ] at this; norm_num at this
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  set Et : ℝ → ℂ := fun t => (m : ℂ) ^ (ρ + 1) * exp (I * ((ρ.im * (t - m) / m : ℝ) : ℂ))
  have hg : ∀ t, gρ ρ t = (t : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) := by
    intro t; unfold gρ; rw [div_div, mul_comm (ρ + 1) ρ]
  have hsplit : ∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (tk m s L j) =
      (∑ j ∈ range (J + 1), (aco c j : ℂ) * Et (tk m s L j) +
        ∑ j ∈ range (J + 1), (aco c j : ℂ) * (((tk m s L j : ℝ) : ℂ) ^ (ρ + 1) - Et (tk m s L j)))
        / (ρ * (ρ + 1)) := by
    rw [← sum_add_distrib, sum_div]; refine sum_congr rfl fun j _ => ?_; rw [hg]; ring
  have hnorm : 0 < ‖ρ * (ρ + 1)‖ := norm_pos_iff.2 (mul_ne_zero hρ0 hρ1)
  rw [hsplit, norm_div]
  suffices hX : ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * Et (tk m s L j) +
      ∑ j ∈ range (J + 1), (aco c j : ℂ) * (((tk m s L j : ℝ) : ℂ) ^ (ρ + 1) - Et (tk m s L j))‖ ≤
      m ^ (3 / 2 : ℝ) * ‖∑ j ∈ range (J + 1), (aco c j : ℂ) *
        exp (I * (((j : ℝ) * (ρ.im * s / m) : ℝ) : ℂ))‖ + ∑ j ∈ range (J + 1), |(aco c j : ℝ)| *
        (m ^ (3 / 2 : ℝ) * (2 * (|(j : ℝ) - L| * (s / m)) + 2 * |ρ.im| * (|(j : ℝ) - L| * (s / m)) ^ 2)) by
    calc _ ≤ (m ^ (3 / 2 : ℝ) * ‖∑ j ∈ range (J + 1), (aco c j : ℂ) *
        exp (I * (((j : ℝ) * (ρ.im * s / m) : ℝ) : ℂ))‖ + ∑ j ∈ range (J + 1), |(aco c j : ℝ)| *
        (m ^ (3 / 2 : ℝ) * (2 * (|(j : ℝ) - L| * (s / m)) + 2 * |ρ.im| * (|(j : ℝ) - L| * (s / m)) ^ 2)))
          / ‖ρ * (ρ + 1)‖ := div_le_div_of_nonneg_right hX hnorm.le
      _ = _ := by
          rw [div_mul_eq_mul_div]
          congr 1
          rw [mul_add (m ^ (3 / 2 : ℝ)), mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => by ring
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have e : ∑ j ∈ range (J + 1), (aco c j : ℂ) * Et (tk m s L j) = (m : ℂ) ^ (ρ + 1) *
        ∑ j ∈ range (J + 1), (aco c j : ℂ) * exp (I * ((ρ.im * (tk m s L j - m) / m : ℝ) : ℂ)) := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; simp only [Et]; ring
    rw [e, norm_mul, norm_sum_phase c J L m s ρ.im hm, norm_m_cpow hm]
    simp only [add_re, one_re, hρ]; norm_num
  · refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
    rw [norm_mul, Complex.norm_intCast]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hjL : |(j : ℝ) - L| ≤ L := by
      rw [abs_le]
      have : (j : ℝ) ≤ 2 * L := by exact_mod_cast (by have := mem_range.1 hj; omega : j ≤ 2 * L)
      constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    set v := |(j : ℝ) - L| * (s / m)
    have hv : v ≤ 1 / 2 := by
      have : v ≤ (L : ℝ) * (s / m) := mul_le_mul_of_nonneg_right hjL (div_nonneg hs hm.le)
      linarith
    set x := tk m s L j / m
    have hx1 : |x - 1| ≤ v := by
      have e : x - 1 = ((j : ℝ) - L) * (s / m) := by simp only [x]; unfold tk; field_simp; ring
      rw [e, abs_mul, abs_of_nonneg (div_nonneg hs hm.le)]
    have hx : 0 < x := by have := (abs_le.1 (hx1.trans hv)).1; linarith
    have ht : tk m s L j = m * x := by simp only [x]; field_simp
    have e1 : ((tk m s L j : ℝ) : ℂ) ^ (ρ + 1) - Et (tk m s L j) =
        (m : ℂ) ^ (ρ + 1) * ((x : ℂ) ^ (ρ + 1) - exp (I * ((((ρ + 1).im) * (x - 1) : ℝ) : ℂ))) := by
      rw [ht, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hm.le hx.le, mul_sub]
      simp only [Et]
      congr 3
      simp only [add_im, one_im, add_zero]
      field_simp
    rw [e1, norm_mul, norm_m_cpow hm]
    simp only [add_re, one_re, hρ]
    rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_cpow_sub_exp_le hx (ρ + 1)).trans ?_
    simp only [add_re, one_re, hρ, add_im, one_im, add_zero]
    rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
    have h1 := rpow_three_halves_sub_one_le hx1 hv
    have h2 := abs_log_sub_le hx1 hv
    nlinarith [abs_nonneg ρ.im]

/-- **Third bound** (trivial): `‖T_ρ‖ ≤ (m + Ls)^{3/2} Σ|a_j| / ‖ρ(ρ+1)‖`. -/
theorem norm_T_le_trivial {ρ : ℂ} (hρ : ρ.re = 1 / 2) {m s : ℝ}
    (hs : 0 ≤ s) (c : ℕ → ℤ) {J L : ℕ} (hJL : J ≤ 2 * L) (hLs : (L : ℝ) * s < m) :
    ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (tk m s L j)‖ ≤
      (m + L * s) ^ (3 / 2 : ℝ) / ‖ρ * (ρ + 1)‖ * ∑ j ∈ range (J + 1), |(aco c j : ℝ)| := by
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
  rw [norm_mul, Complex.norm_intCast, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjL : (j : ℝ) - L ≤ L := by
    have : (j : ℝ) ≤ 2 * L := by exact_mod_cast (by have := mem_range.1 hj; omega : j ≤ 2 * L)
    linarith
  have ht : 0 < tk m s L j := by unfold tk; nlinarith
  unfold gρ
  rw [div_div, norm_div, mul_comm (ρ + 1) ρ, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [add_re, one_re, hρ]
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
  gcongr
  unfold tk; nlinarith

end Cramer.CMS
