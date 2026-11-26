import Cramer.SecondDiff
import Cramer.Sharp.Taylor

/-!
# A sharp bound for the second difference `D_ρ`

For `ρ = 1/2 + iγ`, `γ ≠ 0`, `a, h > 0` and
`D_ρ = g(a+2h) − 2g(a+h) + g(a)`, `g(t) = t^{ρ+1}/(ρ(ρ+1))`:

`‖D_ρ‖ ≤ h² a^{−1/2} (sin²x / x² + h/a + 2|γ|h²/a²)`,   `x = γh/(2a)`.

`D_ρ` is the second difference of `φ(u) = g(a+u)`, with `φ'' = (a+u)^{ρ−1}`. We compare it with
`ψ(u) = −a^{ρ−1} κ^{−2} e^{iκu}`, `κ = γ/a`, whose second derivative is `a^{ρ−1} e^{iκu}` and
whose second difference has norm exactly `a^{−1/2} κ^{−2} |e^{iκh} − 1|² = h² a^{−1/2} sin²x/x²`.
The difference `φ'' − ψ''` is at most `a^{−1/2}(u/(2a) + |γ| u²/(2a²))` (amplitude and phase of
`(1 + u/a)^{ρ−1}` against `e^{iγu/a}`), and two mean-value steps bound its second difference.
-/

namespace Cramer

open Complex Set

/-- **Second differences and second derivatives.** If `F' = DF` and `F'' = DF'` on `[0, 2h]` and
`‖F''‖ ≤ M` there, then `‖F(2h) − 2F(h) + F(0)‖ ≤ M h²`. -/
theorem norm_second_diff_le_of_deriv2 {F F' F'' : ℝ → ℂ} {h M : ℝ} (hh : 0 ≤ h)
    (hF : ∀ u ∈ Icc (0 : ℝ) (2 * h), HasDerivAt F (F' u) u)
    (hF' : ∀ u ∈ Icc (0 : ℝ) (2 * h), HasDerivAt F' (F'' u) u)
    (hM : ∀ u ∈ Icc (0 : ℝ) (2 * h), ‖F'' u‖ ≤ M) :
    ‖F (2 * h) - 2 * F h + F 0‖ ≤ M * h ^ 2 := by
  -- step 1: `‖F'(h+u) − F'(u)‖ ≤ M h` for `u ∈ [0, h]`
  have h1 : ∀ u ∈ Icc (0 : ℝ) h, ‖F' (u + h) - F' u‖ ≤ M * h := by
    intro u hu
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := F') (f' := F'') (C := M)
      (a := u) (b := u + h)
      (fun t ht => (hF' t ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩).hasDerivWithinAt)
      (fun t ht => hM t ⟨by linarith [ht.1, hu.1], by linarith [ht.2, hu.2]⟩) (u + h)
      ⟨by linarith, le_rfl⟩
    simpa using key
  -- step 2: `G(u) = F(u+h) − F(u)` on `[0, h]`
  set G : ℝ → ℂ := fun u => F (u + h) - F u
  have hG : ∀ u ∈ Icc (0 : ℝ) h, HasDerivWithinAt G (F' (u + h) - F' u) (Icc 0 h) u := by
    intro u hu
    have e1 := (hF (u + h) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_add_const u h
    have e2 := hF u ⟨hu.1, by linarith [hu.2]⟩
    exact (e1.sub e2).hasDerivWithinAt
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hG
    (fun u hu => h1 u ⟨hu.1, hu.2.le⟩) h ⟨hh, le_rfl⟩
  have e : G h - G 0 = F (2 * h) - 2 * F h + F 0 := by
    simp only [G, zero_add]
    rw [show h + h = 2 * h by ring]
    ring
  rw [e] at key
  calc _ ≤ M * h * (h - 0) := key
    _ = M * h ^ 2 := by ring

/-- `‖a^{ρ−1}‖ = a^{−1/2}` on the critical line. -/
lemma norm_cpow_rho_sub_one {ρ : ℂ} (hρ : ρ.re = 1 / 2) {a : ℝ} (ha : 0 < a) :
    ‖((a : ℝ) : ℂ) ^ (ρ - 1)‖ = a ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp only [sub_re, one_re, hρ]
  norm_num

/-- `(1+v)^{ρ−1} = e^{−ℓ/2} e^{iγℓ}` with `ℓ = log(1+v)`, for `ρ = 1/2 + iγ`. -/
lemma one_add_cpow_eq {ρ : ℂ} (hρ : ρ.re = 1 / 2) {v : ℝ} (hv : 0 ≤ v) :
    (((1 + v : ℝ)) : ℂ) ^ (ρ - 1)
      = ((Real.exp (-(Real.log (1 + v)) / 2) : ℝ) : ℂ) * exp (I * ((ρ.im * Real.log (1 + v) : ℝ) : ℂ)) := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hne : (((1 + v : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have hρ' : ρ = (1 / 2 : ℂ) + I * (ρ.im : ℂ) := by
    apply Complex.ext <;> simp [hρ]
  rw [hρ']
  push_cast
  simp only [add_im, I_im, mul_im, ofReal_re, ofReal_im, I_re, div_ofNat_im, one_im]
  push_cast
  ring_nf

/-- **Amplitude and phase.** For `ρ = 1/2 + iγ`, `a > 0`, `u ≥ 0`:
`‖(a+u)^{ρ−1} − a^{ρ−1} e^{iγu/a}‖ ≤ a^{−1/2} (u/(2a) + |γ| u²/(2a²))`. -/
theorem norm_cpow_sub_exp_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    ‖(((a + u : ℝ)) : ℂ) ^ (ρ - 1) - ((a : ℝ) : ℂ) ^ (ρ - 1) * exp (I * ((ρ.im * (u / a) : ℝ) : ℂ))‖
      ≤ a ^ (-(1 / 2 : ℝ)) * (u / a / 2 + |ρ.im| * (u / a) ^ 2 / 2) := by
  set v := u / a with hvdef
  have hv : 0 ≤ v := div_nonneg hu ha.le
  have hsplit : (((a + u : ℝ)) : ℂ) ^ (ρ - 1) = ((a : ℝ) : ℂ) ^ (ρ - 1) * (((1 + v : ℝ)) : ℂ) ^ (ρ - 1) := by
    have : a + u = a * (1 + v) := by rw [hvdef]; field_simp
    rw [this, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (by linarith)]
  rw [hsplit, ← mul_sub, norm_mul, norm_cpow_rho_sub_one hρ ha]
  gcongr
  rw [one_add_cpow_eq hρ hv]
  set ℓ := Real.log (1 + v) with hℓ
  set γ := ρ.im
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓv : ℓ ≤ v := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + v by linarith); linarith
  have hvℓ : v - ℓ ≤ v ^ 2 / 2 := by have := sub_sq_div_two_le_log hv; linarith
  set E1 := exp (I * ((γ * ℓ : ℝ) : ℂ))
  set E2 := exp (I * ((γ * v : ℝ) : ℂ))
  have hE1 : ‖E1‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hamp : ‖((Real.exp (-ℓ / 2) : ℝ) : ℂ) * E1 - E1‖ ≤ v / 2 := by
    rw [← sub_one_mul, norm_mul, hE1, mul_one]
    have h1 : ((Real.exp (-ℓ / 2) : ℝ) : ℂ) - 1 = ((Real.exp (-ℓ / 2) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have h2 : Real.exp (-ℓ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 := Real.add_one_le_exp (-ℓ / 2)
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hph : ‖E1 - E2‖ ≤ |γ| * v ^ 2 / 2 := by
    have e : E1 - E2 = E2 * (exp (I * ((γ * (ℓ - v) : ℝ) : ℂ)) - 1) := by
      simp only [E1, E2, mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith : ℓ - v ≤ 0)]
    have := abs_nonneg γ
    nlinarith
  calc ‖((Real.exp (-ℓ / 2) : ℝ) : ℂ) * E1 - E2‖
      = ‖(((Real.exp (-ℓ / 2) : ℝ) : ℂ) * E1 - E1) + (E1 - E2)‖ := by ring_nf
    _ ≤ ‖((Real.exp (-ℓ / 2) : ℝ) : ℂ) * E1 - E1‖ + ‖E1 - E2‖ := norm_add_le _ _
    _ ≤ v / 2 + |γ| * v ^ 2 / 2 := add_le_add hamp hph

/-- **The sharp bound for `D_ρ`.** -/
theorem norm_second_diff_gρ_sharp {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : ρ.im ≠ 0) {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) :
    ‖gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a‖
      ≤ h ^ 2 * a ^ (-(1 / 2 : ℝ)) *
        (Real.sin (ρ.im * h / (2 * a)) ^ 2 / (ρ.im * h / (2 * a)) ^ 2 + h / a
          + 2 * |ρ.im| * h ^ 2 / a ^ 2) := by
  set γ := ρ.im with hγdef
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have hρ1 : ρ ≠ -1 := fun h => by rw [h] at hρ; norm_num at hρ
  set κ : ℝ := γ / a with hκ
  have hκ0 : κ ≠ 0 := div_ne_zero hγ ha.ne'
  set c : ℂ := ((a : ℝ) : ℂ) ^ (ρ - 1) with hc
  -- the comparison function
  set ψ : ℝ → ℂ := fun u => -c * (1 / (κ : ℂ) ^ 2) * exp (I * ((κ * u : ℝ) : ℂ))
  set ψ' : ℝ → ℂ := fun u => -c * (1 / (κ : ℂ) ^ 2) * (I * κ) * exp (I * ((κ * u : ℝ) : ℂ))
  set ψ'' : ℝ → ℂ := fun u => c * exp (I * ((κ * u : ℝ) : ℂ))
  have hexp : ∀ u : ℝ, HasDerivAt (fun u : ℝ => exp (I * ((κ * u : ℝ) : ℂ)))
      (I * κ * exp (I * ((κ * u : ℝ) : ℂ))) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => I * ((κ * u : ℝ) : ℂ)) (I * κ) u := by
      have := ((hasDerivAt_id u).const_mul κ).ofReal_comp.const_mul I
      simpa using this
    have := h1.cexp
    convert this using 1; ring
  have hψ : ∀ u, HasDerivAt ψ (ψ' u) u := by
    intro u
    have := (hexp u).const_mul (-c * (1 / (κ : ℂ) ^ 2))
    convert this using 1; simp only [ψ']; ring
  have hψ' : ∀ u, HasDerivAt ψ' (ψ'' u) u := by
    intro u
    have := (hexp u).const_mul (-c * (1 / (κ : ℂ) ^ 2) * (I * κ))
    convert this using 1
    simp only [ψ'']
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
    field_simp
    rw [show (I : ℂ) ^ 2 = -1 from I_sq]
    ring
  -- `φ(u) = g(a+u)`
  set φ : ℝ → ℂ := fun u => gρ ρ (a + u)
  set φ' : ℝ → ℂ := fun u => gρ' ρ (a + u)
  set φ'' : ℝ → ℂ := fun u => (((a + u : ℝ)) : ℂ) ^ (ρ - 1)
  have hφ : ∀ u, 0 ≤ u → HasDerivAt φ (φ' u) u := by
    intro u hu
    have := (hasDerivAt_gρ hρ1 (t := a + u) (by linarith)).comp_const_add a u
    simpa [φ, φ'] using this
  have hφ' : ∀ u, 0 ≤ u → HasDerivAt φ' (φ'' u) u := by
    intro u hu
    have := (hasDerivAt_gρ' hρ0 (t := a + u) (by linarith)).comp_const_add a u
    simpa [φ', φ''] using this
  -- the error bound on `[0, 2h]`
  set M : ℝ := a ^ (-(1 / 2 : ℝ)) * (2 * h / a / 2 + |γ| * (2 * h / a) ^ 2 / 2)
  have hM : ∀ u ∈ Icc (0 : ℝ) (2 * h), ‖φ'' u - ψ'' u‖ ≤ M := by
    intro u hu
    have key := norm_cpow_sub_exp_le hρ ha hu.1
    have e : ψ'' u = c * exp (I * ((γ * (u / a) : ℝ) : ℂ)) := by
      simp only [ψ'', hκ]; congr 3; ring
    rw [e]
    refine key.trans ?_
    have hua : u / a ≤ 2 * h / a := div_le_div_of_nonneg_right hu.2 ha.le
    have hua0 : 0 ≤ u / a := div_nonneg hu.1 ha.le
    show _ ≤ a ^ (-(1 / 2 : ℝ)) * (2 * h / a / 2 + |ρ.im| * (2 * h / a) ^ 2 / 2)
    gcongr
  have hdiff := norm_second_diff_le_of_deriv2 (F := fun u => φ u - ψ u) (F' := fun u => φ' u - ψ' u)
    (F'' := fun u => φ'' u - ψ'' u) hh.le
    (fun u hu => (hφ u hu.1).sub (hψ u)) (fun u hu => (hφ' u hu.1).sub (hψ' u)) hM
  -- the exact second difference of `ψ`
  have hψ2 : ψ (2 * h) - 2 * ψ h + ψ 0 = -c * (1 / (κ : ℂ) ^ 2) * (exp (I * ((κ * h : ℝ) : ℂ)) - 1) ^ 2 := by
    simp only [ψ]
    have e2 : exp (I * ((κ * (2 * h) : ℝ) : ℂ)) = exp (I * ((κ * h : ℝ) : ℂ)) ^ 2 := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [e2, show ((κ * 0 : ℝ) : ℂ) = 0 by simp, mul_zero, Complex.exp_zero]
    ring
  have hψn : ‖ψ (2 * h) - 2 * ψ h + ψ 0‖
      = h ^ 2 * a ^ (-(1 / 2 : ℝ)) * (Real.sin (γ * h / (2 * a)) ^ 2 / (γ * h / (2 * a)) ^ 2) := by
    rw [hψ2, norm_mul, norm_mul, norm_neg, hc, norm_cpow_rho_sub_one hρ ha, norm_pow,
      Complex.norm_exp_I_mul_ofReal_sub_one, norm_div, norm_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hx : κ * h / 2 = γ * h / (2 * a) := by rw [hκ]; field_simp
    rw [hx, abs_mul, mul_pow, sq_abs, sq_abs]
    have hγ2 : (γ * h / (2 * a)) ^ 2 = κ ^ 2 * h ^ 2 / 4 := by rw [hκ]; field_simp; ring
    rw [hγ2]
    have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ0
    field_simp
    rw [sq_abs]
    ring
  -- combine
  have e : gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a
      = ((φ (2 * h) - ψ (2 * h)) - 2 * (φ h - ψ h) + (φ 0 - ψ 0))
        + (ψ (2 * h) - 2 * ψ h + ψ 0) := by
    simp only [φ, add_zero]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [hψn]
  have hM' : M * h ^ 2 = h ^ 2 * a ^ (-(1 / 2 : ℝ)) * (h / a + 2 * |γ| * h ^ 2 / a ^ 2) := by
    simp only [M]; field_simp
  have := hdiff
  rw [hM'] at this
  nlinarith [this]

end Cramer
