import Erdos985.Analytic.ExplicitFormula.Basic

/-!
# The contribution of a single zero to the explicit formula

On the line `s = 2 + t i` we study `(1/(s - ρ) - 1/(2 - ρ)) · x^s / (s(s+1))`: it is integrable,
its integral is `-2π · zeroTerm x ρ`, and its `L¹` norm is `O(x² ‖ρ‖^{-3/2})` for zeros in the
strip `0 < Re ρ < 1`.
-/

namespace Erdos985.Analytic.IdentityAux

open Complex MeasureTheory

/-- The weighted Perron kernel `x^s / (s(s+1))` on the line `Re s = 2`. -/
noncomputable def kern (x t : ℝ) : ℂ :=
  (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

/-- The kernel with one extra pole at `ρ`. -/
noncomputable def resKern (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

/-- The paired Hadamard term times the kernel. -/
noncomputable def pairTerm (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * kern x t

lemma line_ne_zero' (t : ℝ) : (2 : ℂ) + t * I ≠ 0 := fun h => by
  have := congrArg re h; simp at this

lemma line_add_one_ne_zero' (t : ℝ) : (2 : ℂ) + t * I + 1 ≠ 0 := fun h => by
  have := congrArg re h; simp at this; norm_num at this

lemma line_sub_ne_zero' {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) : (2 : ℂ) + t * I - ρ ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith

lemma two_sub_ne_zero' {ρ : ℂ} (hρ : ρ.re < 2) : (2 : ℂ) - ρ ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith

lemma pairTerm_eq (x : ℝ) (ρ : ℂ) (t : ℝ) :
    pairTerm x ρ t = resKern x ρ t - (1 / (2 - ρ)) * kern x t := by
  unfold pairTerm resKern kern
  simp only [div_eq_mul_inv, mul_inv]
  ring

lemma integrable_kern {x : ℝ} (hx : 0 < x) : Integrable (kern x) := by
  have := PerronKernel.integrable_K 2 x two_pos hx
  unfold PerronKernel.K at this
  simp only [ofReal_ofNat] at this
  exact this

lemma integrable_resKern {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
    Integrable (resKern x ρ) := by
  have := perron_residue_integrable x 2 hx two_pos ρ (by simpa using hρ)
  simp only [ofReal_ofNat] at this
  exact this

lemma integrable_pairTerm {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
    Integrable (pairTerm x ρ) := by
  have : pairTerm x ρ = fun t => resKern x ρ t - (1 / (2 - ρ)) * kern x t :=
    funext (pairTerm_eq x ρ)
  rw [this]
  exact (integrable_resKern hx hρ).sub ((integrable_kern hx).const_mul _)

lemma integral_kern {x : ℝ} (hx : 1 ≤ x) :
    ∫ t, kern x t = 2 * Real.pi * (1 - 1 / (x : ℂ)) := by
  have h := PerronKernel.perron_kernel x 2 (by linarith) two_pos
  simp only [ofReal_ofNat] at h
  rw [show (∫ t, kern x t) = _ from h, ite_eq_left_iff.2 (fun h => absurd hx h)]
  push_cast
  ring

lemma integral_pairTerm (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ -1) :
    ∫ t, pairTerm (x : ℝ) ρ t = -(2 * Real.pi) * zeroTerm x ρ := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h := perron_residue (x : ℝ) 2 hx' two_pos ρ (by simpa using hρ) hρ0 hρ1
  simp only [ofReal_ofNat, ofReal_natCast] at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hR : ∫ t, resKern (x : ℝ) ρ t = 2 * Real.pi * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ
      + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ)) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [resKern]
  have hK := integral_kern hx'
  simp_rw [pairTerm_eq]
  rw [integral_sub (integrable_resKern hx0 hρ) ((integrable_kern hx0).const_mul _),
    integral_const_mul, hR, hK]
  simp only [ofReal_natCast]
  unfold zeroTerm
  ring

lemma norm_pairTerm_le {x : ℝ} {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) :
    ‖pairTerm x ρ t‖ ≤
      ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
        / ‖(2 : ℂ) - ρ‖ := by
  have h0 := line_ne_zero' t
  have h1 := line_add_one_ne_zero' t
  have h2 := line_sub_ne_zero' hρ t
  have h3 := two_sub_ne_zero' hρ
  have heq : pairTerm x ρ t = ((2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1)))
        / (2 - ρ) := by
    unfold pairTerm kern
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  gcongr
  calc ‖(2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)‖ * _ ≤ 1 * _ := by
        gcongr
        rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
        have e : (2 : ℂ) - ((2 : ℂ) + t * I) = -(t * I) := by ring
        rw [e, norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        have := abs_im_le_norm ((2 : ℂ) + t * I)
        simpa using this
    _ = _ := one_mul _

/-- Uniform `L¹` bound for the paired term over zeros with `Re ρ < 1`. -/
theorem integral_norm_pairTerm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ ρ : ℂ, ρ.re < 1 → ρ ≠ 0 →
      ∫ t, ‖pairTerm x ρ t‖ ≤ C * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  refine ⟨3 * K, by positivity, fun x hx ρ hρ hρ0 => ?_⟩
  obtain ⟨hint, hbd⟩ := hK x 2 hx two_pos ρ (by norm_num; exact hρ.le)
  simp only [ofReal_ofNat] at hint hbd
  have hρ2 : ρ.re < 2 := by linarith
  have ha : 1 < ‖(2 : ℂ) - ρ‖ := by
    have := re_le_norm ((2 : ℂ) - ρ); simp at this; linarith
  have hr : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  calc ∫ t, ‖pairTerm x ρ t‖
      ≤ ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
          / ‖(2 : ℂ) - ρ‖ :=
        integral_mono (integrable_pairTerm hx hρ2).norm (hint.norm.div_const _)
          (norm_pairTerm_le hρ2)
    _ = (∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖)
          / ‖(2 : ℂ) - ρ‖ := integral_div _ _
    _ ≤ K * x ^ (2 : ℝ) * (1 + ‖ρ‖) ^ (-(1 / 2 : ℝ)) / ‖(2 : ℂ) - ρ‖ := by gcongr
    _ ≤ 3 * K * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
        have hle : ‖ρ‖ ≤ 3 * ‖(2 : ℂ) - ρ‖ := by
          have := norm_sub_le (2 : ℂ) ((2 : ℂ) - ρ)
          simp at this
          linarith
        have hsq : ‖ρ‖ ^ (1 / 2 : ℝ) ≤ (1 + ‖ρ‖) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hr.le (by linarith) (by norm_num)
        rw [Real.rpow_neg (by positivity), Real.rpow_add hr, Real.rpow_one]
        have hp1 : 0 < (1 + ‖ρ‖) ^ (1 / 2 : ℝ) := by positivity
        have hp2 : 0 < ‖ρ‖ ^ (1 / 2 : ℝ) := by positivity
        have hxk : 0 ≤ K * x ^ (2 : ℝ) := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹ * (‖ρ‖ * ‖ρ‖ ^ (1 / 2 : ℝ))
            ≤ K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹
                * (3 * ‖(2 : ℂ) - ρ‖ * (1 + ‖ρ‖) ^ (1 / 2 : ℝ)) := by
              gcongr
          _ = 3 * K * x ^ (2 : ℝ) * ‖(2 : ℂ) - ρ‖ := by
              field_simp

end Erdos985.Analytic.IdentityAux
