import Littlewood.XiSide
import Erdos985.Analytic.ExplicitFormula.Bounds.DigammaSeries

/-!
# Step 5: the archimedean factor

`ξ(s) = s(s-1) Γℝ(s) ζ(s)` gives `ζ'/ζ = ξ'/ξ - R` with

    R(s) = 1/(s - 1) - ½ log π + ½ ψ(1 + s/2)

(`ψ(s/2) = ψ(1 + s/2) - 2/s` absorbs the `1/s`). `R` has simple poles at `1` and at
`-2k - 2`, and `ψ(1 + w) - ψ(1) = Σ_k (1/(k+1) - 1/(k+1+w))` is its pole expansion, so
`perron_termwise` applies to it as well (`perron_R`). The remaining terms `E_R` are bounded by
`x + 1 + Σ 1/(k+1)²` (`norm_ER_le`), and `‖ψ(1 + w)‖ ≤ 2 log (2 + ‖w‖) + 3` for `Re w ≥ 0`
(`norm_digamma_one_add_le`).
-/

open Complex MeasureTheory

namespace Littlewood

open Erdos985.Analytic Erdos985.Analytic.PrincipalAux Erdos985.Analytic.BoundsAux

/-- The archimedean part `R(s) = 1/(s-1) - ½ log π + ½ ψ(1 + s/2)` of `-ζ'/ζ = R - ξ'/ξ`. -/
noncomputable def archR (s : ℂ) : ℂ :=
  1 / (s - 1) - (1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (1 + s / 2)

/-- `ζ'/ζ = ξ'/ξ - R` on `Re s > 0`, away from `1` and the zeros of `ζ`. -/
theorem logDeriv_riemannZeta_eq_archR {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s = deriv xiZeta s / xiZeta s - archR s := by
  have hne0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hne1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hopen : IsOpen ({w : ℂ | 0 < w.re} ∩ {w | w ≠ 1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hev : xiZeta =ᶠ[nhds s] fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) := by
    filter_upwards [hopen.mem_nhds ⟨hs, hs1⟩] with w hw
    have hw0 : w ≠ 0 := fun h => by have := hw.1; rw [h] at this; simp at this
    rw [xiZeta_eq hw0 hw.2, riemannZeta_def_of_ne_zero hw0,
      mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hw.1)]
  have hp : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hd := hp.fun_mul ((StepAAux.hasDerivAt_Gammaℝ hs).fun_mul
    (differentiableAt_riemannZeta hs1).hasDerivAt)
  have hψ : digamma (s / 2) = digamma (1 + s / 2) - 2 / s := by
    have h := digamma_apply_add_one (s / 2) (fun m h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    rw [add_comm (s / 2) 1] at h
    rw [h]; field_simp; ring
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds, archR, hψ]
  field_simp
  ring

/-! ### The digamma bound -/

lemma norm_digamma_term_le {w : ℂ} (hw : 0 ≤ w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + w))‖
      ≤ 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + (2 + ‖w‖))) := by
  set r := ‖w‖
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hre : (k : ℝ) + 1 ≤ ‖(k : ℂ) + (1 + w)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp; linarith
  have hr : r ≤ ‖(k : ℂ) + (1 + w)‖ := by
    show ‖w‖ ≤ _
    rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_sq (norm_nonneg ((k : ℂ) + (1 + w)))]
    apply Real.sqrt_le_sqrt
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp
    nlinarith
  have hpos : 0 < ‖(k : ℂ) + (1 + w)‖ := lt_of_lt_of_le hk hre
  have hne : (k : ℂ) + (1 + w) ≠ 0 := norm_pos_iff.1 hpos
  have heq : 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + w)) = w / (((k : ℂ) + 1) * ((k : ℂ) + (1 + w))) := by
    field_simp; ring
  rw [heq, norm_div, norm_mul]
  have hk' : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg hk.le]
  rw [hk']
  have hmax : ((k : ℝ) + 1 + r) / 2 ≤ ‖(k : ℂ) + (1 + w)‖ := by linarith
  have hr0 : 0 ≤ r := norm_nonneg w
  rw [div_le_iff₀ (by positivity)]
  have hrhs : 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + (2 + r))) = 2 * (1 + r) / ((k + 1) * (k + 2 + r)) := by
    field_simp; ring
  rw [hrhs]
  have h2 : 0 < (k : ℝ) + 2 + r := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left hmax (show 0 ≤ ((k : ℝ) + 1) by positivity)
  nlinarith [mul_nonneg hr0 hk.le, mul_nonneg hr0 hr0]

/-- `‖ψ(1 + w) - ψ(1)‖ ≤ 2 (log (2 + ‖w‖) + 1)` for `Re w ≥ 0`. -/
theorem norm_digamma_one_add_sub_le {w : ℂ} (hw : 0 ≤ w.re) :
    ‖digamma (1 + w) - digamma 1‖ ≤ 2 * (Real.log (2 + ‖w‖) + 1) := by
  have hs := hasSum_digamma (w := 1 + w) (by simp; linarith)
  set r := ‖w‖
  have hx : (1 / 2 : ℝ) < 2 + r := by have := norm_nonneg w; linarith
  have hR := Complex.hasSum_re (hasSum_digamma_real hx)
  have hRterm : ∀ k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + ((2 + r : ℝ) : ℂ))).re
      = 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + (2 + r)) := by
    intro k
    rw [show (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + ((2 + r : ℝ) : ℂ)))
      = ((1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + (2 + r)) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  simp_rw [hRterm] at hR
  have hval : (digamma ((2 + r : ℝ) : ℂ) - digamma 1).re ≤ Real.log (2 + r) + 1 := by
    rw [digamma_ofReal (by positivity), digamma_one, sub_re, ofReal_re, neg_re, ofReal_re]
    have h1 := (rD_bounds (x := 2 + r) (by have := norm_nonneg w; linarith)).2
    have h2 := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  calc ‖digamma (1 + w) - digamma 1‖ ≤ ∑' k : ℕ, ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + w))‖ := by
        rw [← hs.tsum_eq]
        exact norm_tsum_le_tsum_norm ((hR.summable.mul_left 2).of_nonneg_of_le
          (fun _ => norm_nonneg _) (norm_digamma_term_le hw))
    _ ≤ ∑' k : ℕ, 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + (2 + r))) :=
        Summable.tsum_le_tsum (norm_digamma_term_le hw)
          ((hR.summable.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_digamma_term_le hw))
          (hR.summable.mul_left 2)
    _ = 2 * (digamma ((2 + r : ℝ) : ℂ) - digamma 1).re := by rw [tsum_mul_left, hR.tsum_eq]
    _ ≤ 2 * (Real.log (2 + r) + 1) := by linarith

/-- `‖ψ(1 + w)‖ ≤ 2 log (2 + ‖w‖) + 3` for `Re w ≥ 0`. -/
theorem norm_digamma_one_add_le {w : ℂ} (hw : 0 ≤ w.re) :
    ‖digamma (1 + w)‖ ≤ 2 * Real.log (2 + ‖w‖) + 3 := by
  have h := norm_digamma_one_add_sub_le hw
  have h1 : ‖digamma 1‖ ≤ 1 := by
    rw [digamma_one, norm_neg, norm_real, Real.norm_of_nonneg
      (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  calc ‖digamma (1 + w)‖ = ‖(digamma (1 + w) - digamma 1) + digamma 1‖ := by ring_nf
    _ ≤ ‖digamma (1 + w) - digamma 1‖ + ‖digamma 1‖ := norm_add_le _ _
    _ ≤ 2 * Real.log (2 + ‖w‖) + 3 := by linarith

/-! ### Perron for `R` -/

/-- The trivial poles `a_k = -2k - 2` of `R`. -/
noncomputable def trivPole (k : ℕ) : ℂ := -2 * (k : ℂ) - 2

/-- The non-main terms of the Perron formula for `R`. -/
noncomputable def ER (s : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2 +
    ∑' k : ℕ, -1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)

lemma norm_trivPole_sub_ge {s : ℂ} (hs : 0 ≤ s.re) (k : ℕ) :
    2 * (k : ℝ) + 2 ≤ ‖trivPole k - s‖ := by
  refine le_trans ?_ (abs_re_le_norm _)
  simp only [trivPole, sub_re, mul_re, natCast_re, natCast_im]
  norm_num
  rw [abs_of_neg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
  linarith

lemma summable_inv_rpow_three_halves :
    Summable fun k : ℕ => (((k : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2))
  refine h.congr fun k => ?_
  push_cast; ring_nf

/-- **Perron for `R`**: for `Re s > 0`, `s ≠ 1`, `x ≥ 1`,
`(1/2π) ∫ R(s + w) x^w / w² dv = R(s) log x + E_R(s, x)`. -/
theorem perron_R {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun v : ℝ => archR (s + lineP v) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))) ∧
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, archR (s + lineP v) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
      = archR s * Real.log x + ER s x := by
  have hc : Continuous fun v : ℝ => s + lineP v := continuous_const.add continuous_lineP
  have hre : ∀ v : ℝ, (s + lineP v).re = s.re + 2 := fun v => by simp
  -- the pole at `1`
  obtain ⟨hI1, hP1⟩ := perron_termwise (ι := Unit) (G := fun z => 1 / (z - 1)) hx
    (fun _ => 1) (fun _ => 1) (fun _ => by simp; linarith) (fun _ h => hs1 h.symm)
    (Summable.of_finite) (fun v => by
      have := hasSum_fintype (fun _ : Unit => (1 : ℂ) * (1 / (s + lineP v - 1) - 1 / (s - 1)))
      simp at this ⊢)
    (Continuous.div (f := fun _ => (1 : ℂ)) continuous_const (hc.sub continuous_const) fun v h => by
      have := congrArg re h; simp at this; linarith)
  -- the constant
  obtain ⟨hI2, hP2⟩ := perron_termwise (ι := Empty) (s := s)
    (G := fun _ => -(1 / 2) * (Real.log Real.pi : ℂ)) hx
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (Summable.of_finite) (fun v => by simp)
    continuous_const
  -- the digamma part
  have hne : ∀ z : ℂ, 0 < z.re → ∀ k : ℕ, (k : ℂ) + (1 + z / 2) ≠ 0 := fun z hz k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hne' : ∀ z : ℂ, 0 < z.re → ∀ k : ℕ, z - trivPole k ≠ 0 := fun z hz k h => by
    have := congrArg re h; simp [trivPole] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hdig : ∀ z : ℂ, 0 < z.re → HasSum (fun k : ℕ => (-1 : ℂ) * (1 / (z - trivPole k) - 1 / (s - trivPole k)))
      ((1 / 2) * digamma (1 + z / 2) - (1 / 2) * digamma (1 + s / 2)) := by
    intro z hz
    have h1 := hasSum_digamma (w := 1 + z / 2) (by simp; linarith)
    have h2 := hasSum_digamma (w := 1 + s / 2) (by simp; linarith)
    have := ((h1.sub h2).mul_left (1 / 2))
    convert this using 1
    · funext k
      have a1 := hne z hz k
      have a2 := hne s hs k
      have b1 := hne' z hz k
      have b2 := hne' s hs k
      have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp only [trivPole] at b1 b2 ⊢
      field_simp
      ring
    · ring
  have hψc : Continuous fun v : ℝ => (1 / 2 : ℂ) * digamma (1 + (s + lineP v) / 2) := by
    refine continuous_const.mul ?_
    refine differentiableOn_digamma.continuousOn.comp_continuous
      (continuous_const.add (hc.div_const 2)) fun v => ?_
    show 0 < (1 + (s + lineP v) / 2).re
    simp; linarith
  obtain ⟨hI3, hP3⟩ := perron_termwise (ι := ℕ) (G := fun z => (1 / 2) * digamma (1 + z / 2)) hx
    trivPole (fun _ => -1) (fun k => by
      simp only [trivPole, sub_re, mul_re, natCast_re, natCast_im]; norm_num
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    (fun k h => hne' s hs k (by rw [h]; ring))
    (by
      refine Summable.of_nonneg_of_le (fun k => mul_nonneg (div_nonneg (norm_nonneg _)
        (norm_nonneg _)) (Real.rpow_nonneg (by positivity) _)) (fun k => ?_)
        summable_inv_rpow_three_halves
      have hd := norm_trivPole_sub_ge hs.le k
      have hk : (0 : ℝ) < k + 1 := by positivity
      have hd' : (k : ℝ) + 1 ≤ ‖trivPole k - s‖ := by linarith
      rw [norm_neg, norm_one]
      have e1 : 1 / ‖trivPole k - s‖ ≤ ((k : ℝ) + 1)⁻¹ := by
        rw [one_div]; exact inv_anti₀ hk hd'
      have e2 : (1 + ‖trivPole k - s‖) ^ (-(1 / 2 : ℝ)) ≤ ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)
      calc 1 / ‖trivPole k - s‖ * (1 + ‖trivPole k - s‖) ^ (-(1 / 2 : ℝ))
          ≤ ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = (((k : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hk, ← Real.rpow_neg hk.le]; norm_num)
    (fun v => hdig _ (by rw [hre]; linarith)) hψc
  -- assemble
  have hsplit : (fun v : ℝ => archR (s + lineP v) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)))
      = fun v => (1 / (s + lineP v - 1)) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
        + (-(1 / 2) * (Real.log Real.pi : ℂ)) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
        + (1 / 2) * digamma (1 + (s + lineP v) / 2) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)) := by
    funext v; simp only [archR]; ring
  rw [hsplit]
  have hI12 : Integrable fun v : ℝ => (1 / (s + lineP v - 1)) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
        + (-(1 / 2) * (Real.log Real.pi : ℂ)) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)) :=
    hI1.add hI2
  refine ⟨hI12.add hI3, ?_⟩
  rw [integral_add hI12 hI3, integral_add hI1 hI2, mul_add, mul_add, hP1, hP2, hP3]
  simp only [archR, ER, tsum_fintype, Finset.univ_unique, Finset.sum_singleton,
    one_mul]
  ring

/-- `‖E_R(s, x)‖ ≤ x + 1 + Σ 1/(k+1)²` for `Re s ≥ 0`, `|Im s| ≥ 1`, `x ≥ 1`. -/
theorem norm_ER_le {s : ℂ} (hs : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {x : ℝ} (hx : 1 ≤ x) :
    ‖ER s x‖ ≤ x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hS : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := summable_inv_sq_succ
  have hcpow : ∀ b : ℂ, ‖(x : ℂ) ^ b‖ = x ^ b.re := fun b => norm_cpow_eq_rpow_re_of_pos hx0 b
  -- pole term
  have h1s : 1 ≤ ‖1 - s‖ := by
    refine ht.trans (le_trans ?_ (abs_im_le_norm _)); simp
  have hpole : ‖((x : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2‖ ≤ x + 1 := by
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have hp : ‖(x : ℂ) ^ (1 - s) - 1‖ ≤ x + 1 := by
      calc ‖(x : ℂ) ^ (1 - s) - 1‖ ≤ ‖(x : ℂ) ^ (1 - s)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = x ^ (1 - s.re) + 1 := by rw [hcpow]; simp
        _ ≤ x ^ (1 : ℝ) + 1 := by
            have := Real.rpow_le_rpow_of_exponent_le hx (show 1 - s.re ≤ 1 by linarith)
            linarith
        _ = x + 1 := by rw [Real.rpow_one]
    have : 1 ≤ ‖1 - s‖ ^ 2 := one_le_pow₀ h1s
    nlinarith
  -- trivial terms
  have htriv : ∀ k : ℕ, ‖-1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)‖
      ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hd := norm_trivPole_sub_ge hs k
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
  have hsumT : Summable fun k : ℕ => ‖-1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)‖ :=
    hS.of_nonneg_of_le (fun _ => norm_nonneg _) htriv
  calc ‖ER s x‖ ≤ ‖((x : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2‖ +
        ‖∑' k : ℕ, -1 * (((x : ℂ) ^ (trivPole k - s) - 1) / (trivPole k - s) ^ 2)‖ := norm_add_le _ _
    _ ≤ (x + 1) + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := by
        gcongr
        exact (norm_tsum_le_tsum_norm hsumT).trans (hsumT.tsum_le_tsum htriv hS)

/-- `‖R(2 + it)‖ ≤ log (3 + |t|) + 5`. -/
theorem norm_archR_two_le (t : ℝ) : ‖archR ((2 : ℂ) + t * I)‖ ≤ Real.log (3 + |t|) + 5 := by
  have h1 : ‖1 / ((2 : ℂ) + t * I - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one₀]
    · refine le_trans (by norm_num) (re_le_norm _)
    · exact lt_of_lt_of_le one_pos (le_trans (by norm_num) (re_le_norm _))
  have hpi : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  set A : ℂ := 1 / ((2 : ℂ) + t * I - 1)
  set B : ℂ := -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
  set C : ℂ := (1 / 2 : ℂ) * digamma (1 + ((2 : ℂ) + t * I) / 2)
  have h2 : ‖B‖ ≤ 3 / 2 := by
    simp only [B]
    rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hpi0]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]; linarith
  have hw : 0 ≤ (((2 : ℂ) + t * I) / 2).re := by simp
  have h3 := norm_digamma_one_add_le hw
  have hn : ‖((2 : ℂ) + t * I) / 2‖ ≤ 1 + |t| := by
    rw [norm_div]
    have := norm_add_le (2 : ℂ) (t * I)
    simp at this ⊢
    linarith [abs_nonneg t]
  have hlog : Real.log (2 + ‖((2 : ℂ) + t * I) / 2‖) ≤ Real.log (3 + |t|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hC : ‖C‖ ≤ (1 / 2) * (2 * Real.log (3 + |t|) + 3) := by
    simp only [C]
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linarith
  have heq : archR ((2 : ℂ) + t * I) = A + B + C := by
    simp only [archR, A, B, C]; ring
  rw [heq]
  have := norm_add₃_le (a := A) (b := B) (c := C)
  linarith

end Littlewood
