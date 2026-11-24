import Schoenfeld.Inputs
import Schoenfeld.Density

/-!
# Rosser's zero count and the zero sum `F(T)`

* `analyticOrderAt_zeta_eq_xi`: in the upper half-plane `ζ` and erdos-985's `ξ` have the same
  zero orders, so `positiveZeroCount T = Σ_{ρ : Zeros, 0 < γ ≤ T} mult ρ` (`positiveZeroCount_eq`).
-/

namespace Schoenfeld

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux MeasureTheory Filter Topology

/-- In the upper half-plane, `ζ` and `ξ` have the same order at every point. -/
theorem analyticOrderAt_zeta_eq_xi {ρ : ℂ} (hρ : 0 < ρ.im) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt xiZeta ρ := by
  set V : Set ℂ := {s | 0 < s.im} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  have hVn : V ∈ 𝓝 ρ := hVo.mem_nhds hρ
  have ne0 : ∀ s ∈ V, s ≠ 0 := fun s hs h => by simp [hV, h] at hs
  have ne1 : ∀ s ∈ V, s ≠ 1 := fun s hs h => by simp [hV, h] at hs
  have hG : ∀ s ∈ V, Gammaℝ s ≠ 0 := by
    intro s hs h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
    have : s.im = 0 := by rw [hn]; simp
    simp only [hV, Set.mem_ofPred_eq] at hs; linarith
  set u : ℂ → ℂ := fun s => (Gammaℝ s)⁻¹ / (s * (s - 1)) with hu
  have hud : DifferentiableOn ℂ u V := by
    intro s hs
    have h1 : s * (s - 1) ≠ 0 := mul_ne_zero (ne0 s hs) (sub_ne_zero.mpr (ne1 s hs))
    exact ((differentiable_Gammaℝ_inv s).div (by fun_prop) h1).differentiableWithinAt
  have hua : AnalyticAt ℂ u ρ := hud.analyticAt hVn
  have hxa : AnalyticAt ℂ xiZeta ρ := differentiable_xiZeta.analyticAt ρ
  have hu0 : u ρ ≠ 0 := by
    have h1 : ρ * (ρ - 1) ≠ 0 := mul_ne_zero (ne0 ρ hρ) (sub_ne_zero.mpr (ne1 ρ hρ))
    simp only [hu]
    exact div_ne_zero (inv_ne_zero (hG ρ hρ)) h1
  have heq : riemannZeta =ᶠ[𝓝 ρ] u * xiZeta := by
    filter_upwards [hVn] with s hs
    have h0 := ne0 s hs
    have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne1 s hs)
    simp only [Pi.mul_apply, hu, xiZeta_eq h0 (ne1 s hs), riemannZeta_def_of_ne_zero h0]
    field_simp
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hua hxa,
    hua.analyticOrderAt_eq_zero.mpr hu0, zero_add]

/-- The zero count over erdos-985's zeros. -/
noncomputable def cnt (T : ℝ) : ℝ :=
  ∑' ρ : Zeros, if 0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T then mult ρ else 0

theorem positiveZeroCount_eq (T : ℝ) : positiveZeroCount T = cnt T := by
  classical
  unfold positiveZeroCount cnt
  have hsupp : (Function.support fun ρ : ℂ => if 0 < ρ.im ∧ ρ.im ≤ T then
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) ⊆ {ρ : ℂ | xiZeta ρ = 0} := by
    intro ρ hρ
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hρ
    obtain ⟨⟨him, -⟩, hne⟩ := hρ
    simp only [Set.mem_ofPred_eq]
    by_contra hx
    have : analyticOrderAt xiZeta ρ = 0 :=
      (differentiable_xiZeta.analyticAt ρ).analyticOrderAt_eq_zero.mpr hx
    rw [analyticOrderAt_zeta_eq_xi him, this] at hne
    simp at hne
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun ρ => ?_
  split_ifs with h
  · rw [analyticOrderAt_zeta_eq_xi h.1, mult]; rfl
  · rfl

/-! ### Symmetry `ρ ↦ 1 − ρ` -/

lemma mult_one_sub (ρ : Zeros) :
    analyticOrderNatAt xiZeta (1 - (ρ : ℂ)) = analyticOrderNatAt xiZeta (ρ : ℂ) := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 - w) (1 - (ρ : ℂ)) := by fun_prop
  have hd : deriv (fun w : ℂ => 1 - w) (1 - (ρ : ℂ)) ≠ 0 := by
    rw [deriv_const_sub, deriv_id'']; norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := xiZeta) hg hd
  have hc : (xiZeta ∘ fun w : ℂ => 1 - w) = xiZeta := funext fun w => xiZeta_one_sub w
  rw [hc, sub_sub_cancel] at h
  simp only [analyticOrderNatAt, h]

/-- `ρ ↦ 1 − ρ` on the zeros of `ξ`. -/
def reflect : Zeros ≃ Zeros where
  toFun ρ := ⟨1 - (ρ : ℂ), by rw [xiZeta_one_sub]; exact ρ.2⟩
  invFun ρ := ⟨1 - (ρ : ℂ), by rw [xiZeta_one_sub]; exact ρ.2⟩
  left_inv ρ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

lemma mult_reflect (ρ : Zeros) : mult (reflect ρ) = mult ρ := by
  simp only [mult, reflect, Equiv.coe_fn_mk, mult_one_sub]

lemma im_reflect (ρ : Zeros) : ((reflect ρ : Zeros) : ℂ).im = -(ρ : ℂ).im := by
  simp [reflect]

/-! ### The sum over zeros with positive ordinate -/

/-- `min(1/u, T/u²)`. -/
noncomputable def gmin (T u : ℝ) : ℝ := min (1 / u) (T / u ^ 2)

/-- `m · min(1/γ, T/γ²)` for `γ > 0`, else `0`. -/
noncomputable def posTerm (T : ℝ) (ρ : Zeros) : ℝ :=
  if 0 < (ρ : ℂ).im then mult ρ * gmin T (ρ : ℂ).im else 0

/-- `G(T) = Σ_{γ > 0} m · min(1/γ, T/γ²)`. -/
noncomputable def Gsum (T : ℝ) : ℝ := ∑' ρ, posTerm T ρ

lemma posTerm_nonneg {T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) : 0 ≤ posTerm T ρ := by
  unfold posTerm gmin
  split_ifs with h
  · exact mul_nonneg (mult_nonneg ρ) (le_min (by positivity) (by positivity))
  · exact le_rfl

lemma posTerm_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) :
    posTerm T ρ ≤ 2 * T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have h1 := im_sq_ge hRH ρ
  have h2 := twenty_le_normSq hRH ρ
  have hm := mult_nonneg ρ
  unfold posTerm gmin
  split_ifs with h
  · calc mult ρ * min (1 / (ρ : ℂ).im) (T / (ρ : ℂ).im ^ 2) ≤ mult ρ * (T / (ρ : ℂ).im ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ ≤ mult ρ * (T / (‖(ρ : ℂ)‖ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hT (by positivity) h1) hm
      _ = 2 * T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by field_simp
  · positivity

theorem posTerm_summable (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    Summable (posTerm T) :=
  Summable.of_nonneg_of_le (posTerm_nonneg hT) (posTerm_le hRH hT)
    ((zeroSum_summable hRH).mul_left (2 * T))

lemma fmin_le_posTerm (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (ρ : Zeros) :
    fmin T ρ ≤ posTerm T ρ + posTerm T (reflect ρ) := by
  have hp := im_sq_pos hRH ρ
  have hne : (ρ : ℂ).im ≠ 0 := fun h => by rw [h] at hp; norm_num at hp
  set a := |(ρ : ℂ).im| with ha
  have ha0 : 0 < a := abs_pos.mpr hne
  have han : a ≤ ‖(ρ : ℂ)‖ := Complex.abs_im_le_norm _
  have key : fmin T ρ ≤ mult ρ * gmin T a := by
    unfold fmin gmin
    refine mul_le_mul_of_nonneg_left (min_le_min ?_ ?_) (mult_nonneg ρ)
    · exact one_div_le_one_div_of_le ha0 han
    · exact div_le_div_of_nonneg_left hT (by positivity) (pow_le_pow_left₀ ha0.le han 2)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have e1 : posTerm T ρ = 0 := by unfold posTerm; rw [if_neg (by linarith)]
    have e2 : posTerm T (reflect ρ) = mult ρ * gmin T a := by
      unfold posTerm
      rw [im_reflect, if_pos (by linarith), mult_reflect, ha, abs_of_neg hneg]
    rw [e1, e2, zero_add]; exact key
  · have e1 : posTerm T ρ = mult ρ * gmin T a := by
      unfold posTerm; rw [if_pos hpos, ha, abs_of_pos hpos]
    have e2 : posTerm T (reflect ρ) = 0 := by
      unfold posTerm; rw [im_reflect, if_neg (by linarith)]
    rw [e1, e2, add_zero]; exact key

/-- `F(T) ≤ 2 G(T)`. -/
theorem fmin_tsum_le_two_Gsum (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    ∑' ρ, fmin T ρ ≤ 2 * Gsum T := by
  have hs := posTerm_summable hRH hT
  have hs' : Summable fun ρ => posTerm T (reflect ρ) := (reflect.summable_iff).mpr hs
  calc ∑' ρ, fmin T ρ ≤ ∑' ρ, (posTerm T ρ + posTerm T (reflect ρ)) :=
        (fmin_summable hRH hT).tsum_le_tsum (fmin_le_posTerm hRH hT) (hs.add hs')
    _ = Gsum T + Gsum T := by
        rw [hs.tsum_add hs', Gsum, reflect.tsum_eq (posTerm T)]
    _ = 2 * Gsum T := by ring

end Schoenfeld
