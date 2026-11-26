import Cramer.Statement3
import Erdos233.Basic

/-!
# The nontrivial zeros of `ζ` are the zeros of `ξ`, with the same multiplicities

`Cramer.NontrivialZeros` (Mathlib's `riemannZeta`, `0 < Re ρ < 1`) and erdos-233's `Zeros`
(the zeros of erdos-985's entire `xiZeta s = s(s − 1)Λ(s)`) are in bijection, and
`analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt xiZeta ρ` there. Unconditional.

The proofs follow `RiemannHypothesis.xiZeta_eq_zero_of_mem` and
`RiemannHypothesis.mem_strip_of_xiZeta_eq_zero` (senamakel/li-criterion-rh,
`LiCriterion/Zeros.lean`) and `Density.analyticOrderNatAt_riemannZeta_eq_xiZeta`
(senamakel/density-rh, `Density/ZeroCount/Xi.lean`), same author, restated here for the strip
only.
-/

namespace Cramer.MeanSq

open Complex Filter Topology Erdos985.Analytic Erdos233

lemma xiZeta_eq_zero_of_mem {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    xiZeta ρ = 0 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  rw [xiZeta_eq hρ0 hρ1]
  have hΓ := Gammaℝ_ne_zero_of_re_pos h0
  have : completedRiemannZeta ρ = 0 := by
    have h := riemannZeta_def_of_ne_zero hρ0
    rw [hζ, eq_comm, div_eq_zero_iff] at h
    exact h.resolve_right hΓ
  rw [this, mul_zero]

lemma mem_strip_of_xiZeta_eq_zero {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
  obtain ⟨h0, h1⟩ := xiZeta_zero_re_mem hρ
  refine ⟨h0, h1, ?_⟩
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  rw [xiZeta_eq hρ0 hρ1] at hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rcases mul_eq_zero.mp hρ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.mp h) hρ1
    · exact h
  rw [riemannZeta_def_of_ne_zero hρ0, hΛ, zero_div]

/-- The cofactor `ζ / ξ`. -/
noncomputable def zetaXiFactor (s : ℂ) : ℂ := (Gammaℝ s)⁻¹ / (s * (s - 1))

lemma riemannZeta_eq_xiZeta_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannZeta s = xiZeta s * zetaXiFactor s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [xiZeta_eq hs0 hs1, zetaXiFactor, riemannZeta_def_of_ne_zero hs0]
  field_simp

lemma analyticAt_zetaXiFactor {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    AnalyticAt ℂ zetaXiFactor ρ := by
  have hU : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
  refine DifferentiableOn.analyticAt (s := ({0, 1}ᶜ : Set ℂ)) ?_ (hU.mem_nhds (by simp [h0, h1]))
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  have hd : z * (z - 1) ≠ 0 := mul_ne_zero hz.1 (sub_ne_zero.mpr hz.2)
  exact ((differentiable_Gammaℝ_inv z).div (by fun_prop) hd).differentiableWithinAt

/-- In the critical strip `ζ` and `ξ` vanish to the same order. -/
theorem analyticOrderNatAt_riemannZeta_eq_xiZeta {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt xiZeta ρ := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hev : riemannZeta =ᶠ[𝓝 ρ] xiZeta * zetaXiFactor := by
    have hU : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
    filter_upwards [hU.mem_nhds (by simp [hρ0, hρ1])] with s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    exact riemannZeta_eq_xiZeta_mul hs.1 hs.2
  have hfac : zetaXiFactor ρ ≠ 0 := by
    have hd : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
    simp [zetaXiFactor, Gammaℝ_ne_zero_of_re_pos h0, hd]
  have hord : analyticOrderAt zetaXiFactor ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hfac)
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hev,
    analyticOrderAt_mul (differentiable_xiZeta.analyticAt ρ) (analyticAt_zetaXiFactor hρ0 hρ1),
    hord, add_zero]

/-- The bijection between the two zero sets. -/
def zerosEquiv : Cramer.NontrivialZeros ≃ Zeros where
  toFun ρ := ⟨ρ, xiZeta_eq_zero_of_mem ρ.2.1 ρ.2.2.1 ρ.2.2.2⟩
  invFun ρ := ⟨ρ, mem_strip_of_xiZeta_eq_zero ρ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `cramerTerm ρ = m_ρ² ‖1/ρ‖²`, with erdos-233's multiplicity. -/
lemma cramerTerm_eq (ρ : Cramer.NontrivialZeros) :
    Cramer.cramerTerm ρ = ‖(mult (zerosEquiv ρ) : ℂ) * (1 / ((zerosEquiv ρ : Zeros) : ℂ))‖ ^ 2 := by
  have hm : analyticOrderNatAt riemannZeta (ρ : ℂ) = mult (zerosEquiv ρ) :=
    analyticOrderNatAt_riemannZeta_eq_xiZeta ρ.2.1 ρ.2.2.1
  rw [Cramer.cramerTerm, hm, norm_mul, Complex.norm_natCast, norm_div, norm_one, mul_pow,
    div_pow, one_pow, mul_one_div]
  rfl

end Cramer.MeanSq
