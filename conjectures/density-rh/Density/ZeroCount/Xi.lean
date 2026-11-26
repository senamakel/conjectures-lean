import Density.ZeroCount.Jensen
import Erdos985.Analytic.XiGrowth

/-!
# Zeros of `ζ` and of `ξ` have the same multiplicities right of `-2`

`Erdos985.Analytic.xiZeta s = s (s - 1) Λ(s)` is entire. Near any `ρ ≠ 0, 1` we have
`ζ = xiZeta · h` with `h s = Γℝ(s)⁻¹ / (s (s - 1))` analytic, and `h ρ ≠ 0` unless `ρ` is a trivial
zero `-2n`. At `ρ = 0, 1` both orders are `0` (`ζ(0) = -1/2`, `ζ` is not analytic at the pole,
`xiZeta 0 = xiZeta 1 = 1`).
-/

open Complex Filter Topology

namespace Density

open Erdos985.Analytic

lemma xiZeta_one : xiZeta 1 = 1 := by simp [xiZeta]

/-- `ζ` is not analytic at its pole. -/
lemma not_analyticAt_riemannZeta_one : ¬ AnalyticAt ℂ riemannZeta 1 := by
  intro h
  have hc : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 ((1 - 1) * riemannZeta 1)) :=
    ((continuousAt_id.sub continuousAt_const).mul h.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have := tendsto_nhds_unique hc riemannZeta_residue_one
  simp at this

lemma analyticOrderNatAt_riemannZeta_one : analyticOrderNatAt riemannZeta 1 = 0 := by
  simp [analyticOrderNatAt, analyticOrderAt_of_not_analyticAt not_analyticAt_riemannZeta_one]

lemma analyticAt_xiZeta (z : ℂ) : AnalyticAt ℂ xiZeta z :=
  differentiable_xiZeta.analyticAt z

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

/-- Away from the trivial zeros, `ζ` and `ξ` vanish to the same order. -/
theorem analyticOrderNatAt_riemannZeta_eq_xiZeta {ρ : ℂ} (hρ : -2 < ρ.re) :
    analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt xiZeta ρ := by
  by_cases h1 : ρ = 1
  · subst h1
    rw [analyticOrderNatAt_riemannZeta_one,
      Complex.analyticOrderNatAt_eq_zero_of_ne_zero (by rw [xiZeta_one]; exact one_ne_zero)]
  by_cases h0 : ρ = 0
  · subst h0
    rw [Complex.analyticOrderNatAt_eq_zero_of_ne_zero (by rw [riemannZeta_zero]; norm_num),
      Complex.analyticOrderNatAt_eq_zero_of_ne_zero (by rw [xiZeta_zero]; exact one_ne_zero)]
  have hΓ : Gammaℝ ρ ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, rfl⟩
    rcases n with _ | n
    · simp at h0
    · simp at hρ; linarith
  have hev : riemannZeta =ᶠ[𝓝 ρ] xiZeta * zetaXiFactor := by
    have hU : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
    filter_upwards [hU.mem_nhds (by simp [h0, h1])] with s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    exact riemannZeta_eq_xiZeta_mul hs.1 hs.2
  have hfac : zetaXiFactor ρ ≠ 0 := by
    have hd : ρ * (ρ - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
    simp [zetaXiFactor, hΓ, hd]
  have hord : analyticOrderAt zetaXiFactor ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hfac)
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hev,
    analyticOrderAt_mul (analyticAt_xiZeta ρ) (analyticAt_zetaXiFactor h0 h1), hord, add_zero]

/-- Counting zeros of `ζ` or of `ξ` in a set right of `Re s = -2` gives the same number. -/
theorem zeroCountOn_riemannZeta_eq_xiZeta {S : Set ℂ} (hS : ∀ s ∈ S, -2 < s.re) :
    zeroCountOn riemannZeta S = zeroCountOn xiZeta S := by
  unfold zeroCountOn
  exact finsum_mem_congr rfl fun s hs => analyticOrderNatAt_riemannZeta_eq_xiZeta (hS s hs)

end Density
