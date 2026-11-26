import Artin.Analytic.Core.ZeroSum

/-!
# The weighted explicit formula for `ζ_K` (blueprint A3)

For natural `x ≥ 1`, with `W_K(x) = ∑_{n < x} Λ_K(n) (1 - n/x)` (`weightedPsiK`):

`W_K(x) = ∑_ρ m_ρ zeroTerm x ρ + Γ_K(x) + (x/2 + log x - 7/2 + 3/x) - (1 - 1/x) ζ_K'/ζ_K(2)`,

where `zeroTerm` is erdos-985's contribution of one zero and
`Γ_K(x) = r₁ Γ⁰(x) + r₂ (Γ⁰(x) + Γ¹(x))` (`gammaPartK`), `Γᵃ = gammaPartP a`.

The proof is erdos-985's `explicit_formula_zeta` for `ξ_K` in place of Riemann's `ξ`: Perron's
formula for the Cesàro kernel `x^s/(s(s+1))` on `Re s = 2` (`PerronKernel.perron_weighted`),
`-ζ_K'/ζ_K = -(ξ'/ξ - 1/s - 1/(s-1) - G_K)` (`logDeriv_Z_eq`), Hadamard for `ξ_K`
(subtracting the value at `s = 2`, so the Hadamard constant and the constant `½ log |d_K|` of
`G_K` cancel), and the residues at `ρ`, `1` and `0` (`perron_residue`, `perron_residue_zero`).

`explicit_formula_bound`: under RH, `|W_K(x) - x/2| ≤ √x (log |d_K| + 6n) + 4 n (log x + 1) + 6`,
from `zeroSum_le` and erdos-985's `norm_zeroTerm_le`.
-/

namespace Artin.Analytic

open Complex NumberField ArtinPrimitiveRootsConjecture Filter Topology ArithmeticFunction
  MeasureTheory Erdos985.Analytic Erdos985.Analytic.IdentityAux

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- `W_K(x) = ∑_{n < x} Λ_K(n) (1 - n/x)`. -/
noncomputable def weightedPsiK (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range x, vonMangoldtK K n * (1 - (n : ℝ) / x)

variable (K) in
/-- The gamma-factor part of the explicit formula for `ζ_K`:
`Γ_K(x) = r₁ Γ⁰(x) + r₂ (Γ⁰(x) + Γ¹(x))`. -/
noncomputable def gammaPartK (x : ℕ) : ℂ :=
  (InfinitePlace.nrRealPlaces K : ℂ) * gammaPartP 0 x +
    (InfinitePlace.nrComplexPlaces K : ℂ) * (gammaPartP 0 x + gammaPartP 1 x)

lemma vonMangoldtK_zero : vonMangoldtK K 0 = 0 := by
  simp [vonMangoldtK]

/-- The integral form of `Γ_K`: `(1/2π) ∫ (G_K(2+it) - G_K(2)) x^{2+it}/((2+it)(3+it)) dt`. -/
lemma gammaPartK_eq_integral (x : ℕ) (hx : 1 ≤ x) :
    gammaPartK K x = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (gammaLogDerivK K (2 + t * I) - gammaLogDerivK K 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
        / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) := by
  set r₁ : ℂ := (InfinitePlace.nrRealPlaces K : ℂ)
  set r₂ : ℂ := (InfinitePlace.nrComplexPlaces K : ℂ)
  set A : ℕ → ℝ → ℂ := fun a t => (gR a (2 + t * I) - gR a 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hA
  have hfun : (fun t : ℝ => (gammaLogDerivK K (2 + t * I) - gammaLogDerivK K 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t => r₁ * A 0 t + r₂ * (A 0 t + A 1 t) := by
    funext t
    simp only [hA, gammaLogDerivK, r₁, r₂]
    ring
  have h0 : Integrable (A 0) := integrable_gR_part 0 x hx
  have h1 : Integrable (A 1) := integrable_gR_part 1 x hx
  have h01 : Integrable (fun t => A 0 t + A 1 t) := h0.add h1
  rw [hfun, integral_add (f := fun t => r₁ * A 0 t) (g := fun t => r₂ * (A 0 t + A 1 t))
    (h0.const_mul _) (h01.const_mul _), integral_const_mul, integral_const_mul,
    integral_add h0 h1]
  simp only [gammaPartK, gammaPartP, hA, r₁, r₂]
  ring

namespace ContinuationData

variable (D : ContinuationData K)

/-- `∑ Λ_K(n) n^{-s} = -ζ_K'/ζ_K(s)`, with the continuation `Z`. -/
lemma LSeries_vonMangoldtK_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldtK K n : ℂ)) s = -(deriv D.Z s / D.Z s) := by
  have hev : D.Z =ᶠ[𝓝 s] dedekindZeta K := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show s ∈ {w : ℂ | 1 < w.re} from hs)] with w hw
    exact D.Z_eq_dedekindZeta hw
  rw [LSeries_vonMangoldtK K hs, hev.deriv_eq, D.Z_eq_dedekindZeta hs]

/-- **The weighted explicit formula for `ζ_K`.** -/
theorem explicit_formula (x : ℕ) (hx : 1 ≤ x) :
    ((weightedPsiK K x : ℝ) : ℂ)
      = (∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℂ) * zeroTerm x ρ)
        + gammaPartK K x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv D.Z 2 / D.Z 2) := by
  classical
  set G := gammaLogDerivK K with hG
  set Dξ : ℂ → ℂ := fun z => deriv D.ξ z / D.ξ z with hDξ
  set m : {ρ : ℂ // D.ξ ρ = 0} → ℂ := fun ρ => (D.mult ρ : ℂ) with hm
  set c2 : ℂ := deriv D.Z 2 / D.Z 2 with hc2
  have := D.countable_zeros
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ D.ξ := D.differentiable_ξ
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → D.ξ z ≠ 0 := fun z hz => D.xi_ne_zero_of_one_le_re hz
  /- Hadamard -/
  obtain ⟨hsum_ε, b, hb⟩ := D.hadamard
  have hzre : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => D.xi_zero_re_mem ρ.2
  /- The family of zero terms. -/
  let F : {ρ : ℂ // D.ξ ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * pairTerm x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (D.mult ρ : ℝ) * ∫ t, ‖pairTerm x ρ t‖
        ≤ (D.mult ρ : ℝ) * (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ,
      HasSum (fun ρ => F ρ t) ((Dξ ((2 : ℂ) + t * I) - Dξ 2) * kern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (kern x t)
    convert this using 1
    · funext ρ
      simp only [F, m, pairTerm]
      ring
    · simp only [hDξ]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => Dξ ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv D.ξ) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (Dξ ((2 : ℂ) + t * I) - Dξ 2) * kern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (Dξ ((2 : ℂ) + t * I) - Dξ 2) * kern x t
      = ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ρ) := by
    rw [show (fun t : ℝ => (Dξ ((2 : ℂ) + t * I) - Dξ 2) * kern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, integral_pairTerm x hx (by linarith [hzre ρ]) hρ0 hρ1]
  /- Perron. -/
  set a : ℕ → ℂ := fun n => ((vonMangoldtK K n : ℝ) : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (LSeriesSummable_vonMangoldtK K (s := 2) (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.perron_weighted a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(Dξ z - 1 / z - 1 / (z - 1) - G z) :=
    fun z hz => by
      have h1 := D.LSeries_vonMangoldtK_eq hz
      change LSeries a z = _ at h1
      rw [h1, D.logDeriv_Z_eq hz]
  have hc2' : c2 = Dξ 2 - 1 / 2 - 1 / (2 - 1) - G 2 := D.logDeriv_Z_eq (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * kern x t := fun t => by
    simp only [hH, kern, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) := by
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldtK K (s := (3 / 2 : ℂ)) (by norm_num))) ?_
      have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
      rw [this]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) :=
      (LSeries_differentiableOn a).continuousOn.comp_continuous hs_cont
        (fun t => by simp only [Set.mem_ofPred_eq, hsre]; exact_mod_cast hab)
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (LSeriesSummable_vonMangoldtK K (s := 2) (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * kern x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((integrable_kern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_kern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  /- The poles at `0` and `1`. -/
  set P0 : ℝ → ℂ := fun t => ((x : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
    (((2 : ℂ) + t * I - 0) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hP0
  have hP0_int : Integrable P0 := by
    have := perron_residue_integrable (x : ℝ) 2 hx0 two_pos 0 (by simp)
    simp only [ofReal_ofNat] at this
    exact this
  have hP0_integral : ∫ t, P0 t = 2 * Real.pi * ((Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ)) := by
    have h := perron_residue_zero (x : ℝ) 2 hx1 two_pos 0 rfl
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [hP0]
  have hR1_int : Integrable (resKern x 1) := integrable_resKern hx0 (by norm_num)
  have hR1_integral : ∫ t, resKern x 1 t
      = 2 * Real.pi * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)) - 1 / 1 + (x : ℂ) ^ (-1 : ℂ) / (1 + 1)) := by
    have h := perron_residue (x : ℝ) 2 hx1 two_pos 1 (by norm_num) one_ne_zero (by norm_num)
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [resKern]
  /- Decomposition of the gamma part. -/
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (Dξ ((2 : ℂ) + t * I) - Dξ 2) * kern x t - P0 t - resKern x 1 t
          + (c2 + 3 / 2) * kern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    have h0 := line_ne_zero' t
    have h1 := line_add_one_ne_zero' t
    have h2 := line_sub_ne_zero' (ρ := 1) (by norm_num) t
    rw [hH_eq, hLS _ hz, hc2']
    simp only [kern, resKern, hP0, ofReal_natCast, sub_zero]
    field_simp
    ring
  have hgamma : gammaPartK K x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (Dξ ((2 : ℂ) + t * I) - Dξ 2) * kern x t)
        - (∫ t, P0 t) - (∫ t, resKern x 1 t) + (c2 + 3 / 2) * ∫ t, kern x t) := by
    rw [gammaPartK_eq_integral x hx, ← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_sub _ hR1_int, integral_sub _ hP0_int, integral_add hH_int hF1_int,
      integral_const_mul]
    · exact hH_int.add hF1_int
    · exact (hH_int.add hF1_int).sub hP0_int
    · exact ((hH_int.add hF1_int).sub hP0_int).sub hR1_int
  /- Assemble. -/
  have hbach : ((weightedPsiK K x : ℝ) : ℂ) = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    unfold weightedPsiK
    push_cast
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a, vonMangoldtK_zero]
  have hbach' : ((weightedPsiK K x : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTerm x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, m ρ * zeroTerm x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK, hP0_integral, hR1_integral]
  simp only [ofReal_natCast, cpow_one, cpow_neg_one]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  field_simp
  ring

end ContinuationData

end Artin.Analytic
