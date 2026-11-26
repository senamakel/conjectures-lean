import Mathlib

/-!
# `−ζ'/ζ(s) − 1/(s − 1) → −γ` as `s → 1⁺`

With `ζ(s) = (s − 1)⁻¹ ζ₁(s)` (Mathlib's entire `riemannZeta₁`, `ζ₁(1) = 1`, `ζ₁'(1) = γ`),
`−ζ'/ζ = (s − 1)⁻¹ − ζ₁'/ζ₁`, and `ζ₁'/ζ₁` is continuous at `1`. For real `s > 1`,
`Σ Λ(n) n^{−s} = −ζ'(s)/ζ(s)`.
-/

namespace LLS.Sharp.Principal

open Filter Topology Real ArithmeticFunction

/-- `Σ_n Λ(n) n^{−s}` for real `s`. -/
noncomputable def Lr (s : ℝ) : ℝ := ∑' n : ℕ, (Λ n : ℝ) * (n : ℝ) ^ (-s)

lemma term_eq_ofReal {s : ℝ} (n : ℕ) :
    LSeries.term (fun n => (Λ n : ℂ)) (s : ℂ) n = (((Λ n : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hn0, Complex.ofReal_neg, Complex.ofReal_natCast,
    Complex.cpow_neg, div_eq_mul_inv]

lemma summable_Lr {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => (Λ n : ℝ) * (n : ℝ) ^ (-s) := by
  have h := LSeriesSummable_vonMangoldt (s := (s : ℂ)) (by simpa using hs)
  have h2 : Summable fun n : ℕ => (((Λ n : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    refine h.congr fun n => ?_
    exact term_eq_ofReal n
  exact Complex.summable_ofReal.mp h2

lemma Lr_eq {s : ℝ} (hs : 1 < s) :
    (Lr s : ℂ) = -deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs),
    LSeries, Lr, Complex.ofReal_tsum]
  exact tsum_congr fun n => (term_eq_ofReal n).symm

lemma neg_logDeriv_zeta_eq {s : ℂ} (hs : s ≠ 1) (h1 : riemannZeta₁ s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹
      = -(deriv riemannZeta₁ s / riemannZeta₁ s) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring

theorem tendsto_neg_logDeriv_zeta :
    Tendsto (fun s : ℂ => -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹) (𝓝[≠] 1)
      (𝓝 (-Real.eulerMascheroniConstant : ℂ)) := by
  have hc : ContinuousAt (fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s)) 1 :=
    (differentiable_riemannZeta₁.deriv.continuous.continuousAt.div
      differentiable_riemannZeta₁.continuous.continuousAt (by simp)).neg
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  simp only [deriv_riemannZeta₁_one, riemannZeta₁_one, div_one] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds riemannZeta₁_ne_zero_of_near_one] with s hs h1
  exact (neg_logDeriv_zeta_eq hs h1).symm

/-- `Σ Λ(n) n^{−s} − 1/(s − 1) → −γ` as `s → 1⁺`. -/
theorem tendsto_Lr_sub :
    Tendsto (fun s : ℝ => Lr s - 1 / (s - 1)) (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := Complex.continuous_ofReal.tendsto (1:ℝ)
      rw [Complex.ofReal_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs : (1:ℝ) < s := hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast hs.ne'
  have h2 := (Complex.continuous_re.tendsto _).comp (tendsto_neg_logDeriv_zeta.comp h1)
  simp only [Complex.neg_re, Complex.ofReal_re] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : (1:ℝ) < s := hs
  simp only [Function.comp_apply]
  rw [← Lr_eq hs]
  have : ((s : ℂ) - 1)⁻¹ = ((1 / (s - 1) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_sub, Complex.ofReal_re]

end LLS.Sharp.Principal
