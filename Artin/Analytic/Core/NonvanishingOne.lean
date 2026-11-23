import Artin.Analytic.Core.VonMangoldt

/-!
# `ζ_K` has no zeros on `Re s = 1`

For `D : ContinuationData K`, `D.Z(1 + it) ≠ 0` for `t ≠ 0` (`ContinuationData.Z_ne_zero_on_one_line`),
by Mertens' argument, adapted from Mathlib's proof for Dirichlet `L`-functions
(`DirichletCharacter.LFunction_ne_zero_of_re_eq_one` in `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`):

* `one_le_norm_dedekindZeta_comb`: `|ζ_K(1+x)³ ζ_K(1+x+iy)⁴ ζ_K(1+x+2iy)| ≥ 1` for `x > 0`, since
  `ζ_K = exp(∑ Λ_K(n)/log n · n^{-s})` (`dedekindZeta_eq_exp`) has non-negative coefficients and
  `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0` (`re_term_comb_nonneg`);
* as `x → 0⁺`, `ζ_K(1+x) = O(1/x)` (Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`), `Z(1+x+iy) = O(x)` if `Z(1+iy) = 0`, and
  `Z(1+x+2iy) = O(1)` (`Z` is holomorphic off `1`), so the product would be `O(x)`.
-/

namespace Artin.Analytic

open NumberField

variable (K : Type*) [Field K] [NumberField K]

section LSeries

open Filter Topology Complex Asymptotics

variable {K} in
/-- `Re(3 a n^{-σ} + 4 a n^{-σ-it} + a n^{-σ-2it}) = a n^{-σ} (3 + 4 cos θ + cos 2θ) ≥ 0`. -/
lemma re_term_comb_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (σ t : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun n => (c n : ℂ)) σ n +
      4 * LSeries.term (fun n => (c n : ℂ)) (σ + I * t) n +
      LSeries.term (fun n => (c n : ℂ)) (σ + 2 * I * t) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  set u := (n : ℂ) ^ (I * t) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have h1 : (n : ℂ) ^ ((σ : ℂ) + I * t) = (n : ℂ) ^ (σ : ℂ) * u := cpow_add _ _ hn'
  have h2 : (n : ℂ) ^ ((σ : ℂ) + 2 * I * t) = (n : ℂ) ^ (σ : ℂ) * u ^ 2 := by
    rw [cpow_add _ _ hn', show (2 : ℂ) * I * t = (2 : ℕ) * (I * t) by push_cast; ring,
      cpow_nat_mul]
  have h0 : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl
  have hpos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ
  set R : ℝ := c n / (n : ℝ) ^ σ
  have hR : 0 ≤ R := div_nonneg (hc n) hpos.le
  set v := u⁻¹
  have hv : ‖v‖ = 1 := by rw [norm_inv, hu, inv_one]
  have e : 3 * ((c n : ℂ) / (n : ℂ) ^ (σ : ℂ)) + 4 * ((c n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + I * t)) +
      (c n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 2 * I * t) = (R : ℂ) * (3 + 4 * v + v * v) := by
    have hp0 : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    rw [h1, h2, h0]
    simp only [R, v]
    push_cast
    field_simp
  rw [e, re_ofReal_mul]
  apply mul_nonneg hR
  have hv2 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have := Complex.sq_norm v
    rw [hv, Complex.normSq_apply] at this
    nlinarith
  simp only [add_re, mul_re, re_ofNat, im_ofNat]
  nlinarith [sq_nonneg (1 + v.re)]

/-- **Mertens' inequality** for `ζ_K`: `|ζ_K(1+x)³ ζ_K(1+x+iy)⁴ ζ_K(1+x+2iy)| ≥ 1` for `x > 0`,
since `log ζ_K` has non-negative coefficients and `3 + 4 cos θ + cos 2θ ≥ 0`. -/
theorem one_le_norm_dedekindZeta_comb {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖dedekindZeta K (1 + x) ^ 3 * dedekindZeta K (1 + x + I * y) ^ 4 *
      dedekindZeta K (1 + x + 2 * I * y)‖ := by
  have e : (1 + x : ℂ) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
  have h0 : 1 < (((1 + x : ℝ) : ℂ)).re := by simp; linarith
  have h1 : 1 < (((1 + x : ℝ) : ℂ) + I * y).re := by simp; linarith
  have h2 : 1 < (((1 + x : ℝ) : ℂ) + 2 * I * y).re := by simp; linarith
  rw [e, dedekindZeta_eq_exp K h0, dedekindZeta_eq_exp K h1, dedekindZeta_eq_exp K h2]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, Real.one_le_exp_iff]
  have S0 := LSeriesSummable_logZetaCoeff K h0
  have S1 := LSeriesSummable_logZetaCoeff K h1
  have S2 := LSeriesSummable_logZetaCoeff K h2
  simp only [logDedekindZeta, LSeries]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (S0.mul_left 3).tsum_add (S1.mul_left 4),
    ← ((S0.mul_left 3).add (S1.mul_left 4)).tsum_add S2,
    re_tsum (((S0.mul_left 3).add (S1.mul_left 4)).add S2)]
  exact tsum_nonneg fun n => re_term_comb_nonneg (logZetaCoeff_nonneg K) _ _ n

end LSeries

/-! ### Non-vanishing on `Re s = 1` -/

section NonvanishingOne

open Filter Topology Complex Asymptotics ArtinPrimitiveRootsConjecture

variable {K}

namespace ContinuationData

variable (D : ContinuationData K)

lemma Z_isBigO_near_one :
    (fun x : ℝ => D.Z (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have hres := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hmap : Tendsto (fun x : ℝ => 1 + x) (𝓝[>] 0) (𝓝[>] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun x : ℝ => 1 + x) (𝓝 0) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx ⊢; linarith
  have h : Tendsto (fun x : ℝ => (x : ℂ) * D.Z (1 + x)) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
    refine (hres.comp hmap).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < ((1 : ℂ) + x).re := by simp; exact hx
    simp only [Function.comp_apply]
    push_cast
    rw [D.isDedekindZeta.2 _ hx']
    ring
  have he : (fun x : ℝ => D.Z (1 + x)) =ᶠ[𝓝[>] 0]
      fun x => ((x : ℂ) * D.Z (1 + x)) * (1 / x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx)
    field_simp
  refine he.trans_isBigO ?_
  simpa using (h.isBigO_one ℂ).mul (isBigO_refl (fun x : ℝ => (1 : ℂ) / x) _)

lemma Z_isBigO_horizontal {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ => D.Z (1 + x + I * y)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have hne : 1 + I * y ≠ 1 := by
    simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
      using hy
  have := (D.isDedekindZeta.1.differentiableAt (isOpen_compl_singleton.mem_nhds hne)).continuousAt
  rw [← zero_add (1 + _)] at this
  exact this.comp (f := fun x : ℝ => x + (1 + I * y)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

lemma Z_isBigO_horizontal_of_eq_zero {y : ℝ} (hy : y ≠ 0) (h : D.Z (1 + I * y) = 0) :
    (fun x : ℝ => D.Z (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have hne : 1 + I * y ≠ 1 := by
    simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
      using hy
  have := (D.isDedekindZeta.1.differentiableAt (isOpen_compl_singleton.mem_nhds hne)).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

/-- **`ζ_K(1 + it) ≠ 0` for `t ≠ 0`**, by Mertens' argument (adapted from Mathlib's proof for
Dirichlet `L`-functions, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`). -/
theorem Z_ne_zero_on_one_line {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1) : D.Z s ≠ 0 := by
  have hs' : s = 1 + I * s.im := by
    conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
  set y := s.im
  have hy : y ≠ 0 := by
    intro h; apply hs1; rw [hs', h]; simp
  have hy2 : 2 * y ≠ 0 := mul_ne_zero two_ne_zero hy
  rw [hs']
  intro Hz
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by lia), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ D.Z (1 + x) ^ 3 * D.Z (1 + x + I * y) ^ 4 * D.Z (1 + x + 2 * I * y) := by
    refine IsBigO.of_bound' <| eventually_nhdsWithin_of_forall fun x hx => ?_
    have hx : (0 : ℝ) < x := hx
    have h0 : 1 < ((1 : ℂ) + x).re := by simp; linarith
    have h1 : 1 < ((1 : ℂ) + x + I * y).re := by simp; linarith
    have h2 : 1 < ((1 : ℂ) + x + 2 * I * y).re := by simp; linarith
    rw [norm_one, D.isDedekindZeta.2 _ h0, D.isDedekindZeta.2 _ h1, D.isDedekindZeta.2 _ h2]
    exact one_le_norm_dedekindZeta_comb K hx y
  have H2 := D.Z_isBigO_horizontal (y := 2 * y) hy2
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc] at H2
  have H := (D.Z_isBigO_near_one.pow 3).mul ((D.Z_isBigO_horizontal_of_eq_zero hy Hz).pow 4)
    |>.mul H2
  simp only [help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

end ContinuationData

end NonvanishingOne

end Artin.Analytic
