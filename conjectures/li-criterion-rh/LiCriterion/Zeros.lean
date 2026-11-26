import LiCriterion.Statement
import Erdos985.Analytic.Principal.Identity.Zeros

/-!
# The nontrivial zeros of ζ: summability of `Σ 1/|ρ|²` and unboundedness

Both results are unconditional.

* `summable_inv_sq_nontrivialPosZeros`: `Σ_{ρ ∈ nontrivialPosZeros} ‖ρ‖⁻² < ∞`, from erdos-985's
  Hadamard theorem for `ξ = xiZeta` (`hadamard_logDeriv`, order ≤ 1).
* `exists_nontrivialPosZeros_norm_gt`: for every `R` there is `ρ ∈ nontrivialPosZeros` with
  `R < ‖ρ‖`, i.e. ζ has infinitely many nontrivial zeros. If all zeros were bounded, there would
  be finitely many (they have summable `‖ρ‖⁻²`), so the genus-one Hadamard product would give
  `‖ξ(x)‖ ≤ exp(A + B|x|)`, while `ξ(2n+2) ≥ n! / π^(n+1)` grows faster than any exponential.
-/

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux Complex.Hadamard
open scoped ComplexConjugate

namespace RiemannHypothesis

lemma xiZeta_ne_zero_at_zero : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; exact one_ne_zero

/-- A zero of `ζ` in the critical strip is a zero of `ξ`. -/
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

/-- A zero of `ξ` is a zero of `ζ` in the critical strip. -/
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

/-- `Σ_{ρ ∈ nontrivialPosZeros} ‖ρ‖⁻² < ∞`. -/
theorem summable_inv_sq_nontrivialPosZeros :
    Summable fun ρ : nontrivialPosZeros => ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
  have hs := (hadamard_logDeriv differentiable_xiZeta xiZeta_ne_zero_at_zero xiZeta_growth).1 1
    one_pos
  -- drop the multiplicities (each is ≥ 1)
  have hs' : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => ‖(ρ : ℂ)‖⁻¹ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_) hs
    have hm : (1 : ℝ) ≤ analyticOrderNatAt xiZeta ρ := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xiZeta_order_ne_zero ρ.2)
    have : ‖(ρ : ℂ)‖ ^ ((1 : ℝ) + 1) = ‖(ρ : ℂ)‖ ^ 2 := by
      rw [show (1 : ℝ) + 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    rw [this, inv_pow, div_eq_mul_inv]
    exact le_mul_of_one_le_left (by positivity) hm
  let e : nontrivialPosZeros → {ρ : ℂ // xiZeta ρ = 0} := fun ρ =>
    ⟨ρ.1, xiZeta_eq_zero_of_mem ρ.2.1 ρ.2.2.1 ρ.2.2.2.2⟩
  have he : Function.Injective e := fun a b h => by
    have h' : (e a).1 = (e b).1 := congrArg Subtype.val h
    exact Subtype.ext h'
  have := hs'.comp_injective he
  exact this

/-- `ζ(x) ≥ 1` in real part for real `x > 1`. -/
lemma one_le_re_riemannZeta {x : ℝ} (hx : 1 < x) : 1 ≤ (riemannZeta x).re := by
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have h := Complex.hasSum_re (LSeriesHasSum_one hx')
  have hterm : ∀ n : ℕ, (LSeries.term (1 : ℕ → ℂ) (x : ℂ) n).re =
      if n = 0 then 0 else ((n : ℝ) ^ x)⁻¹ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]; simp only [hn, ↓reduceIte]
      have : ((n : ℂ) ^ (x : ℂ)) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
      rw [Pi.one_apply, this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re,
        one_div]
  have h1 := le_hasSum h 1 (fun j _ => by rw [hterm]; split_ifs <;> positivity)
  simpa [hterm] using h1

/-- `‖ξ(2n+2)‖ ≥ n! / π^(n+1)`. -/
lemma factorial_div_le_norm_xiZeta (n : ℕ) :
    (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤ ‖xiZeta (2 * n + 2)‖ := by
  set s : ℂ := 2 * n + 2 with hs
  have hsre : s.re = 2 * n + 2 := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hsx : s = ((2 * n + 2 : ℝ) : ℂ) := by simp [hs]
  have hΓ : Gammaℝ s = ((Real.pi ^ (n + 1))⁻¹ * n.factorial : ℝ) := by
    rw [Gammaℝ, show s / 2 = (n : ℂ) + 1 by rw [hs]; ring, Complex.Gamma_nat_eq_factorial,
      show -s / 2 = -(((n + 1 : ℕ) : ℂ)) by rw [hs]; push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]
    push_cast; ring
  have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _
      (Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; positivity))]
  have hpos : 0 ≤ (Real.pi ^ (n + 1))⁻¹ * (n.factorial : ℝ) := by positivity
  rw [xiZeta_eq hs0 hs1, hΛ, hΓ, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hpos]
  have hζ : 1 ≤ ‖riemannZeta s‖ := by
    rw [hsx]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact (one_le_re_riemannZeta (by linarith)).trans (Complex.re_le_norm _)
  have hs_ge : 1 ≤ ‖s‖ := by
    rw [hsx, Complex.norm_real, Real.norm_of_nonneg (by positivity)]; linarith
  have hs1_ge : 1 ≤ ‖s - 1‖ := by
    have : s - 1 = ((2 * n + 1 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]; linarith
  calc (n.factorial : ℝ) / Real.pi ^ (n + 1)
      = 1 * 1 * ((Real.pi ^ (n + 1))⁻¹ * n.factorial) * 1 := by ring
    _ ≤ ‖s‖ * ‖s - 1‖ * ((Real.pi ^ (n + 1))⁻¹ * n.factorial) * ‖riemannZeta s‖ := by
        gcongr
    _ = _ := by ring

/-- `‖E₁(u)‖ ≤ exp (2‖u‖)` for the genus-one Weierstrass factor `E₁(u) = (1 - u) eᵘ`. -/
lemma norm_weierstrassFactor_one_le (u : ℂ) :
    ‖weierstrassFactor 1 u‖ ≤ Real.exp (2 * ‖u‖) := by
  rw [weierstrassFactor_def, partialLogSum_eq_sum]
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one]
  rw [norm_mul, Complex.norm_exp]
  have h1 : ‖1 - u‖ ≤ Real.exp ‖u‖ := by
    calc ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
      _ = ‖u‖ + 1 := by simp [add_comm]
      _ ≤ Real.exp ‖u‖ := Real.add_one_le_exp _
  have h2 : Real.exp u.re ≤ Real.exp ‖u‖ := Real.exp_le_exp.mpr (Complex.re_le_norm u)
  calc ‖1 - u‖ * Real.exp u.re ≤ Real.exp ‖u‖ * Real.exp ‖u‖ :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ‖u‖) := by rw [← Real.exp_add]; ring_nf

/-- If the zeros of `ξ` are bounded, then `ξ` grows at most exponentially on the reals. -/
lemma exp_bound_of_bounded_zeros {R : ℝ} (hR : 0 < R)
    (hbd : ∀ ρ : ℂ, xiZeta ρ = 0 → ‖ρ‖ ≤ R) :
    ∃ A B : ℝ, ∀ z : ℂ, ‖xiZeta z‖ ≤ Real.exp (A + B * ‖z‖) := by
  classical
  have hord := HadamardAux.entireOfOrderAtMost_one differentiable_xiZeta xiZeta_ne_zero_at_zero
    xiZeta_growth
  have hnot : ∃ z, xiZeta z ≠ 0 := ⟨0, xiZeta_ne_zero_at_zero⟩
  have hsum2 : Summable (fun p : divisorZeroIndex₀ xiZeta Set.univ =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
    simpa [Nat.floor_one] using hord.summable_norm_inv_pow_divisorZeroIndex₀ (by norm_num) hnot
  -- every term is at least `R⁻²`, so the index is finite
  have hfin : Finite (divisorZeroIndex₀ xiZeta Set.univ) := by
    have ht := hsum2.tendsto_cofinite_zero
    have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < (R⁻¹) ^ 2 by positivity))
    rw [Filter.eventually_cofinite] at hev
    refine Set.finite_univ_iff.mp (hev.subset fun p _ => ?_)
    simp only [Set.mem_ofPred_eq, not_lt]
    have hp := hbd _ (HadamardAux.val_isZero differentiable_xiZeta p)
    have hp0 : 0 < ‖divisorZeroIndex₀_val p‖ := norm_pos_iff.mpr (divisorZeroIndex₀_val_ne_zero p)
    gcongr
  have _ : Fintype (divisorZeroIndex₀ xiZeta Set.univ) := Fintype.ofFinite _
  obtain ⟨P, hdeg, hfac⟩ := hadamard_factorization_of_order (by norm_num : (0 : ℝ) ≤ 1) hnot hord
  have h0 : analyticOrderNatAt xiZeta 0 = 0 := by
    by_contra h
    exact xiZeta_ne_zero_at_zero (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  have hdeg' : P.degree ≤ 1 := by simpa [Nat.floor_one] using hdeg
  set S : ℝ := ∑ p : divisorZeroIndex₀ xiZeta Set.univ, ‖divisorZeroIndex₀_val p‖⁻¹
  refine ⟨‖P.coeff 0‖, ‖P.coeff 1‖ + 2 * S, fun z => ?_⟩
  rw [hfac z, h0, pow_zero, mul_one, Nat.floor_one, divisorCanonicalProduct, tprod_fintype,
    norm_mul, norm_prod]
  have hP : ‖Complex.exp (P.eval z)‖ ≤ Real.exp (‖P.coeff 0‖ + ‖P.coeff 1‖ * ‖z‖) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    have heval : P.eval z = P.coeff 1 * z + P.coeff 0 := by
      conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg']
      simp
    rw [heval]
    calc ‖P.coeff 1 * z + P.coeff 0‖ ≤ ‖P.coeff 1 * z‖ + ‖P.coeff 0‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul]; ring
  have hG : ∏ p : divisorZeroIndex₀ xiZeta Set.univ,
      ‖weierstrassFactor 1 (z / divisorZeroIndex₀_val p)‖ ≤ Real.exp (2 * S * ‖z‖) := by
    calc ∏ p : divisorZeroIndex₀ xiZeta Set.univ,
          ‖weierstrassFactor 1 (z / divisorZeroIndex₀_val p)‖
        ≤ ∏ p : divisorZeroIndex₀ xiZeta Set.univ,
            Real.exp (2 * (‖divisorZeroIndex₀_val p‖⁻¹ * ‖z‖)) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => ?_)
          refine (norm_weierstrassFactor_one_le _).trans_eq ?_
          rw [norm_div, div_eq_inv_mul]
      _ = Real.exp (2 * S * ‖z‖) := by
          rw [← Real.exp_sum, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  calc ‖Complex.exp (P.eval z)‖ * ∏ p : divisorZeroIndex₀ xiZeta Set.univ,
        ‖weierstrassFactor 1 (z / divisorZeroIndex₀_val p)‖
      ≤ Real.exp (‖P.coeff 0‖ + ‖P.coeff 1‖ * ‖z‖) * Real.exp (2 * S * ‖z‖) :=
        mul_le_mul hP hG (by positivity) (by positivity)
    _ = Real.exp (‖P.coeff 0‖ + (‖P.coeff 1‖ + 2 * S) * ‖z‖) := by
        rw [← Real.exp_add]; ring_nf

/-- `ξ` does not grow at most exponentially along `2n + 2`. -/
lemma not_exp_bound (A B : ℝ) : ¬ ∀ z : ℂ, ‖xiZeta z‖ ≤ Real.exp (A + B * ‖z‖) := by
  intro h
  set c : ℝ := Real.pi * Real.exp (2 * |B|)
  set K : ℝ := Real.pi * Real.exp (A + 2 * |B|)
  have hK : 0 < K := by positivity
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop c
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (inv_pos.mpr hK))).exists
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hlow := factorial_div_le_norm_xiZeta n
  have hup := h (2 * n + 2)
  have hz : ‖(2 * n + 2 : ℂ)‖ = 2 * n + 2 := by
    have : (2 * n + 2 : ℂ) = ((2 * n + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hz] at hup
  -- `n! ≤ π^(n+1) exp(A + B(2n+2)) ≤ K cⁿ`
  have hB : B * (2 * n + 2) ≤ |B| * (2 * n + 2) :=
    mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
  have h1 : (n.factorial : ℝ) ≤ Real.pi ^ (n + 1) * Real.exp (A + |B| * (2 * n + 2)) := by
    have hπ : 0 < Real.pi ^ (n + 1) := by positivity
    have := hlow.trans (hup.trans (Real.exp_le_exp.mpr
      (show A + B * (2 * n + 2) ≤ A + |B| * (2 * n + 2) by linarith)))
    rwa [div_le_iff₀ hπ, mul_comm] at this
  have h2 : Real.pi ^ (n + 1) * Real.exp (A + |B| * (2 * n + 2)) = K * c ^ n := by
    simp only [K, c, mul_pow, ← Real.exp_nat_mul, pow_succ]
    rw [show A + |B| * (2 * n + 2) = (A + 2 * |B|) + n * (2 * |B|) by ring, Real.exp_add]
    ring
  rw [h2] at h1
  have := (div_lt_iff₀ hfac).mp hn
  rw [inv_mul_eq_div, lt_div_iff₀ hK] at this
  nlinarith

/-- **ζ has infinitely many nontrivial zeros**: for every `R` there is a nontrivial zero `ρ` with
`Im ρ > 0` and `‖ρ‖ > R`. -/
theorem exists_nontrivialPosZeros_norm_gt (R : ℝ) :
    ∃ ρ ∈ nontrivialPosZeros, R < ‖ρ‖ := by
  by_contra hcon
  push Not at hcon
  set R' := max R 1
  have hbd : ∀ ρ : ℂ, xiZeta ρ = 0 → ‖ρ‖ ≤ R' := by
    intro ρ hρ
    obtain ⟨h0, h1, hζ⟩ := mem_strip_of_xiZeta_eq_zero hρ
    rcases lt_trichotomy ρ.im 0 with him | him | him
    · have hc : conj ρ ∈ nontrivialPosZeros :=
        ⟨by simpa using h0, by simpa using h1, by simpa using him,
          by rw [riemannZeta_conj, hζ, map_zero]⟩
      have := hcon _ hc
      rw [Complex.norm_conj] at this
      exact this.trans (le_max_left _ _)
    · have : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [this, Complex.norm_real, Real.norm_of_nonneg h0.le]
      exact h1.le.trans (le_max_right _ _)
    · exact (hcon ρ ⟨h0, h1, him, hζ⟩).trans (le_max_left _ _)
  obtain ⟨A, B, hAB⟩ := exp_bound_of_bounded_zeros (lt_of_lt_of_le one_pos (le_max_right R 1)) hbd
  exact not_exp_bound A B hAB

end RiemannHypothesis
