import Lindelof.DirichletBounds

/-!
# Lindelöf for Dirichlet L-functions in the `t`-aspect, from GRH

The same argument as for `ζ` (Steps 1–8 of `docs/BLUEPRINT.md`), run through the generic
`LogBounds` interface (`Lindelof/Main.lean`):

* `χ = 1` (any modulus): `L(s, 1) = ∏_{p ∣ N} (1 - p^{-s}) ζ(s)`, and `ζ` is handled by
  `lindelof_of_RH`, with RH obtained from GRH at modulus 1 (`riemannHypothesis_of_GRH`).
* `χ ≠ 1`: `χ` is induced by the primitive `χ' = χ.primitiveCharacter ≠ 1`, and
  `L(s, χ) = L(s, χ') ∏_{p ∣ N} (1 - χ'(p) p^{-s})` (`LFunction_changeLevel`). The finite Euler
  product is at most `2^{ω(N)}` on `σ = 1/2`, and `L(·, χ')` is handled by
  `lindelof_LFunction_of_primitive` (`Lindelof/DirichletBounds.lean`), where `ξ` is replaced by
  the completed L-function `Λ(s, χ')`.
-/

namespace Lindelof

open Complex Erdos985 Erdos985.Analytic Erdos985.Analytic.PrincipalAux DirichletCharacter Filter
  Asymptotics

/-- GRH at modulus `1` gives Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    RiemannHypothesis := by
  intro s hs htriv hs1
  apply xiZeta_zero_re' hGRH
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
  have hΓ : Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
    rcases n with _ | n
    · exact hs0 (by simpa using hn)
    · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
  have hΛ : completedRiemannZeta s = 0 := by
    have := riemannZeta_def_of_ne_zero hs0
    rw [hs, eq_comm, div_eq_zero_iff] at this
    exact this.resolve_right hΓ
  rw [xiZeta_eq hs0 hs1, hΛ, mul_zero]

/-- A finite Euler product with coefficients of norm `≤ 1` is at most `2^{#S}` on `σ ≥ 0`. -/
theorem norm_prod_one_sub_le (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) (c : ℕ → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ S, (1 - c p * (p : ℂ) ^ (-s))‖ ≤ 2 ^ S.card := by
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p hp => ?_
  have hp : 0 < p := Nat.pos_of_ne_zero (hS p hp)
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_natCast_cpow_of_pos hp, neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by linarith)
  calc ‖1 - c p * (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖c p * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 * 1 := by
        rw [norm_one, norm_mul]
        gcongr
        · exact hc p
    _ = 2 := by norm_num

/-- `(1/2 + it)` has real part `1/2`. -/
lemma re_half_add (t : ℝ) : (1 / 2 + t * I : ℂ).re = 1 / 2 := by simp

/-- GRH for Dirichlet L-functions implies the Lindelöf hypothesis for them. -/
theorem dirichletLindelof_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    DirichletLindelofHypothesis := by
  intro N _ χ ε hε
  have hne1 : ∀ t : ℝ, (1 / 2 + t * I : ℂ) ≠ 1 := fun t h => by
    have := congrArg re h; rw [re_half_add] at this; norm_num at this
  have hprimes : ∀ p ∈ N.primeFactors, p ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  by_cases hχ : χ = 1
  · subst hχ
    have hζ := lindelof_of_RH (riemannHypothesis_of_GRH hGRH) ε hε
    refine IsBigO.trans ?_ hζ
    refine IsBigO.of_bound (2 ^ N.primeFactors.card) (Eventually.of_forall fun t => ?_)
    have hT := LFunctionTrivChar_eq_mul_riemannZeta (N := N) (hne1 t)
    unfold LFunctionTrivChar at hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm, hT, norm_mul]
    gcongr
    have h := norm_prod_one_sub_le N.primeFactors hprimes (fun _ => 1) (fun _ => by simp)
      (s := 1 / 2 + t * I) (by rw [re_half_add]; norm_num)
    simpa using h
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    set χ' := χ.primitiveCharacter with hχ'def
    have hχ' : χ' ≠ 1 := by
      intro h
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, ← hχ'def, h, changeLevel_one]
    have hL := lindelof_LFunction_of_primitive hGRH χ.primitiveCharacter_isPrimitive hχ' hε
    refine IsBigO.trans ?_ hL
    refine IsBigO.of_bound (2 ^ N.primeFactors.card) (Eventually.of_forall fun t => ?_)
    have hcl := LFunction_changeLevel χ.conductor_dvd_level χ' (s := 1 / 2 + t * I) (Or.inl hχ')
    rw [hχ'def, χ.changeLevel_primitiveCharacter, ← hχ'def] at hcl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_norm, hcl, norm_mul, mul_comm]
    gcongr
    exact norm_prod_one_sub_le N.primeFactors hprimes (fun p => χ' p)
      (fun p => DirichletCharacter.norm_le_one χ' p) (by rw [re_half_add]; norm_num)

end Lindelof
