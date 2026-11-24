import PsiGRH.ZeroSum

/-!
# The bound for a primitive character

Take `T = u` in the truncated explicit formula. Under GRH `|u^ρ/ρ| = √u/|ρ|`, and
`sum_stripZeros_le` bounds `Σ_{|Im ρ| < u} m_ρ/|ρ|` by `≪ log(Nu) log u`. The truncation error
`u log²(Nu²)/u` and the low-zero term are `≪ log²(Nu)`. Result (`psiChar_primitive_bound`):

`|ψ(u, χ) − E₀(χ) u| ≤ A √u (log u)(log Nu) + B log²(Nu)` for primitive `χ` mod `N`, `u ≥ 2`,

with `A = 32 C₂` and `B = C₁ (6 + 32 C₂)`, where `C₁` and `C₂` are the constants of
`TruncatedExplicitFormula` and `ZeroWindowCount`.
-/

namespace PsiGRH

open Complex DirichletCharacter ArithmeticFunction

/-- The trivial bound `|ψ(u, χ)| ≤ u log u`. -/
lemma norm_psiChar_le {N : ℕ} (χ : DirichletCharacter ℂ N) {u : ℝ} (hu : 1 ≤ u) :
    ‖psiChar χ u‖ ≤ u * Real.log u := by
  unfold psiChar
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ‖(Λ n : ℂ) * χ n‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, Real.log u := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
        have h1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
        have hnu : (n : ℝ) ≤ u := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by linarith))
        have h2 : Λ n ≤ Real.log u :=
          vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hnu)
        have h3 : 0 ≤ Λ n := vonMangoldt_nonneg
        calc Λ n * ‖χ n‖ ≤ Λ n * 1 := by gcongr
          _ ≤ Real.log u := by linarith
    _ = (⌊u⌋₊ : ℝ) * Real.log u := by simp
    _ ≤ u * Real.log u :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (Real.log_nonneg hu)

lemma norm_mainTerm_le {N : ℕ} (χ : DirichletCharacter ℂ N) {u : ℝ} (hu : 0 ≤ u) :
    ‖mainTerm χ u‖ ≤ u := by
  unfold mainTerm
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg hu]
  · simpa using hu

/-- The trivial bound `|ψ(u, χ) − E₀(χ) u| ≤ u log u + u`. -/
lemma norm_psiChar_sub_le_trivial {N : ℕ} (χ : DirichletCharacter ℂ N) {u : ℝ} (hu : 1 ≤ u) :
    ‖psiChar χ u - mainTerm χ u‖ ≤ u * Real.log u + u :=
  (norm_sub_le _ _).trans (add_le_add (norm_psiChar_le χ hu) (norm_mainTerm_le χ (by linarith)))

variable {N : ℕ} [NeZero N]

/-- Under GRH, `|Σ_{|Im ρ| < T} m_ρ u^ρ/ρ| ≤ √u Σ_{|Im ρ| < T} m_ρ/|ρ|`. -/
lemma norm_zeroSum_le (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) {u T : ℝ} (hu : 0 < u)
    (hfin : (stripZeros χ T).Finite) :
    ‖∑ᶠ ρ ∈ stripZeros χ T, (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      Real.sqrt u * ∑ᶠ ρ ∈ stripZeros χ T, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖ := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  have hre := re_eq_half_of_GRH hGRH hprim hρ.1 hρ.2.1 hρ.2.2.2
  rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu, hre, Complex.norm_natCast,
    ← Real.sqrt_eq_rpow]
  exact le_of_eq (by ring)

/-- The primitive case: `|ψ(u, χ) − E₀(χ) u| ≤ A √u (log u)(log Nu) + B log²(Nu)`. -/
theorem psiChar_primitive_bound (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → ∀ u : ℝ, 2 ≤ u →
        ‖psiChar χ u - mainTerm χ u‖ ≤
          A * Real.sqrt u * Real.log u * Real.log (N * u) + B * Real.log (N * u) ^ 2 := by
  obtain ⟨C₁, hC₁, hF⟩ := hEF
  obtain ⟨C₂, hC₂, hW⟩ := hZ
  refine ⟨32 * C₂, C₁ * (6 + 32 * C₂), by positivity, by positivity, ?_⟩
  intro N _ χ hprim u hu
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu0 : 0 < u := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hNu : (0 : ℝ) < N * u := by positivity
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  set ℓ := Real.log u with hℓ
  set L := Real.log (N * u) with hL
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hu
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hLsplit : L = Real.log N + ℓ := by
    rw [hL, Real.log_mul hN0.ne' hu0.ne']
  have hℓL : ℓ ≤ L := by linarith
  have hL2 : Real.log 2 ≤ L := by linarith
  obtain ⟨hfin, hbound⟩ := hF N χ hprim u u hu le_rfl
  have hfin1 : (stripZeros χ 1).Finite :=
    hfin.subset fun ρ hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1.trans_le (by linarith), hρ.2.2.2⟩
  -- the zero sum up to height `u`
  have hS := sum_stripZeros_le hGRH hC₂ hW hprim (by linarith : (1 : ℝ) ≤ u) hfin
  have hZn := norm_zeroSum_le hGRH hprim hu0 hfin
  have hlogA : Real.log (N * (u + 2)) ≤ 2 * L := by
    have : Real.log (N * (u + 2)) ≤ Real.log (2 * (N * u)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) hNu.ne'] at this
    linarith
  have hlogB : 1 + Real.log (u + 1) ≤ 4 * ℓ := by
    have : Real.log (u + 1) ≤ Real.log (2 * u) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hu0.ne'] at this
    linarith
  have hZsum : ‖∑ᶠ ρ ∈ stripZeros χ u,
      (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        32 * C₂ * Real.sqrt u * ℓ * L := by
    refine hZn.trans ?_
    have hA0 : 0 ≤ Real.log (N * (u + 2)) := Real.log_nonneg (by nlinarith)
    have hB0 : 0 ≤ 1 + Real.log (u + 1) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ u + 1); linarith
    calc Real.sqrt u * ∑ᶠ ρ ∈ stripZeros χ u, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖
        ≤ Real.sqrt u * (4 * C₂ * Real.log (N * (u + 2)) * (1 + Real.log (u + 1))) := by
          gcongr
      _ ≤ Real.sqrt u * (4 * C₂ * (2 * L) * (4 * ℓ)) := by
          gcongr
          exact mul_nonneg (by positivity) (by linarith)
      _ = 32 * C₂ * Real.sqrt u * ℓ * L := by ring
  -- the low-zero term
  have hS1 := sum_stripZeros_le hGRH hC₂ hW hprim (le_refl (1 : ℝ)) hfin1
  have hlow : ∑ᶠ ρ ∈ stripZeros χ 1, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖ ≤
      16 * C₂ * L := by
    refine hS1.trans ?_
    have h3 : Real.log (N * (1 + 2)) ≤ 2 * L := by
      have : Real.log (N * (1 + 2)) = Real.log N + Real.log 3 := by
        rw [Real.log_mul hN0.ne' (by norm_num)]; norm_num
      rw [this, hLsplit]
      have : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have h4 : 1 + Real.log (1 + 1) ≤ 2 := by norm_num; linarith
    have h30 : 0 ≤ Real.log (N * (1 + 2)) := Real.log_nonneg (by norm_num; linarith)
    calc 4 * C₂ * Real.log (N * (1 + 2)) * (1 + Real.log (1 + 1))
        ≤ 4 * C₂ * (2 * L) * 2 := by
          have h11 : 0 ≤ 1 + Real.log (1 + 1) := by
            have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1 + 1); linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) h4 h11
            (mul_nonneg (by positivity) (by linarith))
      _ = 16 * C₂ * L := by ring
  -- the truncation error
  have htrunc : u * Real.log (N * u * u) ^ 2 / u ≤ 4 * L ^ 2 := by
    have hcancel : u * Real.log (N * u * u) ^ 2 / u = Real.log (N * u * u) ^ 2 := by
      field_simp
    rw [hcancel]
    have : Real.log (N * u * u) = L + ℓ := by
      rw [Real.log_mul hNu.ne' hu0.ne']
    rw [this]
    have hℓ0 : 0 ≤ ℓ := by linarith
    nlinarith
  have hrhs : C₁ * (u * Real.log (N * u * u) ^ 2 / u + Real.log (N * u) +
      ∑ᶠ ρ ∈ stripZeros χ 1, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖) ≤
        C₁ * (6 + 32 * C₂) * L ^ 2 := by
    rw [← hL]
    have hLL : L ≤ 2 * L ^ 2 := by nlinarith
    have : u * Real.log (N * u * u) ^ 2 / u + L +
        ∑ᶠ ρ ∈ stripZeros χ 1, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖ ≤
          (6 + 32 * C₂) * L ^ 2 := by
      nlinarith
    calc _ ≤ C₁ * ((6 + 32 * C₂) * L ^ 2) := by gcongr
      _ = _ := by ring
  have hsplit : psiChar χ u - mainTerm χ u =
      (psiChar χ u - mainTerm χ u + ∑ᶠ ρ ∈ stripZeros χ u,
          (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
        ∑ᶠ ρ ∈ stripZeros χ u,
          (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  linarith [hbound.trans hrhs]

end PsiGRH
