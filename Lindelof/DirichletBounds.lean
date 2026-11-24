import Lindelof.DirichletCompleted

/-!
# Dirichlet Steps 4–6: bounds for `L(s, χ)` and its logarithm, primitive `χ ≠ 1`

Under GRH, for a primitive character `χ ≠ 1`:

* `norm_LFunction_le_mul` (Step 4): `‖L(σ+it)‖ ≤ C |t|^{(σ'-σ)/2} ‖L(σ'+it)‖` for
  `1/2 ≤ σ ≤ σ' ≤ 2`, `|t| ≥ 1`, from Dirichlet Step 2, `L = Λ / γ` and the Gamma ratio bound
  (`norm_Gamma_le_rpow_mul_two`; odd characters need Gamma arguments up to `3/2`).
* `norm_LFunction_sub_one_le`: `‖L(s) - 1‖ ≤ π²/6 - 1 < 2/3` on `σ ≥ 2`.
* `norm_LFunction_le_poly`: `‖L(s)‖ ≤ K (|t| + 2)` on `1/2 ≤ σ ≤ 5`.
* `exists_log_LFunction` (Step 5): a holomorphic logarithm `M` of `L` on `σ > 1/2`, equal to the
  principal `log L` on `σ ≥ 2`, hence bounded there.
* `logBounds_LFunction`: the hypotheses of the generic Steps 6–8 (`LogBounds`), so
  `lindelof_LFunction_of_primitive` follows from `isBigO_rpow_of_logBounds`.
-/

namespace Lindelof

open Complex ComplexConjugate Erdos985 Erdos985.Analytic DirichletCharacter Filter Topology
  Metric Asymptotics

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- The gamma factor is `Γℝ(s + κ)` with `κ = 0` (even) or `κ = 1` (odd). -/
lemma exists_gammaFactor_eq (χ : DirichletCharacter ℂ N) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ ≤ 1 ∧ ∀ s, gammaFactor χ s = Gammaℝ (s + κ) := by
  rcases χ.even_or_odd with h | h
  · exact ⟨0, le_rfl, zero_le_one, fun s => by rw [h.gammaFactor_def]; simp⟩
  · exact ⟨1, zero_le_one, le_rfl, fun s => by rw [h.gammaFactor_def]; simp⟩

/-- **Dirichlet Step 4.** Under GRH, `‖L(σ+it)‖ ≤ C |t|^{(σ'-σ)/2} ‖L(σ'+it)‖` for
`1/2 ≤ σ ≤ σ' ≤ 2` and `|t| ≥ 1`. -/
theorem norm_LFunction_le_mul (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ σ' t : ℝ, 1 / 2 ≤ σ → σ ≤ σ' → σ' ≤ 2 → 1 ≤ |t| →
      ‖LFunction χ (σ + t * I)‖ ≤ C * |t| ^ ((σ' - σ) / 2) * ‖LFunction χ (σ' + t * I)‖ := by
  obtain ⟨κ, hκ0, hκ1, hG⟩ := exists_gammaFactor_eq χ
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := norm_Gamma_le_rpow_mul_two
  refine ⟨Real.exp (Real.log N * (3 / 4)) * CΓ, by positivity, ?_⟩
  intro σ σ' t hσ hσσ' hσ' ht
  have hre : ∀ x : ℝ, ((x : ℂ) + t * I).re = x := fun x => by simp
  have hΛ : ∀ x : ℝ, 0 < x → ‖completedLFunction χ (x + t * I)‖ =
      ‖Gammaℝ (((x + κ : ℝ) : ℂ) + t * I)‖ * ‖LFunction χ (x + t * I)‖ := by
    intro x hx
    rw [completedLFunction_eq_mul χ (by rw [hre]; exact hx), hG, norm_mul]
    congr 3; push_cast; ring
  have hmono := norm_completedLFunction_le hGRH hprim hχ t hσ hσσ'
  rw [hΛ σ (by linarith), hΛ σ' (by linarith)] at hmono
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hE : Real.exp (Real.log N * (σ' - σ) / 2) ≤ Real.exp (Real.log N * (3 / 4)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hGam : ‖Gammaℝ (((σ' + κ : ℝ) : ℂ) + t * I)‖ ≤
      CΓ * |t| ^ ((σ' - σ) / 2) * ‖Gammaℝ (((σ + κ : ℝ) : ℂ) + t * I)‖ := by
    rw [norm_Gammaℝ_eq, norm_Gammaℝ_eq]
    have hy : 1 / 2 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
    have hg := hCΓ ((σ + κ) / 2) ((σ' + κ) / 2) (t / 2) (by linarith) (by linarith)
      (by linarith) hy
    have hexp : (2 * |t / 2|) ^ ((σ' + κ) / 2 - (σ + κ) / 2) = |t| ^ ((σ' - σ) / 2) := by
      rw [abs_div, abs_two, mul_div_cancel₀ _ two_ne_zero]; ring_nf
    rw [hexp] at hg
    have hπ : Real.pi ^ (-(σ' + κ) / 2) ≤ Real.pi ^ (-(σ + κ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    have h0 : 0 ≤ ‖Gamma (((σ' + κ) / 2 : ℝ) + ((t / 2 : ℝ)) * I)‖ := norm_nonneg _
    calc Real.pi ^ (-(σ' + κ) / 2) * ‖Gamma (((σ' + κ) / 2 : ℝ) + ((t / 2 : ℝ)) * I)‖
        ≤ Real.pi ^ (-(σ + κ) / 2) *
            (CΓ * |t| ^ ((σ' - σ) / 2) * ‖Gamma (((σ + κ) / 2 : ℝ) + ((t / 2 : ℝ)) * I)‖) :=
          mul_le_mul hπ hg h0 (by positivity)
      _ = _ := by ring
  have hGpos : 0 < ‖Gammaℝ (((σ + κ : ℝ) : ℂ) + t * I)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by rw [hre]; linarith))
  set G := ‖Gammaℝ (((σ + κ : ℝ) : ℂ) + t * I)‖
  set G' := ‖Gammaℝ (((σ' + κ : ℝ) : ℂ) + t * I)‖
  set A := ‖LFunction χ (σ + t * I)‖
  set B := ‖LFunction χ (σ' + t * I)‖
  have hB : 0 ≤ B := norm_nonneg _
  have hT : 0 ≤ |t| ^ ((σ' - σ) / 2) := by positivity
  refine le_of_mul_le_mul_left ?_ hGpos
  calc G * A ≤ Real.exp (Real.log N * (σ' - σ) / 2) * (G' * B) := hmono
    _ ≤ Real.exp (Real.log N * (3 / 4)) * ((CΓ * |t| ^ ((σ' - σ) / 2) * G) * B) := by
        gcongr
    _ = G * (Real.exp (Real.log N * (3 / 4)) * CΓ * |t| ^ ((σ' - σ) / 2) * B) := by ring

omit [NeZero N] in
lemma pi_sq_div_six_sub_one_le : Real.pi ^ 2 / 6 - 1 ≤ 2 / 3 := by
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

/-- `‖L(s, χ) - 1‖ ≤ π²/6 - 1` on `σ ≥ 2`. -/
theorem norm_LFunction_sub_one_le (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LFunction χ s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  rw [LFunction_eq_LSeries χ (by linarith)]
  set f := LSeries.term (fun n => χ n) s
  have hsum : Summable f :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => by simpa using DirichletCharacter.norm_le_one χ n) (by linarith)
  have hf1 : f 1 = 1 := by
    simp [f]
  have hF := hsum.hasSum.sub (hasSum_ite_eq 1 (f 1))
  have hg := hasSum_zeta_two.sub (hasSum_ite_eq 1 ((1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2))
  rw [hf1] at hF
  norm_num at hg
  refine hF.norm_le_of_bounded hg fun n => ?_
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [hf1]
  · simp only [hn1, if_false, sub_zero]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [f]
    · rw [LSeries.norm_term_eq, if_neg hn0]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
      have h2 : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn hs
      rw [Real.rpow_two] at h2
      have hp : 0 < (n : ℝ) ^ 2 := by positivity
      calc ‖χ n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ 2 := by
            rw [div_le_div_iff₀ (by linarith) hp]; nlinarith [norm_nonneg (χ n)]
        _ = _ := by simp

/-- On `σ ≥ 2`: `1/3 ≤ ‖L(s)‖ ≤ 2` and `Re L(s) > 0`. -/
theorem LFunction_near_one (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 3 ≤ ‖LFunction χ s‖ ∧ ‖LFunction χ s‖ ≤ 2 ∧ 0 < (LFunction χ s).re := by
  have h := (norm_LFunction_sub_one_le χ hs).trans pi_sq_div_six_sub_one_le
  have h1 : ‖LFunction χ s‖ ≤ ‖LFunction χ s - 1‖ + 1 := by
    simpa using norm_add_le (LFunction χ s - 1) 1
  have h2 : 1 ≤ ‖LFunction χ s‖ + ‖LFunction χ s - 1‖ := by
    simpa using norm_sub_le (LFunction χ s) (LFunction χ s - 1)
  have h3 := abs_re_le_norm (LFunction χ s - 1)
  rw [sub_re, one_re] at h3
  refine ⟨by linarith, by linarith, by linarith [neg_abs_le ((LFunction χ s).re - 1)]⟩

/-- Under GRH, `‖L(s)‖ ≤ K (|t| + 2)` on `1/2 ≤ σ ≤ 5`. -/
theorem norm_LFunction_le_poly (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 →
      ‖LFunction χ s‖ ≤ K * (|s.im| + 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_LFunction_le_mul hGRH hprim hχ
  have hcpt : IsCompact (closedBall (3 : ℂ) (7 / 2)) := isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn
    (differentiable_LFunction hχ).continuous.continuousOn
  refine ⟨max 1 (max B (2 * C)), le_max_left _ _, fun s hs1 hs5 => ?_⟩
  have hK1 : 1 ≤ max 1 (max B (2 * C)) := le_max_left _ _
  have hKB : B ≤ max 1 (max B (2 * C)) := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : 2 * C ≤ max 1 (max B (2 * C)) := (le_max_right _ _).trans (le_max_right _ _)
  have ht : 0 ≤ |s.im| := abs_nonneg _
  by_cases h2 : 2 ≤ s.re
  · have := (LFunction_near_one χ h2).2.1
    nlinarith
  push Not at h2
  by_cases hsm : 1 ≤ |s.im|
  · have hs : s = (s.re : ℂ) + s.im * I := (re_add_im s).symm
    have h := hC s.re 2 s.im hs1 h2.le le_rfl hsm
    have hL2 := (LFunction_near_one χ (s := (2 : ℝ) + s.im * I) (by simp)).2.1
    have hpow : |s.im| ^ ((2 - s.re) / 2) ≤ |s.im| :=
      (Real.rpow_le_rpow_of_exponent_le hsm (by linarith)).trans (Real.rpow_one _).le
    rw [← hs] at h
    calc ‖LFunction χ s‖ ≤ C * |s.im| ^ ((2 - s.re) / 2) * ‖LFunction χ ((2 : ℝ) + s.im * I)‖ := h
      _ ≤ C * |s.im| * 2 := by gcongr
      _ = 2 * C * |s.im| := by ring
      _ ≤ max 1 (max B (2 * C)) * (|s.im| + 2) := by nlinarith
  · push Not at hsm
    have hmem : s ∈ closedBall (3 : ℂ) (7 / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      simp only [sub_re, sub_im]
      norm_num
      have : |s.re - 3| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have := hB s hmem
    nlinarith

/-- **Dirichlet Step 5.** Under GRH, `L(·, χ)` has a holomorphic logarithm on `σ > 1/2`, bounded
on `σ ≥ 2`. -/
theorem exists_log_LFunction (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ M : ℂ → ℂ, DifferentiableOn ℂ M halfPlane ∧
      (∀ s ∈ halfPlane, exp (M s) = LFunction χ s) ∧
      ∀ s : ℂ, 2 ≤ s.re → ‖M s‖ ≤ 2 + Real.pi := by
  have hLd : DifferentiableOn ℂ (LFunction χ) halfPlane :=
    (differentiable_LFunction hχ).differentiableOn
  have hL0 : ∀ s ∈ halfPlane, LFunction χ s ≠ 0 := fun s hs =>
    hGRH N χ s hs (Or.inl hχ)
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const continuous_re
  have hsc : IsSimplyConnected halfPlane := by
    have : ContractibleSpace halfPlane := (convex_halfSpace_re_gt (1 / 2 : ℝ)).contractibleSpace
      ⟨2, show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num⟩
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨M₀, hM₀c, hM₀e⟩ := exists_continuousOn_eqOn_exp_comp hsc hopen hLd.continuousOn
    (by rintro ⟨s, hs, h0⟩; exact hL0 s hs h0)
  have hM₀e' : ∀ s ∈ halfPlane, exp (M₀ s) = LFunction χ s := fun s hs => hM₀e hs
  set W : Set ℂ := {s | 2 ≤ s.re} with hW
  have hWH : W ⊆ halfPlane := fun s (hs : 2 ≤ s.re) => show 1 / 2 < s.re by linarith
  let G : ℂ → ℂ := fun s => log (LFunction χ s)
  have hGc : ContinuousOn G W :=
    ((differentiable_LFunction hχ).continuous.continuousOn).clog fun s (hs : 2 ≤ s.re) =>
      mem_slitPlane_iff.mpr (Or.inl (LFunction_near_one χ hs).2.2)
  have hGe : ∀ s ∈ W, exp (M₀ s) = exp (G s) := fun s hs => by
    rw [hM₀e' s (hWH hs), exp_log (hL0 s (hWH hs))]
  have h2W : (2 : ℂ) ∈ W := show (2 : ℝ) ≤ (2 : ℂ).re by norm_num
  set c := M₀ 2 - G 2 with hc
  have hconst : ∀ s ∈ W, M₀ s - G s = c := fun s hs =>
    sub_eq_sub_of_exp_eq (convex_halfSpace_re_ge (2 : ℝ)).isPreconnected
      (hM₀c.mono hWH) hGc hGe hs h2W
  have hc1 : exp c = 1 := by
    rw [hc, exp_sub, hGe 2 h2W, div_self (exp_ne_zero _)]
  refine ⟨fun s => M₀ s - c, ?_, ?_, ?_⟩
  · exact (differentiableOn_of_exp_eq hopen hLd hM₀c hM₀e').sub_const c
  · intro s hs
    simp only [exp_sub, hc1, div_one, hM₀e' s hs]
  · intro s hs
    have : M₀ s - c = G s := by rw [← hconst s hs]; ring
    show ‖M₀ s - c‖ ≤ _
    rw [this]
    obtain ⟨h1, h2, -⟩ := LFunction_near_one χ hs
    refine (norm_le_abs_re_add_abs_im _).trans (add_le_add ?_ ?_)
    · simp only [G, log_re]
      have hx : 0 < ‖LFunction χ s‖ := by linarith
      rw [abs_le]
      constructor
      · have := Real.one_sub_inv_le_log_of_pos hx
        have : ‖LFunction χ s‖⁻¹ ≤ 3 := by
          rw [inv_le_comm₀ hx (by norm_num)]; linarith
        linarith
      · have := Real.log_le_sub_one_of_pos hx
        linarith
    · simp only [G, log_im]
      exact abs_arg_le_pi _

/-- Under GRH, a primitive `L(·, χ)` with `χ ≠ 1` satisfies the hypotheses of the generic
argument. -/
theorem logBounds_LFunction (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LogBounds (LFunction χ) := by
  obtain ⟨C, -, hC⟩ := norm_LFunction_le_mul hGRH hprim hχ
  obtain ⟨M, hMd, hexp, hMb⟩ := exists_log_LFunction hGRH hχ
  obtain ⟨K, hK1, hKb⟩ := norm_LFunction_le_poly hGRH hprim hχ
  refine ⟨⟨LFunction χ, M, 1, K, 2 + Real.pi, C, hK1, hKb, hMd, hexp,
    fun s hs _ => hMb s hs, fun s hs _ => ?_, fun δ hδ hδ' t ht => ?_⟩⟩
  · rw [← hexp s hs, norm_exp, one_mul]
    exact Real.exp_le_exp.mpr (re_le_norm _)
  · have ht' : 1 ≤ |t| := by rwa [abs_of_nonneg (by linarith)]
    have h := hC (1 / 2) (1 / 2 + δ) t le_rfl (by linarith) (by linarith) ht'
    rw [abs_of_nonneg (by linarith), show 1 / 2 + δ - 1 / 2 = δ by ring] at h
    have hcast : (1 / 2 : ℂ) + t * I = ((1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [hcast]
    exact h

/-- **Lindelöf for a primitive Dirichlet L-function** `χ ≠ 1`, under GRH. -/
theorem lindelof_LFunction_of_primitive (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => ‖LFunction χ (1 / 2 + t * I)‖) =O[atTop] fun t : ℝ => t ^ ε :=
  isBigO_rpow_of_logBounds (logBounds_LFunction hGRH hprim hχ) hε

end Lindelof
