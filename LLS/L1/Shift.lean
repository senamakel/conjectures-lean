import LLS.L1.Defs
import LLS.L1.ShiftAux.Identity

/-! # The log-weighted explicit formula with a real shift `σ > 1` (LLS proof of Lemma 2.5) -/

namespace LLS

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic Erdos985.Analytic.BoundsAux
  LLS.ShiftLogAux

variable {N : ℕ} [NeZero N]

/-- For `σ > 1`, `Σ_{n≤x} Λ(n)χ(n) n^{−σ} log(x/n) = −(L'/L)(σ) log x − (L'/L)'(σ)
− Σ_ρ m_ρ x^{ρ−σ}/(ρ−σ)² − Σ_k x^{−(σ+m_k)}/(σ+m_k)²`; under GRH the last two sums are at most
`x^{1/2−σ} Z2` and `2x^{−σ}` in norm. -/
theorem shifted_log_bound (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) (σ : ℝ) (hσ : 1 < σ) :
    ‖(∑ n ∈ Finset.range (x + 1),
        (Λ n : ℂ) * χ n * (n : ℂ) ^ (-(σ : ℂ)) * (Real.log ((x : ℝ) / n) : ℂ))
      + deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ
          * (Real.log x : ℂ)
      + deriv (fun s => deriv (DirichletCharacter.LFunction χ) s
          / DirichletCharacter.LFunction χ s) σ‖
      ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - σ) * Z2 χ + 2 * (x : ℝ) ^ (-σ) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set L := DirichletCharacter.LFunction χ with hL
  set G := gammaLogDeriv χ with hG
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  set mk : ℕ → ℂ := fun k => ((2 * k + parity χ : ℕ) : ℂ) with hmk
  set u : ℂ := 2 + σ with hu
  set lx : ℂ := (Real.log x : ℂ) with hlx
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  obtain ⟨hS1, hS2, hid⟩ := shifted_identity hGRH hprim hχ x hx1 σ hσ
  have hderiv := deriv_logDeriv_L hGRH hprim hχ hσ
  obtain ⟨hQ1, -⟩ := hasDerivAt_D hGRH hprim hχ hσ
  obtain ⟨hQ2, -⟩ := hasDerivAt_G χ hσ
  have hΛd : Differentiable ℂ Λf := DirichletCharacter.differentiable_completedLFunction hχ
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv hΛd (completedLFunction_zero_ne_zero χ hχ hprim)
    (completedLFunction_growth χ hχ)
  have hσre : 1 < ((σ : ℂ)).re := by simp; linarith
  have hure : 1 < u.re := by simp [hu]; linarith
  obtain ⟨hbσs, hbσe⟩ := hb σ (hΛne _ hσre.le)
  obtain ⟨hbus, hbue⟩ := hb u (hΛne _ hure.le)
  have hre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hρ0 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ) ≠ 0 := fun ρ h => by
    have := hre ρ; rw [h] at this; norm_num at this
  have hsρ : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (σ : ℂ) - ρ ≠ 0 := fun ρ h => by
    have := congrArg Complex.re h; simp [hre ρ] at this; linarith
  have huρ : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, u - ρ ≠ 0 := fun ρ h => by
    have := congrArg Complex.re h; simp [hu, hre ρ] at this; linarith
  have hZ2s := ShiftAux.summable_Z2 hGRH hprim hχ
  have hmkre : ∀ k : ℕ, (k : ℝ) ≤ (mk k).re := fun k => by
    simp only [mk, natCast_re]; push_cast; linarith [(Nat.cast_nonneg (parity χ) : (0 : ℝ) ≤ _)]
  have hsk : ∀ k, (σ : ℂ) + mk k ≠ 0 := fun k h => by
    have := congrArg Complex.re h; simp only [add_re, ofReal_re, zero_re] at this
    linarith [hmkre k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have huk : ∀ k, u + mk k ≠ 0 := fun k h => by
    have := congrArg Complex.re h; simp only [hu, add_re, ofReal_re, zero_re, re_ofNat] at this
    linarith [hmkre k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  /- the pieces of the zero sum -/
  set Zx : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => m ρ * ((x : ℂ) ^ ((ρ : ℂ) - σ) / ((ρ : ℂ) - σ) ^ 2)
    with hZx
  have hZxb : ∀ ρ, ‖Zx ρ‖ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - σ)
      * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ
    have hn := (norm_le_norm_sub (hre ρ) hσ).1
    have hp : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 (hρ0 ρ)
    simp only [Zx, m, norm_mul, Complex.norm_natCast, norm_div, norm_pow]
    have hc : ‖(x : ℂ) ^ ((ρ : ℂ) - σ)‖ = (x : ℝ) ^ ((1 : ℝ) / 2 - σ) := by
      rw [show (x : ℂ) = ((x : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hx0]
      simp [hre ρ]
    have hw : ‖(ρ : ℂ) - σ‖ = ‖(σ : ℂ) - ρ‖ := norm_sub_rev _ _
    rw [hc, hw]
    have : 1 / ‖(σ : ℂ) - ρ‖ ^ 2 ≤ 1 / ‖(ρ : ℂ)‖ ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le hn 2)
    have h0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - σ) := by positivity
    calc (analyticOrderNatAt Λf ρ : ℝ) * ((x : ℝ) ^ ((1 : ℝ) / 2 - σ) / ‖(σ : ℂ) - ρ‖ ^ 2)
        = (x : ℝ) ^ ((1 : ℝ) / 2 - σ) * ((analyticOrderNatAt Λf ρ : ℝ) * (1 / ‖(σ : ℂ) - ρ‖ ^ 2)) := by
          ring
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - σ) * ((analyticOrderNatAt Λf ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hZxs : Summable Zx := Summable.of_norm_bounded (hZ2s.mul_left _) hZxb
  set Q1 : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => m ρ * (1 / ((σ : ℂ) - ρ) ^ 2) with hQ1d
  set P1 : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ =>
    m ρ * ((1 / (u - ρ) + 1 / ρ) - (1 / ((σ : ℂ) - ρ) + 1 / ρ)) with hP1d
  have hP1s : Summable P1 := by
    refine (hbus.sub hbσs).congr fun ρ => ?_
    simp only [P1, m]; ring
  have hP1v : ∑' ρ, P1 ρ = D χ u - D χ σ := by
    rw [show (fun ρ => P1 ρ) = fun ρ => m ρ * (1 / (u - ρ) + 1 / ρ)
        - m ρ * (1 / ((σ : ℂ) - ρ) + 1 / ρ) from funext fun ρ => by simp only [P1]; ring,
      hbus.tsum_sub hbσs]
    simp only [LLS.D]
    rw [hbue, hbσe]; ring
  have hR1 : ∀ ρ, m ρ * Rw x ((ρ : ℂ) - σ) = Zx ρ - Q1 ρ - lx * P1 ρ := by
    intro ρ
    simp only [Rw, Zx, Q1, P1, m, hlx]
    have h1 := hsρ ρ
    have h2 := huρ ρ
    have h3 : (ρ : ℂ) - σ ≠ 0 := fun h => h1 (by rw [← neg_sub, h, neg_zero])
    have h4 : (2 : ℂ) - ((ρ : ℂ) - σ) = u - ρ := by simp only [hu]; ring
    rw [h4]
    have h5 : ((ρ : ℂ) - σ) ^ 2 = ((σ : ℂ) - ρ) ^ 2 := by ring
    rw [h5]
    have h6 := hρ0 ρ
    generalize (x : ℂ) ^ ((ρ : ℂ) - σ) = X
    field_simp
    ring
  have hsum1 : ∑' ρ, m ρ * Rw x ((ρ : ℂ) - σ) = ∑' ρ, Zx ρ - ∑' ρ, Q1 ρ - lx * ∑' ρ, P1 ρ := by
    rw [tsum_congr hR1, (hZxs.sub hQ1).tsum_sub (hP1s.mul_left lx), hZxs.tsum_sub hQ1,
      tsum_mul_left]
  /- the pieces of the gamma sum -/
  set Γx : ℕ → ℂ := fun k => (x : ℂ) ^ (-((σ : ℂ) + mk k)) / (-((σ : ℂ) + mk k)) ^ 2 with hΓx
  have hq : (1 / (x : ℝ) ^ 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hΓxb : ∀ k : ℕ, ‖Γx k‖ ≤ (x : ℝ) ^ (-σ) * (1 / 4) ^ k := by
    intro k
    simp only [Γx, norm_div, norm_pow, norm_neg]
    have hc : ‖(x : ℂ) ^ (-((σ : ℂ) + mk k))‖ = (x : ℝ) ^ (-(σ + (mk k).re)) := by
      rw [show (x : ℂ) = ((x : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    rw [hc]
    have hden : 1 ≤ ‖(σ : ℂ) + mk k‖ ^ 2 := by
      have := Complex.re_le_norm ((σ : ℂ) + mk k)
      simp only [add_re, ofReal_re] at this
      have : 1 ≤ ‖(σ : ℂ) + mk k‖ := by linarith [hmkre k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith
    have hnum : (x : ℝ) ^ (-(σ + (mk k).re)) ≤ (x : ℝ) ^ (-σ) * (1 / 4) ^ k := by
      have h1 : (x : ℝ) ^ (-(σ + (mk k).re)) ≤ (x : ℝ) ^ (-σ - 2 * (k : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        have : 2 * (k : ℝ) ≤ (mk k).re := by
          simp only [mk, natCast_re]; push_cast
          linarith [(Nat.cast_nonneg (parity χ) : (0 : ℝ) ≤ _)]
        linarith
      have h2 : (x : ℝ) ^ (-σ - 2 * (k : ℝ)) = (x : ℝ) ^ (-σ) * (1 / (x : ℝ) ^ 2) ^ k := by
        rw [Real.rpow_sub hx0, div_eq_mul_inv, one_div, ← inv_pow, ← pow_mul,
          show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, inv_pow]
      rw [h2] at h1
      refine h1.trans ?_
      gcongr
    have h0 : 0 ≤ (x : ℝ) ^ (-(σ + (mk k).re)) := by positivity
    calc (x : ℝ) ^ (-(σ + (mk k).re)) / ‖(σ : ℂ) + mk k‖ ^ 2
        ≤ (x : ℝ) ^ (-(σ + (mk k).re)) / 1 := div_le_div_of_nonneg_left h0 one_pos hden
      _ ≤ _ := by rw [div_one]; exact hnum
  have hgeom : Summable fun k : ℕ => (x : ℝ) ^ (-σ) * (1 / 4 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hΓxs : Summable Γx := Summable.of_norm_bounded hgeom hΓxb
  set Q2 : ℕ → ℂ := fun k => 1 / ((σ : ℂ) + mk k) ^ 2 with hQ2d
  set P2 : ℕ → ℂ := fun k => (1 / (2 + mk k) - 1 / ((σ : ℂ) + mk k))
    - (1 / (2 + mk k) - 1 / (u + mk k)) with hP2d
  have hgσ := hasSum_gammaLogDeriv χ (s := (σ : ℂ)) hσre
  have hgu := hasSum_gammaLogDeriv χ (s := u) hure
  have hP2h : HasSum P2 (G σ - G u) := by
    have := hgσ.sub hgu
    convert this using 1
    simp only [hG]; ring
  have hR2 : ∀ k, Rw x (-((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ))) = Γx k - Q2 k - lx * P2 k := by
    intro k
    change Rw x (-((σ : ℂ) + mk k)) = _
    simp only [Rw, Γx, Q2, P2, hlx]
    have h1 := hsk k
    have h2 := huk k
    have h4 : (2 : ℂ) - -((σ : ℂ) + mk k) = u + mk k := by simp only [hu]; ring
    rw [h4]
    have h3 : (2 : ℂ) + mk k ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp only [add_re, zero_re, re_ofNat] at this
      linarith [hmkre k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h5 : (-((σ : ℂ) + mk k)) ^ 2 = ((σ : ℂ) + mk k) ^ 2 := by ring
    rw [h5]
    generalize (x : ℂ) ^ (-((σ : ℂ) + mk k)) = X
    field_simp
    ring
  have hsum2 : ∑' k, Rw x (-((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ)))
      = ∑' k, Γx k - ∑' k, Q2 k - lx * (G σ - G u) := by
    rw [tsum_congr hR2, (hΓxs.sub hQ2).tsum_sub (hP2h.summable.mul_left lx), hΓxs.tsum_sub hQ2,
      tsum_mul_left, hP2h.tsum_eq]
  /- assemble -/
  have hLσ : deriv L σ / L σ = D χ σ - G σ := logDeriv_LFunction_eq hχ hσre
  have hLu : deriv L u / L u = D χ u - G u := logDeriv_LFunction_eq hχ hure
  have hkey : (∑ n ∈ Finset.range (x + 1),
        (Λ n : ℂ) * χ n * (n : ℂ) ^ (-(σ : ℂ)) * (Real.log ((x : ℝ) / n) : ℂ))
      + deriv L σ / L σ * lx
      + deriv (fun s => deriv L s / L s) σ = -(∑' ρ, Zx ρ) - ∑' k, Γx k := by
    rw [hid, hsum1, hsum2, hP1v, hderiv, hLσ]
    change -(∑' ρ, Zx ρ - ∑' ρ, Q1 ρ - lx * (D χ u - D χ σ))
      - (∑' k, Γx k - ∑' k, Q2 k - lx * (G σ - G u)) - deriv L u / L u * lx
      + (D χ σ - G σ) * lx + (-(∑' ρ, Q1 ρ) - ∑' k, Q2 k) = _
    rw [hLu]; ring
  rw [hkey]
  have hb1 : ‖∑' ρ, Zx ρ‖ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - σ) * Z2 χ := by
    refine (norm_tsum_le_tsum_norm hZxs.norm).trans ?_
    calc ∑' ρ, ‖Zx ρ‖ ≤ ∑' ρ : {ρ : ℂ // Λf ρ = 0}, (x : ℝ) ^ ((1 : ℝ) / 2 - σ)
          * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) :=
          hZxs.norm.tsum_le_tsum hZxb (hZ2s.mul_left _)
      _ = _ := by rw [tsum_mul_left]; rfl
  have hb2 : ‖∑' k, Γx k‖ ≤ 2 * (x : ℝ) ^ (-σ) := by
    refine (norm_tsum_le_tsum_norm hΓxs.norm).trans ?_
    calc ∑' k, ‖Γx k‖ ≤ ∑' k : ℕ, (x : ℝ) ^ (-σ) * (1 / 4 : ℝ) ^ k :=
          hΓxs.norm.tsum_le_tsum hΓxb hgeom
      _ = (x : ℝ) ^ (-σ) * (4 / 3) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      _ ≤ 2 * (x : ℝ) ^ (-σ) := by
          have : (0 : ℝ) ≤ (x : ℝ) ^ (-σ) := by positivity
          nlinarith
  calc ‖-(∑' ρ, Zx ρ) - ∑' k, Γx k‖ ≤ ‖∑' ρ, Zx ρ‖ + ‖∑' k, Γx k‖ := by
        rw [sub_eq_add_neg, ← neg_add]; rw [norm_neg]; exact norm_add_le _ _
    _ ≤ _ := add_le_add hb1 hb2

end LLS
