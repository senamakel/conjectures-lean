import LLS.Analytic.Log.Identity
import LLS.Analytic.Shift.ZeroPart

/-!
# The derivative of `L'/L` at a real point `σ > 1`

Termwise differentiation of the Hadamard series of `D = Λ'/Λ` and of the digamma series of
`G = gammaLogDeriv χ` on a small ball around `σ`:
`(L'/L)'(σ) = D'(σ) − G'(σ) = −Σ_ρ m_ρ/(σ−ρ)² − Σ_k 1/(σ+m_k)²`, `m_k = 2k + 𝔞`.
-/

namespace LLS.ShiftLogAux

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic Erdos985.Analytic.BoundsAux

lemma re_gt_of_mem_ball {σ ε : ℝ} (hε : ε = (σ - 1) / 2) {z : ℂ}
    (hz : z ∈ Metric.ball (σ : ℂ) ε) : 1 < z.re := by
  have hz' : ‖z - σ‖ < ε := by simpa [dist_eq_norm] using hz
  have := Complex.abs_re_le_norm (z - σ)
  simp only [sub_re, ofReal_re] at this
  have : |z.re - σ| < ε := lt_of_le_of_lt this hz'
  rw [abs_lt] at this
  rw [hε] at this; linarith

variable {N : ℕ} [NeZero N]

/-- For a zero on the critical line and `σ > 1`: `|ρ| ≤ |σ − ρ|` and `σ − 1/2 ≤ |σ − ρ|`. -/
lemma norm_le_norm_sub {ρ : ℂ} (hρ : ρ.re = 1 / 2) {σ : ℝ} (hσ : 1 < σ) :
    ‖ρ‖ ≤ ‖(σ : ℂ) - ρ‖ ∧ σ - 1 / 2 ≤ ‖(σ : ℂ) - ρ‖ := by
  constructor
  · rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, hρ]
    nlinarith
  · have := Complex.abs_re_le_norm ((σ : ℂ) - ρ)
    simp only [sub_re, ofReal_re, hρ] at this
    rw [abs_of_pos (by linarith)] at this
    exact this

/-- `D` has the termwise derivative at `σ > 1`. -/
theorem hasDerivAt_D (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * (1 / ((σ : ℂ) - ρ) ^ 2)) ∧
    HasDerivAt (D χ) (-∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * (1 / ((σ : ℂ) - ρ) ^ 2)) σ := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  have hΛd : Differentiable ℂ Λf := DirichletCharacter.differentiable_completedLFunction hχ
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv hΛd (completedLFunction_zero_ne_zero χ hχ hprim)
    (completedLFunction_growth χ hχ)
  have hZ2 := ShiftAux.summable_Z2 hGRH hprim hχ
  set ε : ℝ := (σ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set t : Set ℂ := Metric.ball (σ : ℂ) ε with ht
  have hre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  -- for `s ∈ t`, `|s − ρ| ≥ |ρ|/2`
  have hlow : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ∀ s ∈ t, ‖(ρ : ℂ)‖ / 2 ≤ ‖s - ρ‖ := by
    intro ρ s hs
    obtain ⟨h1, h2⟩ := norm_le_norm_sub (hre ρ) hσ
    have hs' : ‖s - σ‖ < ε := by simpa [ht, dist_eq_norm] using hs
    have : ‖(σ : ℂ) - ρ‖ ≤ ‖s - ρ‖ + ‖s - σ‖ := by
      have := norm_sub_le (s - ρ) (s - σ)
      rw [show s - ρ - (s - σ) = (σ : ℂ) - ρ by ring] at this
      linarith
    have : ε ≤ ‖(σ : ℂ) - ρ‖ / 2 := by rw [hε]; linarith
    linarith
  have hρ0 : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, 0 < ‖(ρ : ℂ)‖ := fun ρ => by
    apply norm_pos_iff.2; intro h; have := hre ρ; rw [h] at this; norm_num at this
  have hsne : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ∀ s ∈ t, s - ρ ≠ 0 := fun ρ s hs h => by
    have := hlow ρ s hs; rw [h, norm_zero] at this; linarith [hρ0 ρ]
  have hσt : (σ : ℂ) ∈ t := Metric.mem_ball_self hε0
  -- termwise data
  set g : {ρ : ℂ // Λf ρ = 0} → ℂ → ℂ := fun ρ s => m ρ * (1 / (s - ρ) + 1 / ρ) with hg
  set g' : {ρ : ℂ // Λf ρ = 0} → ℂ → ℂ := fun ρ s => -(m ρ * (1 / (s - ρ) ^ 2)) with hg'
  have hgd : ∀ ρ y, y ∈ t → HasDerivAt (g ρ) (g' ρ y) y := by
    intro ρ y hy
    have h1 : HasDerivAt (fun s : ℂ => s - ρ) 1 y := (hasDerivAt_id y).sub_const _
    have h2 := (h1.inv (hsne ρ y hy))
    have h3 := (h2.add_const (1 / (ρ : ℂ))).const_mul (m ρ)
    convert h3 using 1
    · funext s; simp [g, one_div]
    · simp only [g', one_div]; ring
  have hbound : ∀ ρ y, y ∈ t → ‖g' ρ y‖ ≤ 4 * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ y hy
    have hl := hlow ρ y hy
    have hp : 0 < ‖(ρ : ℂ)‖ / 2 := by linarith [hρ0 ρ]
    simp only [g', norm_neg, norm_mul, m, Complex.norm_natCast, norm_div, norm_one, norm_pow]
    have : 1 / ‖y - ρ‖ ^ 2 ≤ 1 / (‖(ρ : ℂ)‖ / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le hl 2)
    have hm0 : (0 : ℝ) ≤ analyticOrderNatAt Λf ρ := Nat.cast_nonneg _
    calc (analyticOrderNatAt Λf ρ : ℝ) * (1 / ‖y - ρ‖ ^ 2)
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (1 / (‖(ρ : ℂ)‖ / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left this hm0
      _ = 4 * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
          field_simp; ring
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  have hσ1 : 1 ≤ ((σ : ℂ)).re := by simp; linarith
  obtain ⟨hs0, -⟩ := hb σ (hΛne _ hσ1)
  have hderiv := hasDerivAt_tsum_of_isPreconnected (hZ2.mul_left 4) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected hgd hbound hσt hs0 hσt
  -- `D = b + Σ g` near `σ`
  have hev : D χ =ᶠ[nhds (σ : ℂ)] fun z => b + ∑' ρ, g ρ z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hσt] with z hz
    have hz1 : 1 ≤ z.re := (re_gt_of_mem_ball hε hz).le
    obtain ⟨-, he⟩ := hb z (hΛne _ hz1)
    simp only [LLS.D]
    rw [he]
  have hsum' : Summable (fun ρ : {ρ : ℂ // Λf ρ = 0} => m ρ * (1 / ((σ : ℂ) - ρ) ^ 2)) := by
    refine Summable.of_norm_bounded (hZ2.mul_left 4) fun ρ => ?_
    have := hbound ρ σ hσt
    simpa [g'] using this
  refine ⟨hsum', ?_⟩
  have h2 := (hderiv.const_add b).congr_of_eventuallyEq hev
  convert h2 using 1
  simp only [g', tsum_neg, m]
  rfl

omit [NeZero N] in
/-- `G = gammaLogDeriv χ` has the termwise derivative at `σ > 1`. -/
theorem hasDerivAt_G (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun k : ℕ => 1 / ((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ)) ^ 2) ∧
    HasDerivAt (gammaLogDeriv χ)
      (∑' k : ℕ, 1 / ((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ)) ^ 2) σ := by
  set ε : ℝ := (σ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set t : Set ℂ := Metric.ball (σ : ℂ) ε with ht
  have hσt : (σ : ℂ) ∈ t := Metric.mem_ball_self hε0
  have hret : ∀ s ∈ t, 1 < s.re := fun z hz => re_gt_of_mem_ball hε hz
  set mk : ℕ → ℂ := fun k => ((2 * k + parity χ : ℕ) : ℂ) with hmk
  have hmk_re : ∀ k : ℕ, (k : ℝ) ≤ (mk k).re := fun k => by
    simp only [mk, natCast_re]; push_cast; linarith [(Nat.cast_nonneg (parity χ) : (0 : ℝ) ≤ _)]
  have hlow : ∀ k : ℕ, ∀ s ∈ t, (k : ℝ) + 1 ≤ ‖s + mk k‖ := fun k s hs => by
    have := Complex.re_le_norm (s + mk k)
    simp only [add_re] at this
    linarith [hret s hs, hmk_re k]
  have hne : ∀ k : ℕ, ∀ s ∈ t, s + mk k ≠ 0 := fun k s hs h => by
    have := hlow k s hs; rw [h, norm_zero] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set g : ℕ → ℂ → ℂ := fun k s => 1 / (2 + mk k) - 1 / (s + mk k) with hg
  set g' : ℕ → ℂ → ℂ := fun k s => 1 / (s + mk k) ^ 2 with hg'
  have hgd : ∀ k y, y ∈ t → HasDerivAt (g k) (g' k y) y := by
    intro k y hy
    have h1 : HasDerivAt (fun s : ℂ => s + mk k) 1 y := (hasDerivAt_id y).add_const _
    have h2 := (h1.inv (hne k y hy)).const_sub (1 / (2 + mk k))
    convert h2 using 1
    · funext s; simp [g, one_div]
    · simp only [g', one_div]; ring
  have hu : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    exact (summable_nat_add_iff 1).2 this |>.congr fun k => by push_cast; ring
  have hbound : ∀ k y, y ∈ t → ‖g' k y‖ ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
    intro k y hy
    simp only [g', norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (hlow k y hy) 2)
  have hs0 : Summable fun k => g k σ := (hasSum_gammaLogDeriv χ (hret _ hσt)).summable
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball _ _).isPreconnected hgd hbound hσt hs0 hσt
  have hev : gammaLogDeriv χ =ᶠ[nhds (σ : ℂ)] fun z => gammaLogDeriv χ 2 + ∑' k, g k z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hσt] with z hz
    rw [(hasSum_gammaLogDeriv χ (hret z hz)).tsum_eq]; ring
  have hsum' : Summable (fun k : ℕ => 1 / ((σ : ℂ) + mk k) ^ 2) :=
    Summable.of_norm_bounded hu fun k => hbound k σ hσt
  exact ⟨hsum', (hderiv.const_add _).congr_of_eventuallyEq hev⟩

/-- `(L'/L)'(σ) = −Σ_ρ m_ρ/(σ−ρ)² − Σ_k 1/(σ+m_k)²` for `σ > 1`, under GRH. -/
theorem deriv_logDeriv_L (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ) :
    deriv (fun s => deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) σ
      = -(∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
              * (1 / ((σ : ℂ) - ρ) ^ 2))
        - ∑' k : ℕ, 1 / ((σ : ℂ) + ((2 * k + parity χ : ℕ) : ℂ)) ^ 2 := by
  obtain ⟨-, hD⟩ := hasDerivAt_D hGRH hprim hχ hσ
  obtain ⟨-, hG⟩ := hasDerivAt_G χ hσ
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun s => deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
      =ᶠ[nhds (σ : ℂ)] fun s => D χ s - gammaLogDeriv χ s := by
    filter_upwards [hopen.mem_nhds (show 1 < ((σ : ℂ)).re by simp; linarith)] with s hs
    exact logDeriv_LFunction_eq hχ hs
  rw [((hD.sub hG).congr_of_eventuallyEq hev).deriv]

end LLS.ShiftLogAux
