import Lindelof.Monotone
import Lindelof.GammaRatio

/-!
# Step 4: consequences for `ζ` of Steps 2 and 3

`ζ = ξ / (s (s - 1) Γℝ(s))`, so monotonicity of `|ξ|` moves bounds for `ζ` to the left at the
cost of a Gamma ratio.
-/

namespace Lindelof

open Complex Erdos985.Analytic

/-- `‖ξ(s)‖ = ‖s‖ ‖s - 1‖ ‖Γℝ(s)‖ ‖ζ(s)‖` for `Re s > 0`, `s ≠ 1`. -/
lemma norm_xiZeta_eq_mul {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖xiZeta s‖ = ‖s‖ * ‖s - 1‖ * ‖Gammaℝ s‖ * ‖riemannZeta s‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]
  rw [xiZeta_eq hs0 hs1, hΛ]
  simp only [norm_mul]
  ring

/-- `‖Γℝ(σ + it)‖ = π^{-σ/2} ‖Γ(σ/2 + it/2)‖`. -/
lemma norm_Gammaℝ_eq (σ t : ℝ) :
    ‖Gammaℝ (σ + t * I)‖ = Real.pi ^ (-σ / 2) * ‖Gamma ((σ / 2 : ℝ) + (t / 2 : ℝ) * I)‖ := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  · simp [neg_div]
  · push_cast; ring_nf

/-- The Gamma ratio bound of Step 3, extended to `|y| ≥ 1/2` by compactness. -/
lemma norm_Gamma_le_rpow_mul' :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b y : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → 1 / 2 ≤ |y| →
      ‖Gamma (b + y * I)‖ ≤ C * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by
  obtain ⟨C₀, hC₀⟩ := norm_Gamma_le_rpow_mul
  set K : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 / 2 ≤ |z.im| ∧ |z.im| ≤ 1} with hK
  have hKcl : IsClosed K :=
    (isClosed_le continuous_const continuous_re).inter
      ((isClosed_le continuous_re continuous_const).inter
        ((isClosed_le continuous_const (continuous_abs.comp continuous_im)).inter
          (isClosed_le (continuous_abs.comp continuous_im) continuous_const)))
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2, fun z hz => ?_⟩
    obtain ⟨h1, h2, -, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hnpole : ∀ z ∈ K, ∀ m : ℕ, z ≠ -m := by
    intro z hz m hm
    have := hz.2.2.1
    rw [hm] at this
    simp at this
    linarith
  have hcont : ContinuousOn (fun z => ‖Gamma z‖) K := fun z hz =>
    (differentiableAt_Gamma z (hnpole z hz)).continuousAt.norm.continuousWithinAt
  have hne : K.Nonempty := ⟨(1 / 2 : ℂ) + I, by norm_num [hK]⟩
  obtain ⟨z₀, hz₀K, hz₀⟩ := hKc.exists_isMinOn hne hcont
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  have hm : 0 < ‖Gamma z₀‖ :=
    norm_pos_iff.2 (Gamma_ne_zero (hnpole z₀ hz₀K))
  set m := ‖Gamma z₀‖
  refine ⟨max C₀ 0 + max M 0 / m, add_nonneg (le_max_right _ _)
    (div_nonneg (le_max_right _ _) hm.le), ?_⟩
  intro a b y ha hab hb hy
  have hpow1 : 1 ≤ (2 * |y|) ^ (b - a) := Real.one_le_rpow (by linarith) (by linarith)
  have hG0 : 0 ≤ ‖Gamma (a + y * I)‖ := norm_nonneg _
  have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
  have hMm : 0 ≤ max M 0 / m := div_nonneg (le_max_right _ _) hm.le
  by_cases hy1 : 1 ≤ |y|
  · calc ‖Gamma (b + y * I)‖ ≤ C₀ * |y| ^ (b - a) * ‖Gamma (a + y * I)‖ :=
          hC₀ a b y ha hab hb hy1
      _ ≤ max C₀ 0 * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by
          apply mul_le_mul_of_nonneg_right _ hG0
          apply mul_le_mul (le_max_left _ _) _ (by positivity) hC0
          exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg y]) (by linarith)
      _ ≤ (max C₀ 0 + max M 0 / m) * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by
          apply mul_le_mul_of_nonneg_right _ hG0
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  · replace hy1 := not_le.mp hy1
    have hbK : (b : ℂ) + y * I ∈ K := by
      simp only [hK, Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨by linarith, hb, hy, hy1.le⟩
    have haK : (a : ℂ) + y * I ∈ K := by
      simp only [hK, Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨ha, by linarith, hy, hy1.le⟩
    have h1 : ‖Gamma (b + y * I)‖ ≤ max M 0 :=
      le_trans (by simpa using hM _ hbK) (le_max_left _ _)
    have h2 : m ≤ ‖Gamma (a + y * I)‖ := isMinOn_iff.mp hz₀ _ haK
    calc ‖Gamma (b + y * I)‖ ≤ max M 0 / m * m := by rw [div_mul_cancel₀ _ hm.ne']; exact h1
      _ ≤ max M 0 / m * ‖Gamma (a + y * I)‖ := mul_le_mul_of_nonneg_left h2 hMm
      _ ≤ (max C₀ 0 + max M 0 / m) * ‖Gamma (a + y * I)‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hG0
      _ ≤ (max C₀ 0 + max M 0 / m) * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by
          rw [mul_right_comm]
          exact le_mul_of_one_le_right (by positivity) hpow1

/-- `‖Γ(x + 1 + iy)‖ = ‖x + iy‖ ‖Γ(x + iy)‖` off the real axis. -/
lemma norm_Gamma_add_one_eq (x y : ℝ) (hy : y ≠ 0) :
    ‖Gamma ((x + 1 : ℝ) + y * I)‖ = ‖(x : ℂ) + y * I‖ * ‖Gamma (x + y * I)‖ := by
  have hne : (x : ℂ) + y * I ≠ 0 := fun h => hy (by simpa using congrArg Complex.im h)
  have : ((x + 1 : ℝ) : ℂ) + y * I = ((x : ℂ) + y * I) + 1 := by push_cast; ring
  rw [this, Gamma_add_one _ hne, norm_mul]

/-- The Gamma ratio bound on the wider range `0 ≤ a ≤ b ≤ 2`, from `Γ(s + 1) = s Γ(s)`. -/
lemma norm_Gamma_le_rpow_mul_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b y : ℝ, 0 ≤ a → a ≤ b → b ≤ 2 → 1 / 2 ≤ |y| →
      ‖Gamma (b + y * I)‖ ≤ C * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_le_rpow_mul'
  refine ⟨C + 3 * C + 3 * C ^ 2, by positivity, fun a b y ha hab hb hy => ?_⟩
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; norm_num at hy
  have hpow : ∀ e : ℝ, 0 ≤ (2 * |y|) ^ e := fun e => Real.rpow_nonneg (by positivity) e
  -- both arguments at least `1`: shift down by one
  have hhigh : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 →
      ‖Gamma (b + y * I)‖ ≤ 3 * C * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by
    intro a b ha hab hb
    have e1 := norm_Gamma_add_one_eq (a - 1) y hy0
    have e2 := norm_Gamma_add_one_eq (b - 1) y hy0
    rw [show a - 1 + 1 = a by ring] at e1
    rw [show b - 1 + 1 = b by ring] at e2
    rw [e1, e2]
    have hG := hC (a - 1) (b - 1) y (by linarith) (by linarith) (by linarith) hy
    rw [show b - 1 - (a - 1) = b - a by ring] at hG
    have hlin : ‖((b - 1 : ℝ) : ℂ) + y * I‖ ≤ 3 * ‖((a - 1 : ℝ) : ℂ) + y * I‖ := by
      have hy' : 1 / 2 ≤ ‖((a - 1 : ℝ) : ℂ) + y * I‖ :=
        hy.trans (by simpa using abs_im_le_norm (((a - 1 : ℝ) : ℂ) + y * I))
      have : ((b - 1 : ℝ) : ℂ) + y * I = (((a - 1 : ℝ) : ℂ) + y * I) + ((b - a : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    calc ‖((b - 1 : ℝ) : ℂ) + y * I‖ * ‖Gamma (((b - 1 : ℝ) : ℂ) + y * I)‖
        ≤ (3 * ‖((a - 1 : ℝ) : ℂ) + y * I‖) *
            (C * (2 * |y|) ^ (b - a) * ‖Gamma (((a - 1 : ℝ) : ℂ) + y * I)‖) :=
          mul_le_mul hlin hG (norm_nonneg _) (by positivity)
      _ = 3 * C * (2 * |y|) ^ (b - a) *
            (‖((a - 1 : ℝ) : ℂ) + y * I‖ * ‖Gamma (((a - 1 : ℝ) : ℂ) + y * I)‖) := by ring
  have hG0 : 0 ≤ ‖Gamma (a + y * I)‖ := norm_nonneg _
  by_cases hb1 : b ≤ 1
  · refine (hC a b y ha hab hb1 hy).trans ?_
    gcongr
    nlinarith
  by_cases ha1 : 1 ≤ a
  · refine (hhigh a b ha1 hab hb).trans ?_
    gcongr
    nlinarith
  push Not at hb1 ha1
  have h1 := hhigh 1 b le_rfl hb1.le hb
  have h2 := hC a 1 y ha ha1.le le_rfl hy
  have hsplit : (2 * |y|) ^ (b - a) = (2 * |y|) ^ (b - 1) * (2 * |y|) ^ (1 - a) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  have h1' : ‖Gamma ((1 : ℝ) + y * I)‖ ≤ C * (2 * |y|) ^ (1 - a) * ‖Gamma (a + y * I)‖ := h2
  calc ‖Gamma (b + y * I)‖ ≤ 3 * C * (2 * |y|) ^ (b - 1) * ‖Gamma ((1 : ℝ) + y * I)‖ := h1
    _ ≤ 3 * C * (2 * |y|) ^ (b - 1) * (C * (2 * |y|) ^ (1 - a) * ‖Gamma (a + y * I)‖) := by
        gcongr
    _ = 3 * C ^ 2 * (2 * |y|) ^ (b - a) * ‖Gamma (a + y * I)‖ := by rw [hsplit]; ring
    _ ≤ _ := by
        gcongr
        nlinarith

/-- Under RH, a bound for the factor `s (s - 1) Γℝ(s)` moves bounds for `ζ` leftwards. -/
lemma norm_zeta_le_of_factor (hRH : RiemannHypothesis) {σ σ' t K : ℝ} (hσ : 1 / 2 ≤ σ)
    (hσσ' : σ ≤ σ') (ht : 1 ≤ |t|)
    (hK : ‖(σ' : ℂ) + t * I‖ * ‖(σ' : ℂ) + t * I - 1‖ * ‖Gammaℝ (σ' + t * I)‖ ≤
      K * (‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I - 1‖ * ‖Gammaℝ (σ + t * I)‖)) :
    ‖riemannZeta (σ + t * I)‖ ≤ K * ‖riemannZeta (σ' + t * I)‖ := by
  have hne : ∀ x : ℝ, (x : ℂ) + t * I ≠ 1 := fun x h => by
    have := congrArg im h
    simp at this
    rw [this] at ht
    norm_num at ht
  have hre : ∀ x : ℝ, ((x : ℂ) + t * I).re = x := fun x => by simp
  have hxi := norm_xiZeta_le_of_half_le hRH t hσ hσσ'
  rw [norm_xiZeta_eq_mul (by rw [hre]; linarith) (hne σ),
    norm_xiZeta_eq_mul (by rw [hre]; linarith) (hne σ')] at hxi
  have hP : 0 < ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I - 1‖ * ‖Gammaℝ (σ + t * I)‖ := by
    have h0 : (σ : ℂ) + t * I ≠ 0 := fun h => by
      have := congrArg re h; rw [hre] at this; simp at this; linarith
    have h1 : (σ : ℂ) + t * I - 1 ≠ 0 := sub_ne_zero.mpr (hne σ)
    have h2 := Gammaℝ_ne_zero_of_re_pos (s := (σ : ℂ) + t * I) (by rw [hre]; linarith)
    positivity
  refine le_of_mul_le_mul_left ?_ hP
  calc _ ≤ _ := hxi
    _ ≤ K * (‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I - 1‖ * ‖Gammaℝ (σ + t * I)‖) *
          ‖riemannZeta (σ' + t * I)‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
    _ = _ := by ring

/-- Shifting right by at most `c` changes the norm by at most a factor `1 + c` once `|Im| ≥ 1`. -/
lemma norm_add_ofReal_le {z : ℂ} {d c : ℝ} (hz : 1 ≤ |z.im|) (hd : 0 ≤ d) (hdc : d ≤ c) :
    ‖z + d‖ ≤ (1 + c) * ‖z‖ := by
  have h1 : 1 ≤ ‖z‖ := hz.trans (abs_im_le_norm z)
  calc ‖z + d‖ ≤ ‖z‖ + ‖(d : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ + d := by rw [norm_real, Real.norm_of_nonneg hd]
    _ ≤ (1 + c) * ‖z‖ := by nlinarith

/-- The polynomial factor `‖s‖ ‖s - 1‖` at two points of the same height. -/
lemma norm_poly_le {σ σ' t c : ℝ} (ht : 1 ≤ |t|) (h : σ ≤ σ') (hc : σ' - σ ≤ c) :
    ‖(σ' : ℂ) + t * I‖ * ‖(σ' : ℂ) + t * I - 1‖ ≤
      (1 + c) ^ 2 * (‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I - 1‖) := by
  have e1 : (σ' : ℂ) + t * I = ((σ : ℂ) + t * I) + ((σ' - σ : ℝ) : ℂ) := by push_cast; ring
  have e2 : (σ' : ℂ) + t * I - 1 = ((σ : ℂ) + t * I - 1) + ((σ' - σ : ℝ) : ℂ) := by
    push_cast; ring
  have hi1 : 1 ≤ |((σ : ℂ) + t * I).im| := by simpa using ht
  have hi2 : 1 ≤ |((σ : ℂ) + t * I - 1).im| := by simpa using ht
  have hd : 0 ≤ σ' - σ := by linarith
  rw [e2, e1]
  have a1 := norm_add_ofReal_le hi1 hd hc
  have a2 := norm_add_ofReal_le hi2 hd hc
  have hc0 : 0 ≤ 1 + c := by linarith
  calc _ ≤ ((1 + c) * ‖(σ : ℂ) + t * I‖) * ((1 + c) * ‖(σ : ℂ) + t * I - 1‖) :=
        mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Under RH, `‖ζ(1/2 + it)‖ ≤ C t^{δ/2} ‖ζ(1/2 + δ + it)‖`, uniformly in `δ ∈ (0, 1/2]`. -/
theorem norm_zeta_half_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * t ^ (δ / 2) * ‖riemannZeta ((1 / 2 + δ : ℝ) + t * I)‖ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_Gamma_le_rpow_mul'
  refine ⟨(1 + 1 / 2) ^ 2 * C₁, fun δ hδ hδ' t ht => ?_⟩
  have ht' : 1 ≤ |t| := by rwa [abs_of_nonneg (by linarith)]
  have hcast : (1 / 2 : ℂ) + t * I = ((1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  rw [hcast]
  apply norm_zeta_le_of_factor hRH (by norm_num) (by linarith) ht'
  have hpoly := norm_poly_le (c := 1 / 2) ht' (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + δ)
    (by linarith)
  rw [norm_Gammaℝ_eq, norm_Gammaℝ_eq]
  have hy : 1 / 2 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
  have hG := hC₁ (1 / 2 / 2) ((1 / 2 + δ) / 2) (t / 2) (by norm_num) (by linarith) (by linarith) hy
  have hexp : (2 * |t / 2|) ^ ((1 / 2 + δ) / 2 - 1 / 2 / 2) = t ^ (δ / 2) := by
    rw [abs_div, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
    ring_nf
  rw [hexp] at hG
  have hπ : Real.pi ^ (-(1 / 2 + δ) / 2) ≤ Real.pi ^ (-(1 / 2 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  set P := ‖((1 / 2 : ℝ) : ℂ) + t * I‖ * ‖((1 / 2 : ℝ) : ℂ) + t * I - 1‖
  set P' := ‖((1 / 2 + δ : ℝ) : ℂ) + t * I‖ * ‖((1 / 2 + δ : ℝ) : ℂ) + t * I - 1‖
  set G := ‖Gamma (((1 / 2 / 2 : ℝ)) + ((t / 2 : ℝ)) * I)‖
  set G' := ‖Gamma ((((1 / 2 + δ) / 2 : ℝ)) + ((t / 2 : ℝ)) * I)‖
  have hP0 : 0 ≤ P := by positivity
  have hG'0 : 0 ≤ G' := norm_nonneg _
  have hG0 : 0 ≤ G := norm_nonneg _
  have htp : 0 ≤ t ^ (δ / 2) := by positivity
  have hpi0 : 0 ≤ Real.pi ^ (-(1 / 2 + δ) / 2) := by positivity
  have hpi1 : 0 ≤ Real.pi ^ (-(1 / 2 : ℝ) / 2) := by positivity
  calc P' * (Real.pi ^ (-(1 / 2 + δ) / 2) * G')
      ≤ ((1 + 1 / 2) ^ 2 * P) * (Real.pi ^ (-(1 / 2 : ℝ) / 2) * (C₁ * t ^ (δ / 2) * G)) := by
        apply mul_le_mul hpoly _ (by positivity) (by positivity)
        exact mul_le_mul hπ hG hG'0 hpi1
    _ = (1 + 1 / 2) ^ 2 * C₁ * t ^ (δ / 2) * (P * (Real.pi ^ (-(1 / 2 : ℝ) / 2) * G)) := by ring

/-- `‖ζ(s)‖ ≤ ∑ 1/(n+1)²` for `Re s ≥ 2`. -/
lemma norm_zeta_le_of_two_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith)]
  refine tsum_of_norm_bounded hsum.hasSum (fun n => ?_)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_one, show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos hn]
  apply one_div_le_one_div_of_le (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (by push_cast; exact hs)

/-- Under RH, `ζ` grows at most linearly on `σ ≥ 1/2`, `|t| ≥ 1`. -/
theorem norm_zeta_le_poly (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_Gamma_le_rpow_mul'
  set Z := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨Z * (1 + (1 + 2) ^ 2 * C₁), fun s hσ ht => ?_⟩
  have hK0 : 0 ≤ (1 + 2) ^ 2 * C₁ := by positivity
  by_cases h2 : 2 ≤ s.re
  · calc ‖riemannZeta s‖ ≤ Z := norm_zeta_le_of_two_le h2
      _ ≤ Z * (1 + (1 + 2) ^ 2 * C₁) * |s.im| := by
        rw [mul_assoc]
        apply le_mul_of_one_le_right hZ0
        nlinarith
  replace h2 := not_le.mp h2
  set σ := s.re
  set t := s.im
  have hs : s = (σ : ℂ) + t * I := (re_add_im s).symm
  rw [hs]
  have hcalc : ‖riemannZeta (σ + t * I)‖ ≤ (1 + 2) ^ 2 * C₁ * |t| *
      ‖riemannZeta ((2 : ℝ) + t * I)‖ := by
    apply norm_zeta_le_of_factor hRH hσ h2.le ht
    have hpoly := norm_poly_le (c := 2) ht h2.le (by linarith)
    rw [norm_Gammaℝ_eq, norm_Gammaℝ_eq]
    have hy : 1 / 2 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
    have hG := hC₁ (σ / 2) (2 / 2) (t / 2) (by linarith) (by linarith) (by norm_num) hy
    have hexp : (2 * |t / 2|) ^ (2 / 2 - σ / 2) ≤ |t| := by
      rw [abs_div, abs_two, mul_div_cancel₀ _ two_ne_zero]
      calc |t| ^ (2 / 2 - σ / 2) ≤ |t| ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht (by linarith)
        _ = |t| := Real.rpow_one _
    have hπ : Real.pi ^ (-(2 : ℝ) / 2) ≤ Real.pi ^ (-σ / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    set P := ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I - 1‖
    set G := ‖Gamma (((σ / 2 : ℝ)) + ((t / 2 : ℝ)) * I)‖
    set G' := ‖Gamma ((((2 : ℝ) / 2 : ℝ)) + ((t / 2 : ℝ)) * I)‖
    have hP0 : 0 ≤ P := by positivity
    have hG'0 : 0 ≤ G' := norm_nonneg _
    have hG0 : 0 ≤ G := norm_nonneg _
    have hpi0 : 0 ≤ Real.pi ^ (-(2 : ℝ) / 2) := by positivity
    have hpi1 : 0 ≤ Real.pi ^ (-σ / 2) := by positivity
    have hG2 : G' ≤ C₁ * |t| * G := by
      calc G' ≤ C₁ * (2 * |t / 2|) ^ (2 / 2 - σ / 2) * G := hG
        _ ≤ C₁ * |t| * G := by gcongr
    calc _ ≤ ((1 + 2) ^ 2 * P) * (Real.pi ^ (-σ / 2) * (C₁ * |t| * G)) := by
          apply mul_le_mul hpoly _ (by positivity) (by positivity)
          exact mul_le_mul hπ hG2 hG'0 hpi1
      _ = (1 + 2) ^ 2 * C₁ * |t| * (P * (Real.pi ^ (-σ / 2) * G)) := by ring
  have hz2 := norm_zeta_le_of_two_le (s := ((2 : ℝ) : ℂ) + t * I) (by simp)
  calc _ ≤ (1 + 2) ^ 2 * C₁ * |t| * ‖riemannZeta ((2 : ℝ) + t * I)‖ := hcalc
    _ ≤ (1 + 2) ^ 2 * C₁ * |t| * Z := by gcongr
    _ ≤ Z * (1 + (1 + 2) ^ 2 * C₁) * |t| := by nlinarith [abs_nonneg t]

end Lindelof
