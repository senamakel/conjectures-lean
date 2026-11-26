import Speiser.Statement
import Speiser.Xi
import Speiser.Gamma
import Erdos985.Analytic.Digamma.EulerMascheroni

/-!
# RH ⇒ `ζ'(s) ≠ 0` for `0 < Re s < 1/2`, `|Im s| ≤ 5/2`

A size argument on the real parts. Suppose `ζ'(s) = 0` there, so that
`ξ'/ξ(s) = E(s) := 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)` (`Speiser.Xi`).

1. `ξ'(1) = Λ₀(1) = 1 + (γ - log 4π)/2 < 0.0295`, and under RH the Hadamard sum gives
   `Re ξ'/ξ(1) = Σ_ρ m_ρ Re 1/(1-ρ) = Σ_ρ m_ρ (1/2)/(1/4 + γ_ρ²)`. A single term is at most the
   sum, so every zero has `γ_ρ² ≥ 16` (`im_sq_ge_of_RH`).
2. For `|γ| ≥ 4` and `|t| ≤ 5/2`: `(1/2 - σ)/|s-ρ|² ≤ (65/9) (1/2)/(1/4 + γ²)`, so
   `Re ξ'/ξ(s) = Σ_ρ m_ρ (σ - 1/2)/|s-ρ|² ≥ -(65/9) Re ξ'/ξ(1) > -0.214`.
3. `Re E(s) < -0.3`: `Re 1/(s-1) ≤ -1/13`, and each term of `Re (ψ(1+s/2) - ψ(1))` is at most
   `dTerm k` (the exact minimum of `u/(u² + 25/16)` over `u ∈ [n, n+1/4]`), and at most
   `(15/8)/n²` for `n ≥ 2`. Ten terms plus `(15/8)(π²/6 - Σ_{n ≤ 10} 1/n²)` give `< 1.105`;
   with `γ > 0.57688` and `log π > 1.14` the total is `< -0.38`.
-/

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux

namespace Speiser

/-! ### Step 1: `ξ'(1)` and the first zero -/

lemma deriv_xiZeta_one_eq :
    deriv xiZeta 1 = 1 + ((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * Real.pi)) / 2 := by
  have hΛ := (differentiable_completedZeta₀ 1).hasDerivAt
  have h1 : HasDerivAt (fun s : ℂ => s * (s - 1)) (2 * 1 - 1) 1 := by
    have := (hasDerivAt_id' (1 : ℂ)).mul ((hasDerivAt_id' (1 : ℂ)).sub_const 1)
    convert this using 1; ring
  have h := (h1.mul hΛ).add_const 1
  have hx : (fun x => ((fun s : ℂ => s * (s - 1)) * completedRiemannZeta₀) x + 1) = xiZeta := by
    funext x; simp [xiZeta, Pi.mul_apply]
  rw [hx] at h
  rw [h.deriv, completedRiemannZeta₀_one]; ring

/-- `log π > 1.14`, from `π > 3.14` and `e^{1.14} = e · e^{0.14} < 2.71828183 · 1.1505`. -/
lemma log_pi_gt : 1.14 < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have hb := Real.exp_bound (x := 0.14) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hb' := (abs_le.mp hb).2
  have he := Real.exp_one_lt_d9
  have : Real.exp 1.14 = Real.exp 1 * Real.exp 0.14 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  have hp := Real.pi_gt_d2
  nlinarith [Real.exp_pos 0.14, Real.exp_pos 1]

lemma re_deriv_xiZeta_one_lt : (deriv xiZeta 1).re < 0.0295 := by
  rw [deriv_xiZeta_one_eq]
  have hlog : Complex.log (4 * Real.pi) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; ring_nf
  rw [hlog]
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hre : (1 + (((Real.eulerMascheroniConstant : ℝ) : ℂ) -
      ((Real.log (4 * Real.pi) : ℝ) : ℂ)) / 2).re =
      1 + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 := by
    simp
  rw [hre, h4]
  linarith [log_pi_gt, eulerMascheroni_lt, Real.log_two_gt_d9]

lemma re_one_div_one_sub_eq {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ((1 : ℂ) / (1 - ρ)).re = (1 / 2) / (1 / 4 + ρ.im ^ 2) := by
  simp only [one_div, inv_re, normSq_apply, sub_re, one_re, sub_im, one_im, hρ]
  ring

/-- Under RH every zero of `ξ` has `γ² ≥ 16`. -/
theorem im_sq_ge_of_RH (hRH : RiemannHypothesis) (ρ : {ρ : ℂ // xiZeta ρ = 0}) :
    16 ≤ (ρ : ℂ).im ^ 2 := by
  have hS := hasSum_re_logDeriv_xiZeta hRH (z := 1) (by rw [xiZeta_one]; exact one_ne_zero)
  rw [xiZeta_one, div_one] at hS
  have hnn : ∀ j : {ρ : ℂ // xiZeta ρ = 0},
      0 ≤ (analyticOrderNatAt xiZeta (j : ℂ) : ℝ) * ((1 : ℂ) / (1 - j)).re := fun j => by
    rw [re_one_div_one_sub_eq (re_eq_half_of_xiZeta_eq_zero hRH j.2)]
    positivity
  have h1 := le_hasSum hS ρ (fun j _ => hnn j)
  have hm : (1 : ℝ) ≤ analyticOrderNatAt xiZeta (ρ : ℂ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xiZeta_order_ne_zero ρ.2)
  rw [re_one_div_one_sub_eq (re_eq_half_of_xiZeta_eq_zero hRH ρ.2)] at h1
  have hlt := re_deriv_xiZeta_one_lt
  have hpos : 0 < (1 / 2 : ℝ) / (1 / 4 + (ρ : ℂ).im ^ 2) := by positivity
  have h2 : (1 / 2 : ℝ) / (1 / 4 + (ρ : ℂ).im ^ 2) < 0.0295 := by nlinarith
  rw [div_lt_iff₀ (by positivity)] at h2
  nlinarith

/-! ### Step 2: the zero sum at `s` -/

/-- For a zero `ρ = 1/2 + iγ` with `γ² ≥ 16` and `|Im z| ≤ 5/2`, `Re z ≤ 1/2`:
`Re 1/(z-ρ) ≥ -(65/9) Re 1/(1-ρ)`. -/
lemma re_one_div_sub_ge {z ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : 16 ≤ ρ.im ^ 2)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1 / 2) (ht : |z.im| ≤ 5 / 2) :
    -(65 / 9) * ((1 : ℂ) / (1 - ρ)).re ≤ ((1 : ℂ) / (z - ρ)).re := by
  rw [re_one_div_one_sub_eq hρ]
  have hre : ((1 : ℂ) / (z - ρ)).re =
      (z.re - 1 / 2) / ((z.re - 1 / 2) ^ 2 + (z.im - ρ.im) ^ 2) := by
    simp only [one_div, inv_re, normSq_apply, sub_re, sub_im, hρ]; ring
  rw [hre]
  set a := 1 / 2 - z.re with ha
  set d := z.im - ρ.im with hd
  set g := |ρ.im| with hg
  have hg4 : 4 ≤ g := by
    have : (4 : ℝ) ^ 2 ≤ g ^ 2 := by rw [hg, sq_abs]; linarith
    nlinarith [abs_nonneg ρ.im]
  have hdg : g - 5 / 2 ≤ |d| := by
    have := abs_sub_abs_le_abs_sub ρ.im z.im
    rw [abs_sub_comm] at this
    rw [hd]; linarith
  have hd2 : (g - 5 / 2) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs d]; exact pow_le_pow_left₀ (by linarith) hdg 2
  have hγg : ρ.im ^ 2 = g ^ 2 := (sq_abs _).symm
  have hK : 1 / 4 + ρ.im ^ 2 ≤ 65 / 9 * d ^ 2 := by
    rw [hγg]; nlinarith [mul_nonneg (sub_nonneg.mpr hg4) (show (0 : ℝ) ≤ 224 * g - 404 by linarith)]
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 / 2 := by linarith
  have hdpos : 0 < d ^ 2 := by nlinarith
  rw [show z.re - 1 / 2 = -a by rw [ha]; ring]
  rw [neg_div, neg_le_neg_iff.symm, neg_neg, neg_mul, neg_neg]
  -- a / (a² + d²) ≤ (65/9) (1/2)/(1/4 + γ²)
  rw [div_le_iff₀ (by positivity)]
  have hpos : 0 < 1 / 4 + ρ.im ^ 2 := by positivity
  have hrw : 65 / 9 * (1 / 2 / (1 / 4 + ρ.im ^ 2)) * ((-a) ^ 2 + d ^ 2) =
      (65 / 9 * (1 / 2) * ((-a) ^ 2 + d ^ 2)) / (1 / 4 + ρ.im ^ 2) := by
    field_simp
  rw [hrw, le_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hK ha0, mul_nonneg (sub_nonneg.mpr ha1) hdpos.le,
    sq_nonneg a]

/-! ### Step 3: the archimedean part below height `5/2` -/

/-- Upper bound for the real part of the `k`-th digamma-series term, `|t| ≤ 5/2`. -/
noncomputable def dTerm (k : ℕ) : ℝ :=
  if k = 0 then 1 - 1 / (1 + 25 / 16)
  else 1 / ((k : ℝ) + 1) - ((k : ℝ) + 1 + 1 / 4) / (((k : ℝ) + 1 + 1 / 4) ^ 2 + 25 / 16)

lemma term_re_upper (k : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2)
    (ht : s.im ^ 2 ≤ 25 / 4) :
    (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + s / 2))).re ≤ dTerm k := by
  set n : ℝ := (k : ℝ) + 1 with hn
  set u : ℝ := n + s.re / 2 with hu
  set v : ℝ := s.im / 2 with hv
  have hn1 : 1 ≤ n := by simp [hn]
  have hre1 : (1 / ((k : ℂ) + 1)).re = 1 / n := by
    rw [show ((k : ℂ) + 1) = ((n : ℝ) : ℂ) by simp [hn]]
    rw [← ofReal_one, ← ofReal_div, ofReal_re]
  have hre2 : (1 / ((k : ℂ) + (1 + s / 2))).re = u / (u ^ 2 + v ^ 2) := by
    simp only [one_div, inv_re, normSq_apply, add_re, add_im, natCast_re, natCast_im, one_re,
      one_im, div_re, div_im, hu, hv, hn]
    norm_num
    ring_nf
  rw [sub_re, hre1, hre2]
  have hun : n ≤ u := by simp [hu]; linarith
  have hun' : u ≤ n + 1 / 4 := by simp [hu]; linarith
  have hv2 : v ^ 2 ≤ 25 / 16 := by simp [hv]; nlinarith
  have hupos : 0 < u := by linarith
  have hmono : u / (u ^ 2 + 25 / 16) ≤ u / (u ^ 2 + v ^ 2) :=
    div_le_div_of_nonneg_left hupos.le (by positivity) (by linarith)
  unfold dTerm
  split_ifs with hk
  · have hn' : n = 1 := by simp [hn, hk]
    have := frac_le_of_le (u := 1) (a := u) (w := 25 / 16) (by linarith) (by nlinarith)
      (by norm_num)
    rw [hn'] at *
    norm_num at this ⊢
    linarith
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have := frac_le_of_ge (u := n + 1 / 4) (n := u) (w := 25 / 16) hupos hun' (by nlinarith)
      (by norm_num)
    rw [← hn]; linarith

lemma dTerm_le (k : ℕ) (hk : k ≠ 0) : dTerm k ≤ (15 / 8) / ((k : ℝ) + 1) ^ 2 := by
  unfold dTerm
  rw [if_neg hk]
  set n : ℝ := (k : ℝ) + 1 with hn
  have hn2 : 2 ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    simp [hn]; linarith
  have hA : 0 < (n + 1 / 4) ^ 2 + 25 / 16 := by positivity
  rw [div_sub_div _ _ (by positivity) hA.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg n, mul_pos (show (0 : ℝ) < n by linarith) (show (0 : ℝ) < n by linarith)]

/-- The comparison series: `dTerm k` for `k < 10`, then `(15/8)/(k+1)²`. -/
noncomputable def eTerm (k : ℕ) : ℝ := if k < 10 then dTerm k else (15 / 8) / ((k : ℝ) + 1) ^ 2

lemma hasSum_eTerm : HasSum eTerm (∑ k ∈ Finset.range 10,
    (dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2) + 15 / 8 * (Real.pi ^ 2 / 6)) := by
  have hz : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hf : HasSum (fun k : ℕ => if k < 10 then dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2 else 0)
      (∑ k ∈ Finset.range 10, (dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2)) := by
    have h0 : HasSum (fun k : ℕ => if k < 10 then dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2 else 0)
        (∑ k ∈ Finset.range 10,
          (if k < 10 then dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2 else 0)) :=
      hasSum_sum_of_ne_finset_zero
        (fun k hk => by simp only [Finset.mem_range] at hk; simp [hk])
    have hs : (∑ k ∈ Finset.range 10,
        (if k < 10 then dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2 else 0)) =
        ∑ k ∈ Finset.range 10, (dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2) :=
      Finset.sum_congr rfl fun k hk => by simp only [Finset.mem_range] at hk; simp [hk]
    rw [hs] at h0
    exact h0
  have heq : eTerm = fun k : ℕ =>
      (if k < 10 then dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2 else 0) +
        15 / 8 * (1 / ((k : ℝ) + 1) ^ 2) := by
    funext k
    unfold eTerm
    split_ifs <;> ring
  rw [heq]
  exact hf.add (hz.mul_left (15 / 8))

lemma dSum_le : ∑ k ∈ Finset.range 10, (dTerm k - (15 / 8) / ((k : ℝ) + 1) ^ 2) ≤ -1.98 := by
  simp only [dTerm, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **The archimedean part is negative below height `5/2`.** -/
theorem re_archimedean_lt {s : ℂ} (h0 : 0 < s.re) (h1 : s.re ≤ 1 / 2) (ht : |s.im| ≤ 5 / 2) :
    (1 / s + 1 / (s - 1) +
      (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2))).re < -0.3 := by
  have ht2 : s.im ^ 2 ≤ 25 / 4 := by
    have := sq_abs s.im
    nlinarith [abs_nonneg s.im]
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hrec : digamma (s / 2 + 1) = digamma (s / 2) + (s / 2)⁻¹ := by
    refine digamma_apply_add_one _ fun m h => ?_
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hw : 1 / 2 < (1 + s / 2).re := by simp; linarith
  have hSre := Complex.hasSum_re (Erdos985.Analytic.BoundsAux.hasSum_digamma hw)
  have hup := hasSum_le (fun k => by
      show (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + s / 2))).re ≤ eTerm k
      unfold eTerm
      split_ifs with hk
      · exact term_re_upper k h0.le h1 ht2
      · exact (term_re_upper k h0.le h1 ht2).trans (dTerm_le k (by omega)))
    hSre hasSum_eTerm
  have hpsi1 : digamma 1 = ((-Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [digamma_one]; push_cast; ring
  have hE : 1 / s + 1 / (s - 1) +
      (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2)) =
      1 / (s - 1) + (-(1 / 2) * (Real.log Real.pi : ℂ)) +
        (1 / 2) * (digamma (1 + s / 2) - digamma 1) + (1 / 2) * digamma 1 := by
    rw [add_comm 1 (s / 2), hrec]
    field_simp
    ring
  rw [hE]
  have hd1 : (digamma 1).re = -Real.eulerMascheroniConstant := by rw [hpsi1, ofReal_re]
  have hre_inv : (1 / (s - 1)).re = (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
    simp only [one_div, inv_re, normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero]
    ring_nf
  have hre_inv' : (1 / (s - 1)).re ≤ -1 / 13 := by
    have hD : 0 < (s.re - 1) ^ 2 + s.im ^ 2 := by nlinarith
    rw [hre_inv, div_le_div_iff₀ hD (by norm_num)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show (0 : ℝ) ≤ 1 - s.re - 1 / 2 by linarith)
      (show 1 - s.re - 25 / 2 ≤ 0 by linarith)]
  have hgoal : (1 / (s - 1) + (-(1 / 2) * (Real.log Real.pi : ℂ)) +
      (1 / 2) * (digamma (1 + s / 2) - digamma 1) +
        (1 / 2) * digamma 1).re =
      (1 / (s - 1)).re - 1 / 2 * Real.log Real.pi +
        1 / 2 * (digamma (1 + s / 2) - digamma 1).re + 1 / 2 * (digamma 1).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, neg_re, neg_im]
    norm_num
    ring
  rw [hgoal]
  have hpi2 : Real.pi ^ 2 < 3.1416 ^ 2 := by
    have := Real.pi_lt_d4
    nlinarith [Real.pi_pos]
  have hds := dSum_le
  have hlog := log_pi_gt
  have hgam := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  nlinarith

/-! ### The theorem -/

/-- **Speiser's theorem below height `5/2`, under RH** (the real segment included). -/
theorem speiserBelow_of_RH (hRH : RiemannHypothesis) : SpeiserBelow (5 / 2) := by
  intro s h0 h1 ht hd
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hζ : riemannZeta s ≠ 0 := by
    intro h
    have := hRH s h (by
      rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at h0
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith) hs1
    linarith
  have hξ : xiZeta s ≠ 0 := by
    rw [xiZeta_eq hs0 hs1]
    refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) ?_
    intro hΛ
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have hS := hasSum_re_logDeriv_xiZeta hRH hξ
  have hS1 := hasSum_re_logDeriv_xiZeta hRH (z := 1) (by rw [xiZeta_one]; exact one_ne_zero)
  rw [xiZeta_one, div_one] at hS1
  have hle := hasSum_le (fun ρ => by
      have hρ := re_eq_half_of_xiZeta_eq_zero hRH ρ.2
      have h := re_one_div_sub_ge hρ (im_sq_ge_of_RH hRH ρ) h0.le h1.le ht.le
      have hm : (0 : ℝ) ≤ analyticOrderNatAt xiZeta (ρ : ℂ) := Nat.cast_nonneg _
      show -(65 / 9) * ((analyticOrderNatAt xiZeta (ρ : ℂ) : ℝ) * ((1 : ℂ) / (1 - ρ)).re) ≤
        (analyticOrderNatAt xiZeta (ρ : ℂ) : ℝ) * ((1 : ℂ) / (s - ρ)).re
      nlinarith [mul_le_mul_of_nonneg_left h hm])
    (hS1.mul_left (-(65 / 9))) hS
  rw [logDeriv_xiZeta_of_deriv_eq_zero h0 hs1 hζ hd] at hle
  have := re_archimedean_lt h0 h1.le ht.le
  have := re_deriv_xiZeta_one_lt
  linarith

end Speiser
