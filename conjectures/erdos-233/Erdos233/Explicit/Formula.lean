import Erdos985
import Erdos985.Analytic.Principal.Identity
import Erdos985.Analytic.Principal.Bounds

/-!
# The weighted explicit formula for `ζ` at real `x ≥ 1`

erdos-985 proves `explicit_formula_zeta` for natural `x`. The proof only uses `x ∈ ℕ` in the
weighted Perron formula, whose finite side is `Σ_{0 < n < N}`. Here the same argument is run with
real `x`: the finite side becomes `Σ_{1 ≤ n ≤ ⌊x⌋}`. We also record that the zero sum is
absolutely summable and that the gamma part is real with `gammaPartR x + log x ∈ [1 − 3/(2x), 1]`.
-/

open Complex ArithmeticFunction MeasureTheory Filter

namespace Erdos233.ExplicitAux

open Erdos985.Analytic Erdos985.Analytic.IdentityAux Erdos985.Analytic.BoundsAux

/-- The contribution of one zero `ρ` at real `x`. -/
noncomputable def zeroTermR (x : ℝ) (ρ : ℂ) : ℂ :=
  (1 - 1 / (x : ℂ)) / (2 - ρ)
    - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))

/-- The gamma-factor contribution at real `x` (character mod `1`). -/
noncomputable def gammaPartR (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (gammaLogDeriv (1 : DirichletCharacter ℂ 1) (2 + t * I)
        - gammaLogDeriv (1 : DirichletCharacter ℂ 1) 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

/-! ### Weighted Perron at real `x` -/

lemma term_mul_eqR (a : ℕ → ℂ) (c t : ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ) :
    LSeries.term a ((c : ℂ) + t * I) n * ((x : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = if n = 0 then 0 else a n * PerronKernel.K c (x / n) t := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · unfold PerronKernel.K
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hnc : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
      rw [cpow_ne_zero_iff]; left; exact_mod_cast hn
    rw [ofReal_div, div_eq_mul_inv (x : ℂ), ← ofReal_inv, mul_cpow_ofReal_nonneg
      hx.le (by positivity), ofReal_inv, inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast]
    field_simp

theorem perron_weightedR (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (x : ℝ) (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (1 - (n : ℂ) / x)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I)
          / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  set C := ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < x / n := fun n hn =>
    div_pos hx (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  let G : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * PerronKernel.K c (x / n) t
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]
      exact (PerronKernel.integrable_K c _ hc (hpos n hn)).const_mul _
  have hG_norm : ∀ n, ∫ t, ‖G n t‖ = if n = 0 then 0 else ‖a n‖ * ((x / n) ^ c * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul, PerronKernel.integral_norm_K c _ (hpos n hn)]
  have hsum : Summable fun n => ∫ t, ‖G n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (ha.mul_left (x ^ c * C))
    rw [hG_norm]
    split_ifs with hn
    · have : 0 ≤ ‖a n‖ / (n : ℝ) ^ c := div_nonneg (norm_nonneg _) (by positivity)
      positivity
    · rw [Real.div_rpow hx.le (Nat.cast_nonneg n)]
      apply le_of_eq
      ring
  have hfun : (fun t : ℝ => LSeries a ((c : ℂ) + t * I) * (x : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) = fun t => ∑' n, G n t := by
    funext t
    rw [mul_div_assoc, LSeries, ← tsum_mul_right]
    congr 1
    funext n
    exact term_mul_eqR a c t x hx n
  have hGint : ∀ n, ∫ t, G n t = if n = 0 then 0 else
      a n * (2 * Real.pi * ((if 1 ≤ x / n then 1 - 1 / (x / n) else 0 : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      unfold PerronKernel.K
      rw [PerronKernel.perron_kernel _ c (hpos n hn) hc]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn.2
    have hle : 1 ≤ x / n := by
      rw [one_le_div (Nat.cast_pos.2 (by omega))]; exact hnx
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
    push_cast
    field_simp
  · intro n hn
    rw [Finset.mem_Icc] at hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      have hnN : ⌊x⌋₊ < n := by omega
      have hxn : x < n := (Nat.floor_lt hx.le).1 hnN
      have hlt : ¬ 1 ≤ x / n := by
        rw [not_le, div_lt_one (Nat.cast_pos.2 (by omega))]; exact hxn
      simp [hlt]

/-! ### One zero term at real `x` -/

lemma integral_pairTermR (x : ℝ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ -1) :
    ∫ t, pairTerm x ρ t = -(2 * Real.pi) * zeroTermR x ρ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h := perron_residue x 2 hx two_pos ρ (by simpa using hρ) hρ0 hρ1
  simp only [ofReal_ofNat] at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hR : ∫ t, resKern x ρ t = 2 * Real.pi * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ
      + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ)) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [resKern]
  have hK := integral_kern hx
  simp_rw [pairTerm_eq]
  rw [integral_sub (integrable_resKern hx0 hρ) ((integrable_kern hx0).const_mul _),
    integral_const_mul, hR, hK]
  unfold zeroTermR
  ring

/-! ### The gamma part at real `x` -/

/-- The `m`-th term of the gamma-part integrand at real `x`. -/
noncomputable def gTermR (x : ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

lemma gTermR_eq (x : ℝ) (m : ℕ) (t : ℝ) : gTermR x m t =
    1 / (2 + (m : ℂ)) * ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
    - (x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold gTermR
  rw [sub_neg_eq_add]
  field_simp

lemma integrable_gTermR (x : ℝ) (hx : 1 ≤ x) (m : ℕ) : Integrable (gTermR x m) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hK := PerronAux.integrable_cesaro_kernel (x := x) (c := 2) hx0 two_pos
  have hP := PerronAux.integrable_perron_kernel (x := x) (c := 2) hx0 two_pos (hw_m m)
  simp only [ofReal_ofNat] at hK hP
  rw [show gTermR x m = _ from funext (gTermR_eq x m)]
  exact (hK.const_mul _).sub hP

lemma integral_gTermR (x : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, gTermR x m t = (tau x m : ℂ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0.ne'
  have hK := PerronAux.integrable_cesaro_kernel (x := x) (c := 2) hx0 two_pos
  have hP := PerronAux.integrable_perron_kernel (x := x) (c := 2) hx0 two_pos (hw_m m)
  have hC := perron_cesaro x 2 hx0 two_pos
  simp only [ofReal_ofNat] at hK hP hC
  rw [show gTermR x m = _ from funext (gTermR_eq x m), integral_sub (hK.const_mul _) hP,
    integral_const_mul, mul_sub, mul_left_comm, hC,
    max_eq_right (show (0 : ℝ) ≤ 1 - 1 / x by
      rw [sub_nonneg, div_le_one hx0]; exact hx)]
  rcases m with _ | _ | m
  · have hR := perron_residue_zero x 2 hx two_pos (-((0 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hR := perron_residue_neg_one x 2 hx two_pos (-((0 + 1 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte, zero_add, one_ne_zero]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hw0 : -((m + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hw1 : -((m + 1 + 1 : ℕ) : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR := perron_residue x 2 hx two_pos _ (hw_m (m + 1 + 1)) hw0 hw1
    simp only [ofReal_ofNat] at hR
    rw [hR]
    have h0 : m + 1 + 1 ≠ 0 := by omega
    have h1 : m + 1 + 1 ≠ 1 := by omega
    simp only [tau, h0, h1, ↓reduceIte]
    rw [cpow_neg, cpow_natCast, cpow_neg_one]
    push_cast
    have e1 : (m : ℂ) + 1 + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e2 : (m : ℂ) + 1 + 1 - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e3 : (2 : ℂ) + ((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e4 : -((m : ℂ) + 1 + 1) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e5 : 1 + -((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e6 : (x : ℂ) ^ (m + 1 + 1) ≠ 0 := pow_ne_zero _ hxC
    simp only [one_div, inv_pow]
    field_simp
    ring

lemma norm_gTermR_le (x : ℝ) (m : ℕ) (t : ℝ) :
    ‖gTermR x m t‖ ≤ 1 / (2 + m) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : gTermR x m t = (((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)) * (1 / (2 + (m : ℂ))) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))) := by
    unfold gTermR
    rw [sub_neg_eq_add]
    field_simp
    ring
  rw [e, norm_mul, norm_mul]
  have hq : ‖((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr h0)]
    have : (2 : ℂ) + t * I - 2 = t * I := by ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.abs_im_le_norm ((2 : ℂ) + t * I)
    simpa using this
  have hn : ‖1 / (2 + (m : ℂ))‖ = 1 / (2 + m) := by
    rw [norm_div, norm_one]
    congr 1
    exact_mod_cast Complex.norm_natCast (2 + m)
  rw [hn]
  have := norm_nonneg ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1)))
  have : 0 ≤ 1 / (2 + (m : ℝ)) := by positivity
  calc _ ≤ 1 * (1 / (2 + (m : ℝ))) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by gcongr
    _ = _ := by ring

theorem gammaPartR_eq_tsum_tau (x : ℝ) (hx : 1 ≤ x) :
    gammaPartR x = ((∑' k : ℕ, tau x (2 * k) : ℝ) : ℂ) := by
  set χ : DirichletCharacter ℂ 1 := 1
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by linarith
  have hpar : parity χ = 0 := PrincipalAux.parity_one
  have hsum : ∀ t : ℝ, (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, gTermR x (2 * k + parity χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact (((hasSum_gammaLogDeriv χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖gTermR x m t‖ ≤
      C * x ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖gTermR x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (integrable_gTermR x hx m).norm (hQi.norm.const_mul _)
            (fun t => norm_gTermR_le x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * x ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖gTermR x (2 * k + parity χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * x ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : gammaPartR x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, gTermR x (2 * k + parity χ) t := by
    unfold gammaPartR
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTermR x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTermR x hx]
  rw [← Complex.ofReal_tsum, hpar]
  simp

theorem gammaPartR_bound (x : ℝ) (hx : 1 ≤ x) :
    (gammaPartR x).im = 0 ∧
    1 - 3 / (2 * x) ≤ (gammaPartR x).re + Real.log x ∧
    (gammaPartR x).re + Real.log x ≤ 1 := by
  rw [gammaPartR_eq_tsum_tau x hx]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact (PrincipalAux.tsum_tau_even_bound x hx).2

/-! ### The explicit formula at real `x` -/

/-- The weighted explicit formula for `ζ` at real `x ≥ 1`, with absolute summability of the
zero sum. -/
theorem explicit_formula_real (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
        (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTermR x ρ) ∧
    (((∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTermR x ρ)
        + gammaPartR x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv riemannZeta 2 / riemannZeta 2) := by
  classical
  set G := gammaLogDeriv (1 : DirichletCharacter ℂ 1) with hG
  set D : ℂ → ℂ := fun z => deriv xiZeta z / xiZeta z with hD
  set m : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt xiZeta ρ : ℂ) with hm
  set c2 : ℂ := deriv riemannZeta 2 / riemannZeta 2 with hc2
  have := PrincipalAux.countable_xiZeta_zeros
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ xiZeta := differentiable_xiZeta
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → xiZeta z ≠ 0 := fun z hz h => by
    linarith [(xiZeta_zero_re_mem h).2]
  /- Hadamard -/
  obtain ⟨hsum_ε, b, hb⟩ := hadamard_logDeriv hΛd (by rw [xiZeta_zero]; exact one_ne_zero)
    xiZeta_growth
  have hzre : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => xiZeta_zero_re_mem ρ.2
  /- The family of zero terms. -/
  let F : {ρ : ℂ // xiZeta ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * pairTerm x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (integrable_pairTerm hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := integral_norm_pairTerm_le
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * x ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt xiZeta ρ : ℝ) * ∫ t, ‖pairTerm x ρ t‖
        ≤ (analyticOrderNatAt xiZeta ρ : ℝ) *
            (C * x ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_eval : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      ∫ t, F ρ t = m ρ * (-(2 * Real.pi) * zeroTermR x ρ) := by
    intro ρ
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, integral_pairTermR x hx (by linarith [hzre ρ]) hρ0 hρ1]
  have hZ_sum : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => m ρ * zeroTermR x ρ := by
    refine Summable.of_norm_bounded (hF_sum.mul_left (1 / (2 * Real.pi))) fun ρ => ?_
    have h1 := norm_integral_le_integral_norm (μ := volume) (F ρ)
    rw [hF_eval ρ, show m ρ * (-(2 * Real.pi) * zeroTermR x ρ)
      = -(2 * (Real.pi : ℂ)) * (m ρ * zeroTermR x ρ) by ring, norm_mul, norm_neg, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at h1
    have hp : 0 < 2 * Real.pi := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hp]
    linarith
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I) - D 2) * kern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (kern x t)
    convert this using 1
    · funext ρ
      simp only [F, m, pairTerm]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv xiZeta) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t :=
    integrable_of_hasSum
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (integrable_kern hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t
      = ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTermR x ρ) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    exact tsum_congr hF_eval
  /- Perron. -/
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := perron_weightedR a 2 two_pos ha_sum x hx0
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - 1 / z - 1 / (z - 1) - G z) := fun z hz => by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
    change LSeries a z = _ at h1
    rw [h1, neg_div, PrincipalAux.logDeriv_riemannZeta_eq hz]
  have hc2' : c2 = D 2 - 1 / 2 - 1 / (2 - 1) - G 2 :=
    PrincipalAux.logDeriv_riemannZeta_eq (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * kern x t := fun t => by
    simp only [hH, kern]
    ring
  have hH_int : Integrable H := by
    have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) := by
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num))) ?_
      have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
      rw [this]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) :=
      (LSeries_differentiableOn a).continuousOn.comp_continuous hs_cont
        (fun t => by simp only [Set.mem_ofPred_eq, hsre]; exact_mod_cast hab)
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * kern x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((integrable_kern hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (integrable_kern hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  /- The poles at `0` and `1`. -/
  set P0 : ℝ → ℂ := fun t => (x : ℂ) ^ ((2 : ℂ) + t * I) /
    (((2 : ℂ) + t * I - 0) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hP0
  have hP0_int : Integrable P0 := by
    have := perron_residue_integrable x 2 hx0 two_pos 0 (by simp)
    simp only [ofReal_ofNat] at this
    exact this
  have hP0_integral : ∫ t, P0 t = 2 * Real.pi * ((Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ)) := by
    have h := perron_residue_zero x 2 hx1 two_pos 0 rfl
    simp only [ofReal_ofNat] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have hR1_int : Integrable (resKern x 1) := integrable_resKern hx0 (by norm_num)
  have hR1_integral : ∫ t, resKern x 1 t
      = 2 * Real.pi * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)) - 1 / 1 + (x : ℂ) ^ (-1 : ℂ) / (1 + 1)) := by
    have h := perron_residue x 2 hx1 two_pos 1 (by norm_num) one_ne_zero (by norm_num)
    simp only [ofReal_ofNat] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [resKern]
  /- Decomposition of the gamma part. -/
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * kern x t - P0 t - resKern x 1 t
          + (c2 + 3 / 2) * kern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    have h0 := line_ne_zero' t
    have h1 := line_add_one_ne_zero' t
    have h2 := line_sub_ne_zero' (ρ := 1) (by norm_num) t
    rw [hH_eq, hLS _ hz, hc2']
    simp only [kern, resKern, hP0, sub_zero]
    field_simp
    ring
  have hgamma : gammaPartR x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        - (∫ t, P0 t) - (∫ t, resKern x 1 t) + (c2 + 3 / 2) * ∫ t, kern x t) := by
    unfold gammaPartR
    rw [← hG, hF2, integral_add _ ((integrable_kern hx0).const_mul _),
      integral_sub _ hR1_int, integral_sub _ hP0_int, integral_add hH_int hF1_int,
      integral_const_mul]
    · exact hH_int.add hF1_int
    · exact (hH_int.add hF1_int).sub hP0_int
    · exact ((hH_int.add hF1_int).sub hP0_int).sub hR1_int
  /- Assemble. -/
  have hbach : (((∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (1 - (n : ℂ) / x) := by
    push_cast
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Icc] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : (((∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := integral_kern hx1
  have htsum : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (-(2 * Real.pi) * zeroTermR x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * zeroTermR x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  refine ⟨hZ_sum, ?_⟩
  rw [hgamma, hbach', hF1_integral, htsum, hK, hP0_integral, hR1_integral]
  simp only [cpow_one, cpow_neg_one]
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0.ne'
  field_simp
  ring

end Erdos233.ExplicitAux
