import Erdos985.Analytic.ExplicitFormula.Basic
import Erdos985.Analytic.ExplicitFormula.Bounds.DigammaSeries
import Erdos985.Analytic.ExplicitFormula.Bounds.GammaSum

/-!
# `‖gammaPart χ x‖ ≤ log x + 1`

`G(s) − G(2) = Σ_k (1/(2+m_k) − 1/(s+m_k))` with `m_k = 2k + a` (digamma series). Integrating
term by term against `x^s/(s(s+1))` on `Re s = 2` and evaluating each term by the Perron residue
formulas gives `gammaPart χ x = Σ_k tau x m_k`, which is bounded in `GammaSum`.
-/

open Complex MeasureTheory Filter Topology

namespace Erdos985.Analytic.BoundsAux

lemma parity_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) : parity χ ≤ 1 := by
  unfold parity; split_ifs <;> norm_num

lemma hasSum_gammaLogDeriv {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + parity χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + parity χ : ℕ) : ℂ)))
      (gammaLogDeriv χ s - gammaLogDeriv χ 2) := by
  have ha0 : (0 : ℝ) ≤ (parity χ : ℝ) := Nat.cast_nonneg _
  have hw : 1 / 2 < ((s + (parity χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have hw2 : 1 / 2 < ((2 + (parity χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have h := ((hasSum_digamma hw).sub (hasSum_digamma hw2)).mul_left (1 / 2)
  unfold gammaLogDeriv
  convert h using 1
  · funext k
    have hh (u z : ℂ) : 1 / 2 * (1 / (u + z / 2)) = 1 / (2 * u + z) := by
      rw [one_div_mul_one_div]; congr 1; ring
    rw [show (1 / 2 : ℂ) * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (s + (parity χ : ℂ)) / 2)
        - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (2 + (parity χ : ℂ)) / 2)))
        = 1 / 2 * (1 / ((k : ℂ) + (2 + (parity χ : ℂ)) / 2))
          - 1 / 2 * (1 / ((k : ℂ) + (s + (parity χ : ℂ)) / 2)) by ring, hh, hh]
    push_cast
    congr 1 <;> congr 1 <;> ring
  · ring

/-- The `m`-th term of the gamma-part integrand. -/
noncomputable def gTerm (x : ℕ) (m : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

lemma gTerm_eq (x m : ℕ) (t : ℝ) : gTerm x m t =
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
  unfold gTerm
  rw [sub_neg_eq_add]
  field_simp

lemma hw_m (m : ℕ) : (-(m : ℂ)).re < 2 := by
  simp only [neg_re, natCast_re]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

lemma integrable_gTerm (x : ℕ) (hx : 1 ≤ x) (m : ℕ) : Integrable (gTerm x m) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hK := PerronAux.integrable_cesaro_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.integrable_perron_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP
  rw [show gTerm x m = _ from funext (gTerm_eq x m)]
  exact (hK.const_mul _).sub hP

lemma integral_gTerm (x : ℕ) (hx : 1 ≤ x) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, gTerm x m t = (tau x m : ℂ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hK := PerronAux.integrable_cesaro_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.integrable_perron_kernel (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  have hC := perron_cesaro (x : ℝ) 2 hx0 two_pos
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP hC
  rw [show gTerm x m = _ from funext (gTerm_eq x m), integral_sub (hK.const_mul _) hP,
    integral_const_mul, mul_sub, mul_left_comm, hC,
    max_eq_right (show (0 : ℝ) ≤ 1 - 1 / (x : ℝ) by
      rw [sub_nonneg, div_le_one hx0]; exact hx1)]
  rcases m with _ | _ | m
  · have hR := perron_residue_zero (x : ℝ) 2 hx1 two_pos (-((0 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hR := perron_residue_neg_one (x : ℝ) 2 hx1 two_pos (-((0 + 1 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte, zero_add, one_ne_zero]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hM : (2 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hw0 : -((m + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hw1 : -((m + 1 + 1 : ℕ) : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR := perron_residue (x : ℝ) 2 hx1 two_pos _ (hw_m (m + 1 + 1)) hw0 hw1
    simp only [ofReal_natCast, ofReal_ofNat] at hR
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

lemma norm_gTerm_le (x m : ℕ) (t : ℝ) :
    ‖gTerm x m t‖ ≤ 1 / (2 + m) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
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
  have e : gTerm x m t = (((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)) * (1 / (2 + (m : ℂ))) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))) := by
    unfold gTerm
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

lemma rpow_bound (k m : ℕ) (hkm : k ≤ m) :
    (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have e : ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) = ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1) := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + (-1) by norm_num, Real.rpow_add hk, Real.rpow_neg_one]
    ring
  rw [e]
  apply div_le_div₀ (by positivity) _ hk (by linarith)
  exact Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)

lemma summable_rpow32 : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
  simpa using this

end Erdos985.Analytic.BoundsAux

namespace Erdos985.Analytic

open BoundsAux

theorem norm_gammaPart_le' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖gammaPart χ x‖ ≤ Real.log x + 1 := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, gTerm x (2 * k + parity χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact (((hasSum_gammaLogDeriv χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖gTerm x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖gTerm x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (integrable_gTerm x hx m).norm (hQi.norm.const_mul _)
            (fun t => norm_gTerm_le x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖gTerm x (2 * k + parity χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : gammaPart χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, gTerm x (2 * k + parity χ) t := by
    unfold gammaPart
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTerm x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTerm x hx]
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  exact (tsum_tau_bound x hx1 (parity χ) (parity_le_one χ)).2

end Erdos985.Analytic
