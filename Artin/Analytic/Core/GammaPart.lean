import Erdos985.Analytic.ExplicitFormula.Bounds
import Erdos985.Analytic.Principal.Bounds

/-!
# Gamma factors: logarithmic derivatives and their part of the explicit formula

`Γ_ℝ(s) = π^{-s/2} Γ(s/2)` and `Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)` (Mathlib's
`Gammaℝ_mul_Gammaℝ_add_one`). Write `gR a s = -½ log π + ½ ψ((s + a)/2)` for `a ∈ {0, 1}`: then
`Γ_ℝ'/Γ_ℝ(s) = gR 0 s` and `Γ_ℂ'/Γ_ℂ(s) = gR 0 s + gR 1 s`. This is erdos-985's
`gammaLogDeriv χ`, which depends on the Dirichlet character `χ` only through its parity `a`; here
the parity is a plain parameter, so both parities are available without choosing an odd
character.

`gammaPartP a x` is the contribution of `gR a` to the weighted explicit formula, and
`gammaPartP_eq_tsum_tau` evaluates it as `∑_k tau x (2k + a)` (erdos-985's `tau`, the residues at
the poles `-2k - a`). The proofs of `hasSum_gR` and `gammaPartP_eq_tsum_tau` are those of
erdos-985's `BoundsAux.hasSum_gammaLogDeriv` and `PrincipalAux.gammaPart_eq_tsum_tau` with
`parity χ` replaced by `a`.
-/

namespace Artin.Analytic

open Complex MeasureTheory Erdos985.Analytic Erdos985.Analytic.BoundsAux

/-- `gR a s = -½ log π + ½ ψ((s + a)/2)`; `gR 0 = Γ_ℝ'/Γ_ℝ`, and `gR 0 + gR 1 = Γ_ℂ'/Γ_ℂ`. -/
noncomputable def gR (a : ℕ) (s : ℂ) : ℂ :=
  -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + a) / 2)

lemma gR_eq_gammaLogDeriv {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gR (parity χ) s = gammaLogDeriv χ s := rfl

lemma hasSum_gR {a : ℕ} {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + a : ℕ) : ℂ)) - 1 / (s + ((2 * k + a : ℕ) : ℂ)))
      (gR a s - gR a 2) := by
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hw : 1 / 2 < ((s + (a : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have hw2 : 1 / 2 < ((2 + (a : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have h := ((hasSum_digamma hw).sub (hasSum_digamma hw2)).mul_left (1 / 2)
  unfold gR
  convert h using 1
  · funext k
    have hh (u z : ℂ) : 1 / 2 * (1 / (u + z / 2)) = 1 / (2 * u + z) := by
      rw [one_div_mul_one_div]; congr 1; ring
    rw [show (1 / 2 : ℂ) * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (s + (a : ℂ)) / 2)
        - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (2 + (a : ℂ)) / 2)))
        = 1 / 2 * (1 / ((k : ℂ) + (2 + (a : ℂ)) / 2))
          - 1 / 2 * (1 / ((k : ℂ) + (s + (a : ℂ)) / 2)) by ring, hh, hh]
    push_cast
    congr 1 <;> congr 1 <;> ring
  · ring

/-- The contribution of `gR a` to the weighted explicit formula on the line `Re s = 2`. -/
noncomputable def gammaPartP (a x : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (gR a (2 + t * I) - gR a 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

lemma gammaPartP_eq_gammaPart {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℕ) :
    gammaPartP (parity χ) x = gammaPart χ x := rfl

/-- `gammaPartP a x = ∑_k tau x (2k + a)`. -/
theorem gammaPartP_eq_tsum_tau (a x : ℕ) (hx : 1 ≤ x) :
    gammaPartP a x = ((∑' k : ℕ, tau x (2 * k + a) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (gR a (2 + t * I) - gR a 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, gTerm x (2 * k + a) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact (((hasSum_gR (a := a) hs).mul_right _).div_const _).tsum_eq.symm
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
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖gTerm x (2 * k + a) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : gammaPartP a x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, gTerm x (2 * k + a) t := by
    unfold gammaPartP
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTerm x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTerm x hx]
  rw [← Complex.ofReal_tsum]

/-- `|gammaPartP a x| ≤ log x + 1` for `a ≤ 1`. -/
theorem norm_gammaPartP_le {a : ℕ} (ha : a ≤ 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖gammaPartP a x‖ ≤ Real.log x + 1 := by
  rw [gammaPartP_eq_tsum_tau a x hx, Complex.norm_real, Real.norm_eq_abs]
  exact (tsum_tau_bound x (by exact_mod_cast hx) a ha).2

end Artin.Analytic
