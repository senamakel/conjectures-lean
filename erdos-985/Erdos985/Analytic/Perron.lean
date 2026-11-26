import Mathlib
import Erdos985.Analytic.Perron.Mellin
import Erdos985.Analytic.Perron.Bounds
import Erdos985.Analytic.Perron.Residue

/-!
# Contour integrals of the weighted Perron kernel `x^s / (s (s + 1))`

All integrals are over the vertical line `Re s = c`, written `s = c + t i`, normalized by
`1/(2π)` (so they equal `(1/2πi) ∫_{(c)}`).

The proofs go through Mathlib's Mellin inversion theorem (`mellinInv_mellin_eq`): each rational
kernel is the Mellin transform of an explicit profile supported on `(0, 1]`
(see `Erdos985.Analytic.PerronAux.prof`), so no contour shifting is needed.
-/

open Complex MeasureTheory Set

namespace Erdos985.Analytic

open PerronAux

/-- Perron's formula for the Cesàro kernel: `(1/2πi)∫_{(c)} y^s/(s(s+1)) ds = max 0 (1 - 1/y)`. -/
theorem perron_cesaro (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) :=
  PerronKernel.perron_cesaro_aux y c hy hc

/-- Residue formula for one extra simple pole `w` left of the line, `x ≥ 1`. -/
theorem perron_residue (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) :=
  PerronKernel.perron_residue_aux x c hx hc w hw hw0 hw1

/-- Double-pole case `w = 0` of `perron_residue`: the residues of `x^s/(s^2(s+1))` at `0` and
`-1` sum to `log x - 1 + 1/x`. -/
theorem perron_residue_zero (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ) := by
  subst hw
  have hx0 : 0 < x := by linarith
  have key := perron_prof (c := c) hx0 (-1) 0 (-1) 0 1 0 0 1
    (by simp) (by simpa using hc) (by simpa using hc)
    (by simpa using hc) (by simpa using (show 0 < c + 1 by linarith))
    (fun _ => by ring) (F := fun s => 1 / ((s - 0) * s * (s + 1)))
    (fun t => by
      have h0 := line_ne_zero hc t
      have h1 := line_add_one_ne_zero hc t
      simp only [add_zero, sub_zero]
      field_simp
      ring)
    (integrable_div_line_three hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
      (fun _ => by simp) (w := 0) (by simpa using hc))
  simp only [mul_one_div] at key
  rw [key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
  push_cast
  simp only [cpow_one, cpow_zero]
  ring

/-- Double-pole case `w = -1` of `perron_residue`: the residues of `x^s/(s(s+1)^2)` at `0` and
`-1` sum to `1 - 1/x - (log x)/x`. -/
theorem perron_residue_neg_one (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 1 - (x : ℂ) ^ (-1 : ℂ) - (x : ℂ) ^ (-1 : ℂ) * (Real.log x : ℂ) := by
  subst hw
  have hx0 : 0 < x := by linarith
  have key := perron_prof (c := c) hx0 1 1 1 (-1) 0 0 1 0
    (by simp) (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
    (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
    (fun _ => by ring) (F := fun s => 1 / ((s - -1) * s * (s + 1)))
    (fun t => by
      have h0 := line_ne_zero hc t
      have h1 := line_add_one_ne_zero hc t
      simp only [add_zero, sub_neg_eq_add]
      field_simp
      ring)
    (integrable_div_line_three hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
      (fun _ => by simp) (w := -1) (by simp; linarith))
  simp only [mul_one_div] at key
  rw [key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
  push_cast
  simp only [cpow_one, cpow_zero]
  ring

/-! ### Integrability and bounds for dominated convergence over poles `w` -/

/-- The kernel of `perron_residue` is integrable on the line. -/
theorem perron_residue_integrable (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  integrable_perron_kernel hx hc hw

/-- Exact pointwise norm: `|x^s/((s-w)s(s+1))| = x^c/(|s-w||s||s+1|)`. -/
theorem perron_residue_norm (x c : ℝ) (hx : 0 < x) (t : ℝ) (w : ℂ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
      = x ^ c / (‖(c : ℂ) + t * I - w‖ * ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) :=
  norm_perron_kernel hx c t w

/-- `∫ |x^s/((s-w)(s+1))| dt ≤ K x^c (1+|w|)^{-θ}` uniformly in `Re w ≤ c - δ`, any `θ < 1`.
Use with the paired Hadamard term `1/(s-ρ) + 1/ρ = s/(ρ(s-ρ))` to get summable
`O(x^c |ρ|^{-1-θ})` contributions. -/
theorem perron_pair_integral_norm_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) :=
  integral_norm_kernel_two_le hδ hθ0 hθ1

/-- `∫ |x^s/((s-w)s(s+1))| dt ≤ (K/c) x^c (1+|w|)^{-θ}` uniformly in `Re w ≤ c - δ`. -/
theorem perron_residue_integral_norm_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
        ≤ K / c * x ^ c * (1 + ‖w‖) ^ (-θ) :=
  integral_norm_perron_kernel_le hδ hθ0 hθ1

end Erdos985.Analytic
