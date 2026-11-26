import LLS.Sharp.Defs

/-!
# Numerical part of LLS Theorem 1.5: the one-variable functions

With `l = log x`, `u = 1/l` and `y = 1/√x`, the bounds of `LLS.Sharp.Assembly`, after the prime
sums are estimated (`LLS.Sharp.Principal`, `LLS.Sharp.Lemma51`), become

* upper: `log ‖L(1,χ)‖ ≤ log l + γ + FUu 𝔞 u y`,
* lower: `−log ‖L(1,χ)‖ ≤ log l + γ − log ζ(2) + HLu 𝔞 u y + E`,

where `E` is the error of the prime-by-prime estimate. Both functions are `u + 2u² + y·Q` for an
explicit `Q` (`FUu_eq`, `HLu_eq`). The targets are `log(1 + V(u))` and `log(1 + V(u) + Zz)`,
`V(u) = u + 4u²/(1 + 2u log 2)`, and `log(1 + w) ≥ 2w/(2 + w)` turns everything into rational
inequalities.
-/

namespace LLS.Sharp

open Real

/-! ### Constants -/

lemma log_pi_lt : Real.log π < 1.1448 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h1 : Real.exp 1.1448 = Real.exp 1 * Real.exp 0.1448 := by
    rw [← Real.exp_add]; norm_num
  have h2 : (1 : ℝ) + 0.1448 + 0.1448 ^ 2 / 2 + 0.1448 ^ 3 / 6 ≤ Real.exp 0.1448 := by
    have := Real.sum_le_exp_of_nonneg (x := 0.1448) (by norm_num) 4
    simpa [Finset.sum_range_succ, Nat.factorial] using this
  have h3 := Real.exp_one_gt_d9
  have h4 := Real.pi_lt_d4
  rw [h1]
  nlinarith

/-- The numerical constants, with the precision used below. -/
lemma consts :
    0.57688 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 0.5774 ∧
      1.144 < Real.log π ∧ Real.log π < 1.1448 ∧
      0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt,
    Erdos985.Analytic.PrincipalAux.eulerMascheroniConstant_lt',
    Erdos985.Analytic.PrincipalAux.log_pi_gt', log_pi_lt, Real.log_two_gt_d9,
    Real.log_two_lt_d9⟩

/-! ### The functions -/

/-- `V(u) = u + 4u²/(1 + 2u log 2)`: `log(1 + V(1/l)) = log(l + 1 + 4/(l + 2 log 2)) − log l`. -/
noncomputable def Vf (u : ℝ) : ℝ := u + 4 * u ^ 2 / (1 + 2 * Real.log 2 * u)

/-- `u · ELpar 𝔞 x` with `u = 1/log x`, `y² = 1/x`. -/
noncomputable def ELu (a : ℕ) (u y : ℝ) : ℝ :=
  if a = 0 then ((1 - y ^ 2) / 3 - 1 + y ^ 2 - 1 / 3 + (1 - y ^ 2) * G3par 0) * u + y ^ 2
  else (-(1 / 2) + (1 - y ^ 2) * G3par 1) * u

/-- `u · EUpar 𝔞 x` with `u = 1/log x`, `y² = 1/x`. -/
noncomputable def EUu (a : ℕ) (u y : ℝ) : ℝ :=
  if a = 0 then
    ((1 - y ^ 2) / 3 - 1 + y ^ 2 - 1 / 3 + 3 / 2 * y ^ 2 + (1 - y ^ 2) * G3par 0) * u + y ^ 2
  else ((3 * y ^ 2 - 1) / 2 + (1 - y ^ 2) * G3par 1) * u

/-- The upper-bound function: `log ‖L(1,χ)‖ − log l − γ ≤ FUu 𝔞 u y`. -/
noncomputable def FUu (a : ℕ) (u y : ℝ) : ℝ :=
  -1 + (eulerMascheroniConstant + Gpar a) * u + (0.6 * y + 29 * y ^ 2) * u
    + 2 * u * (1 + y ^ 2 / 2) * (1 + (1 - y) * u) / (1 + y)
    + (1 - 2 * y * u)
        * (1 - ((1 + eulerMascheroniConstant - 0.25 * y - 12 * y ^ 2) * u + ELu a u y))
        / (1 + y) ^ 2
    + 2 * y ^ 2 * u ^ 2

/-- The lower-bound function: `−log ‖L(1,χ)‖ − log l − γ + log ζ(2) ≤ HLu 𝔞 u y + E`. -/
noncomputable def HLu (a : ℕ) (u y : ℝ) : ℝ :=
  -1 + eulerMascheroniConstant * u + (0.6 * y + 29 * y ^ 2) * u
    + (1 + 2 * y * u)
        * (1 - (1 + eulerMascheroniConstant - 0.25 * y - 12 * y ^ 2) * u + EUu a u y)
        / (1 - y) ^ 2
    - Gpar a * u + 2 * u * (1 + y ^ 2 / 2) * (1 + u * (1 + y)) / (1 - y) + 2 * y ^ 2 * u ^ 2

/-- `k = 1 + γ + Re G(1)`. -/
noncomputable def kU (a : ℕ) : ℝ := 1 + eulerMascheroniConstant + Gpar a

noncomputable def eU (a : ℕ) (u y : ℝ) : ℝ :=
  if a = 0 then -(0.25 + y * (34 / 3 + G3par 0)) * u + y
  else -(0.25 + y * (12 + G3par 1)) * u

/-- `(FUu − u − 2u²)/y`. -/
noncomputable def QU (a : ℕ) (u y : ℝ) : ℝ :=
  (-(1 - kU a * u) * (2 + y) - eU a u y - 2 * u * (1 - kU a * u - y * eU a u y)) / (1 + y) ^ 2
    + 2 * u * (y / 2 * (1 + u) - 1 - 2 * u - y ^ 2 * u / 2) / (1 + y)
    + (0.6 + 29 * y) * u + 2 * y * u ^ 2

/-- `k' = 1 + γ − Re G(1)`. -/
noncomputable def kL (a : ℕ) : ℝ := 1 + eulerMascheroniConstant - Gpar a

noncomputable def cL (a : ℕ) : ℝ := if a = 0 then 13 / 6 - G3par 0 else 3 / 2 - G3par 1

/-- `(HLu − u − 2u²)/y`. -/
noncomputable def QL (a : ℕ) (u y : ℝ) : ℝ :=
  (0.6 + 29 * y) * u + 2 * y * u ^ 2
    + ((0.25 + 12 * y) * u + y * cL a * u + (if a = 0 then y else 0)) * (1 + 2 * y * u)
        / (1 - y) ^ 2
    + (1 - kL a * u) * (2 + 2 * u - y) / (1 - y) ^ 2
    + 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) / (1 - y)

lemma FUu_eq (a : ℕ) (ha : a ≤ 1) (u y : ℝ) (hy : 0 ≤ y) :
    FUu a u y = u + 2 * u ^ 2 + y * QU a u y := by
  have h1 : (1 + y) ≠ 0 := by positivity
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · simp only [FUu, QU, ELu, eU, kU, Gpar, G3par, ↓reduceIte]
    field_simp
    ring
  · simp only [FUu, QU, ELu, eU, kU, Gpar, G3par, one_ne_zero, ↓reduceIte]
    field_simp
    ring

lemma HLu_eq (a : ℕ) (ha : a ≤ 1) (u y : ℝ) (hy : y < 1) :
    HLu a u y = u + 2 * u ^ 2 + y * QL a u y := by
  have h1 : (1 - y) ≠ 0 := by intro h; linarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · simp only [HLu, QL, EUu, cL, kL, Gpar, G3par, ↓reduceIte]
    field_simp
    ring
  · simp only [HLu, QL, EUu, cL, kL, Gpar, G3par, one_ne_zero, ↓reduceIte]
    field_simp
    ring

/-! ### Logarithm -/

/-- `log(1 + w) ≥ 2w/(2 + w)` for `w ≥ 0`. -/
lemma log_one_add_ge {w : ℝ} (hw : 0 ≤ w) : 2 * w / (2 + w) ≤ Real.log (1 + w) := by
  rcases hw.eq_or_lt with rfl | hw0
  · simp
  have h := Real.hasSum_log_one_add_inv (a := 1 / w) (by positivity)
  have hle := le_hasSum h 0 (fun k _ => by
    have : 0 < 1 / (2 * (1 / w) + 1) := by positivity
    positivity)
  have e1 : (1 : ℝ) + (1 / w)⁻¹ = 1 + w := by field_simp
  have e2 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * (1 / w) + 1)) ^ (2 * 0 + 1)
      = 2 * w / (2 + w) := by
    have h2w : (2 + w) ≠ 0 := by positivity
    have hw' : w ≠ 0 := hw0.ne'
    rw [show (1 : ℝ) / (2 * (1 / w) + 1) = w / (2 + w) by field_simp]
    push_cast
    ring
  rw [e1, e2] at hle
  exact hle

end LLS.Sharp
