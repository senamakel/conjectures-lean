import LLS.Sharp.Final
import LLS.ClassNumberAll
import LLS.Statement2

/-!
# LLS Corollary 1.3 with the paper's constants, under GRH and the class number formula

For every imaginary quadratic field `K` of discriminant `−q`, `q ≥ 10¹⁰`, the class number
formula gives a primitive `χ` mod `q` with `‖L(1, χ)‖ = π h(K)/√q`
(`LLS.exists_primitive_norm_L1_eq`), and `l1UpperBound_of_GRH`, `l1LowerBound_of_GRH` finish.
-/

namespace LLS.Sharp

open Erdos985 Real NumberField Module

/-- **LLS Corollary 1.3, upper bound**:
`h(−q) ≤ (2e^γ/π) √q (log log q − log 2 + 1/2 + 1/log log q)` for every imaginary quadratic
field of discriminant `−q`, `q ≥ 10¹⁰`, under GRH and the class number formula. -/
theorem classNumberUpperBound_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : LLS.ClassNumberFormula) :
    LLS.ClassNumberUpperBound := by
  intro K _ _ h2 q hD hq10
  have hq4 := LLS.four_lt_of_ge hq10
  have : NeZero q := ⟨by omega⟩
  obtain ⟨χ, hprim, hnorm⟩ := LLS.exists_primitive_norm_L1_eq hCNF K h2 hD hq4
  have hU := l1UpperBound_of_GRH hGRH q hq10 χ hprim
  rw [hnorm] at hU
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < q by omega))
  rw [div_le_iff₀ hs] at hU
  set W := log (log q) - log 2 + 1 / 2 + 1 / log (log q)
  rw [show 2 * exp eulerMascheroniConstant / π * √q * W
      = 2 * exp eulerMascheroniConstant * W * √q / π by ring,
    le_div_iff₀ Real.pi_pos]
  linarith

/-- **LLS Corollary 1.3, lower bound**:
`h(−q) ≥ (π/(12e^γ)) √q (log log q − log 2 + 1/2 + 1/log log q + 14 log log q/log q)⁻¹` for
every imaginary quadratic field of discriminant `−q`, `q ≥ 10¹⁰`, under GRH and the class
number formula. -/
theorem classNumberLowerBound_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : LLS.ClassNumberFormula) :
    LLS.ClassNumberLowerBound := by
  intro K _ _ h2 q hD hq10
  have hq4 := LLS.four_lt_of_ge hq10
  have : NeZero q := ⟨by omega⟩
  obtain ⟨χ, hprim, hnorm⟩ := LLS.exists_primitive_norm_L1_eq hCNF K h2 hD hq4
  have hL := l1LowerBound_of_GRH hGRH q hq10 χ hprim
  rw [hnorm] at hL
  set W := log (log q) - log 2 + 1 / 2 + 1 / log (log q) + 14 * log (log q) / log q
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < q by omega))
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have ht : 0 < π * classNumber K / √q := by positivity
  have he : 0 < exp eulerMascheroniConstant := Real.exp_pos _
  have hpi := Real.pi_pos
  have hB : 0 < 12 * exp eulerMascheroniConstant / π ^ 2 * W :=
    lt_of_lt_of_le (by positivity) hL
  have hW : 0 < W := by
    by_contra hW
    push Not at hW
    have : 12 * exp eulerMascheroniConstant / π ^ 2 * W ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hW
    linarith
  rw [div_le_iff₀ ht] at hL
  have e : 12 * exp eulerMascheroniConstant / π ^ 2 * W * (π * classNumber K / √q)
      = 12 * exp eulerMascheroniConstant * W * classNumber K / (π * √q) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)] at hL
  rw [← div_eq_mul_inv, div_le_iff₀ hW,
    show π / (12 * exp eulerMascheroniConstant) * √q = π * √q / (12 * exp eulerMascheroniConstant)
      by ring, div_le_iff₀ (by positivity)]
  linarith

end LLS.Sharp
