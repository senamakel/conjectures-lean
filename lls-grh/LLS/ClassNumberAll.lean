import LLS.ClassNumber
import LLS.FundamentalDiscr
import LLS.Kronecker
import LLS.Statement3

/-!
# Class-number bounds under GRH for every imaginary quadratic field

`classNumberUpperBoundWith_of_GRH_of_formula : ClassNumberUpperBoundWith 5` and
`classNumberLowerBoundWith_of_GRH_of_formula : ClassNumberLowerBoundWith 5`: for every number
field `K` of degree `2` with `discr K = −q`, `q ≥ 10¹⁰`,
`√q/(2πe^γ(log log q + 5)) ≤ h(K) ≤ (2e^γ/π)√q(log log q + 5)`, under GRH and Dirichlet's class
number formula (`LLS.ClassNumberFormula`, tier H). No hypothesis on `q` beyond `q ≥ 10¹⁰`.

1. `discr K` is a fundamental discriminant (`discr_isFundamentalDiscr`, from Mathlib's
   quadratic algebras), so either `q ≡ 3 (mod 4)` is squarefree, or `q = 4m` with `m`
   squarefree and `m ≡ 1, 2 (mod 4)`.
2. The Kronecker symbol `χ_{−q}` is a primitive character mod `q`: `jacobiChar q` in the first
   case (`jacobiChar_kronecker`, `jacobiChar_isPrimitive`), `kroneckerChar q` in the second
   (`kroneckerChar_natCast_of_odd`, `kroneckerChar_isPrimitive`).
3. The class number formula gives `‖L(1, χ_{−q})‖ = π h/√q`, and the GRH bounds
   `l1UpperBoundWith_of_GRH`, `l1LowerBoundWith_of_GRH` for primitive characters finish.
-/

namespace LLS

open Erdos985 Real NumberField Module
open scoped NumberTheorySymbols

/-- For every imaginary quadratic field of discriminant `−q`, `q > 4`, the class number formula
supplies a primitive character `χ` mod `q` with `‖L(1, χ)‖ = π h/√q`. -/
lemma exists_primitive_norm_L1_eq (hCNF : ClassNumberFormula) (K : Type) [Field K]
    [NumberField K] (h2 : finrank ℚ K = 2) {q : ℕ} [NeZero q] (hD : discr K = -q) (hq : 4 < q) :
    ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧
      ‖DirichletCharacter.LFunction χ 1‖ = π * classNumber K / √q := by
  have hF := discr_isFundamentalDiscr K h2
  rw [hD, Int.isFundamentalDiscr_iff_squarefree] at hF
  have key : ∀ χ : DirichletCharacter ℂ q,
      (∀ n : ℕ, Odd n → χ n = ((J(-(q : ℤ) | n) : ℤ) : ℂ)) →
        ‖DirichletCharacter.LFunction χ 1‖ = π * classNumber K / √q := fun χ hχ => by
    rw [hCNF K q h2 hD hq χ hχ, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rcases hF with ⟨h4, hsq⟩ | ⟨h4, hsq, hm⟩
  · have h4' : q % 4 = 3 := by omega
    have hsq' : Squarefree q := by simpa using Int.squarefree_natAbs.2 hsq
    exact ⟨jacobiChar q, jacobiChar_isPrimitive (Nat.odd_iff.2 (by omega)) hsq',
      key _ (jacobiChar_kronecker h4')⟩
  · obtain ⟨m, rfl⟩ : 4 ∣ q := by omega
    have hdiv : -((4 * m : ℕ) : ℤ) / 4 = -(m : ℤ) := by push_cast; omega
    rw [hdiv] at hsq hm
    have hsq' : Squarefree m := by simpa using Int.squarefree_natAbs.2 hsq
    exact ⟨kroneckerChar (4 * m) (dvd_mul_right 4 m),
      kroneckerChar_isPrimitive hsq' (by omega),
      key _ fun n hn => kroneckerChar_natCast_of_odd _ hn⟩

/-- **Upper bound** `h(−q) ≤ (2e^γ/π) √q (log log q + 5)` for every imaginary quadratic field of
discriminant `−q`, `q ≥ 10¹⁰`, under GRH and the class number formula. -/
theorem classNumberUpperBoundWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberUpperBoundWith 5 := by
  intro K _ _ h2 q hD hq10
  have hq4 := four_lt_of_ge hq10
  have : NeZero q := ⟨by omega⟩
  obtain ⟨χ, hprim, hnorm⟩ := exists_primitive_norm_L1_eq hCNF K h2 hD hq4
  have hU := l1UpperBoundWith_of_GRH hGRH q hq10 χ hprim
  rw [hnorm] at hU
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < q by omega))
  rw [div_le_iff₀ hs] at hU
  rw [show 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + 5)
      = 2 * exp eulerMascheroniConstant * (log (log q) + 5) * √q / π by ring,
    le_div_iff₀ Real.pi_pos]
  linarith

/-- **Lower bound** `h(−q) ≥ √q / (2πe^γ (log log q + 5))` for every imaginary quadratic field
of discriminant `−q`, `q ≥ 10¹⁰`, under GRH and the class number formula. -/
theorem classNumberLowerBoundWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberLowerBoundWith 5 := by
  intro K _ _ h2 q hD hq10
  have hq4 := four_lt_of_ge hq10
  have : NeZero q := ⟨by omega⟩
  obtain ⟨χ, hprim, hnorm⟩ := exists_primitive_norm_L1_eq hCNF K h2 hD hq4
  have hL := l1LowerBoundWith_of_GRH hGRH q hq10 χ hprim
  rw [hnorm] at hL
  set B := 2 * exp eulerMascheroniConstant * (log (log q) + 5)
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < q by omega))
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have ht : 0 < π * classNumber K / √q := by positivity
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hL
  rw [div_le_iff₀ ht] at hL
  rw [show 2 * π * exp eulerMascheroniConstant * (log (log q) + 5) = π * B by ring,
    div_le_iff₀ (by positivity)]
  have : π * classNumber K / √q * √q = π * classNumber K := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hL hs.le]

end LLS
