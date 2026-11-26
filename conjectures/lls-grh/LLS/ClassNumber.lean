import LLS.L1.Final
import LLS.Statement2

/-!
# Class numbers of imaginary quadratic fields under GRH (LLS Corollary 1.3, weaker constants)

LLS Corollary 1.3 (`LLS.ClassNumberUpperBound`, `LLS.ClassNumberLowerBound` in
`LLS/Statement2.lean`, not proved here) is LLS Theorem 1.5 combined with Dirichlet's class
number formula `h(−q) = (√q/π) L(1, χ_{−q})`. We combine the formula (the tier-H hypothesis
`LLS.ClassNumberFormula`) with our weaker Theorem 1.5 (`L1UpperBoundWith 5`,
`L1LowerBoundWith 5`), for the odd fundamental discriminants `−q` (`q ≡ 3 (mod 4)` squarefree,
which includes every prime `q ≡ 3 (mod 4)`), `q ≥ 10¹⁰`:

* `h(−q) ≤ (2e^γ/π) √q (log log q + 5)` (LLS: `log log q − log 2 + 1/2 + 1/log log q`);
* `h(−q) ≥ √q / (2π e^γ (log log q + 5))` (LLS: `(π/(12e^γ)) √q / (log log q − log 2 + …)`).

For such `q` the Kronecker symbol `χ_{−q}` is the Jacobi symbol `n ↦ J(n | q)` (quadratic
reciprocity, `jacobiChar_kronecker`), and it is primitive mod `q` (`jacobiChar_isPrimitive`:
if it factored through `q/p` for a prime `p ∣ q`, an `n ≡ 1 (mod q/p)` that is a non-residue
mod `p` would give `1 = J(n | q) = −1`). Theorem 1.5 is for primitive characters, so this is
what the argument needs.

The hypotheses `q % 4 = 3` and `Squarefree q` are not restrictions on the fields covered beyond
"odd discriminant": if `discr K = −q` with `q` odd then both hold (Stickelberger, and `−q` is a
fundamental discriminant). Neither fact is in Mathlib at this pin, so they are stated.

Even discriminants `−q = −4m` are not covered: the Kronecker symbol there involves `χ₄`, `χ₈`
and needs its own construction and primitivity proof at `2`, and the fact that `m ≡ 1, 2
(mod 4)` is squarefree.
-/

namespace LLS

open Erdos985 Real NumberField Module

/-- Upper bound of LLS Corollary 1.3's shape with additive constant `C`, for odd fundamental
discriminants `−q` (`q ≡ 3 (mod 4)` squarefree), `q ≥ 10¹⁰`. -/
def ClassNumberUpperBoundOddWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, q % 4 = 3 →
    Squarefree q → discr K = -q → (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ) ≤ 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + C)

/-- Lower bound of LLS Corollary 1.3's shape (leading constant `1/(2πe^γ)`, LLS: `π/(12e^γ)`)
with additive constant `C`, for odd fundamental discriminants `−q`, `q ≥ 10¹⁰`. -/
def ClassNumberLowerBoundOddWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, q % 4 = 3 →
    Squarefree q → discr K = -q → (10 : ℝ) ^ 10 ≤ q →
      √q / (2 * π * exp eulerMascheroniConstant * (log (log q) + C)) ≤ classNumber K

lemma jacobiSym_mod (q n : ℕ) : jacobiSym ((n % q : ℕ) : ℤ) q = jacobiSym n q := by
  rw [jacobiSym.mod_left (n : ℤ)]
  push_cast
  rfl

/-- The Jacobi symbol `x ↦ J(x | q)` as a complex Dirichlet character mod `q`. -/
noncomputable def jacobiChar (q : ℕ) [NeZero q] : DirichletCharacter ℂ q where
  toFun x := ((jacobiSym (x.val : ℕ) q : ℤ) : ℂ)
  map_one' := by
    show ((jacobiSym (((1 : ZMod q).val : ℕ) : ℤ) q : ℤ) : ℂ) = 1
    rw [ZMod.val_one_eq_one_mod, jacobiSym_mod, Nat.cast_one, jacobiSym.one_left, Int.cast_one]
  map_mul' x y := by
    show ((jacobiSym (((x * y).val : ℕ) : ℤ) q : ℤ) : ℂ)
      = ((jacobiSym ((x.val : ℕ) : ℤ) q : ℤ) : ℂ) * ((jacobiSym ((y.val : ℕ) : ℤ) q : ℤ) : ℂ)
    rw [ZMod.val_mul, jacobiSym_mod, Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' x hx := by
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
    show ((jacobiSym ((x.val : ℕ) : ℤ) q : ℤ) : ℂ) = 0
    rw [Int.cast_eq_zero, jacobiSym.eq_zero_iff]
    exact ⟨NeZero.ne q, by rwa [Int.gcd_natCast_natCast]⟩

section Jacobi

variable {q : ℕ} [NeZero q]

lemma jacobiChar_natCast (n : ℕ) : jacobiChar q n = ((jacobiSym n q : ℤ) : ℂ) := by
  change ((jacobiSym ((n : ZMod q).val : ℕ) q : ℤ) : ℂ) = _
  rw [ZMod.val_natCast, jacobiSym_mod]

/-- For `q ≡ 3 (mod 4)` the Jacobi symbol mod `q` is the Kronecker symbol `χ_{−q}`. -/
lemma jacobiChar_kronecker (h4 : q % 4 = 3) (n : ℕ) (hn : Odd n) :
    jacobiChar q n = ((jacobiSym (-(q : ℤ)) n : ℤ) : ℂ) := by
  rw [jacobiChar_natCast, jacobiSym.neg _ hn]
  congr 1
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hn) with h1 | h1
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.2 (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h1, jacobiSym.quadratic_reciprocity_three_mod_four h1 h4]
    ring

/-- For odd squarefree `q > 1` the Jacobi symbol mod `q` is primitive. -/
lemma jacobiChar_isPrimitive (hodd : Odd q) (hsq : Squarefree q) : (jacobiChar q).IsPrimitive := by
  by_contra hne
  set c := (jacobiChar q).conductor with hcdef
  obtain ⟨hc, χ₀, hχ₀⟩ := (jacobiChar q).factorsThrough_conductor
  have ⟨k, hk⟩ := hc
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (by rw [DirichletCharacter.isPrimitive_def]; simpa using hk.symm)
  obtain ⟨p, hp, j, rfl⟩ := Nat.exists_prime_and_dvd hk1
  -- `q = (c j) p`, with `c j` and `p` coprime
  have hq : q = c * j * p := by rw [hk]; ring
  have hco : (c * j).Coprime p := Nat.coprime_of_squarefree_mul (hq ▸ hsq)
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hq] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (by simp)
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hco 1 a.val
  -- `J(n | q) = J(n | c j) J(n | p) = 1 · (−1)`
  have hcj0 : c * j ≠ 0 := by
    intro h; rw [h, zero_mul] at hq; exact NeZero.ne q hq
  have : NeZero (c * j) := ⟨hcj0⟩
  have hJ1 : jacobiSym n (c * j) = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast hn1), jacobiSym.one_left]
  have hJ2 : jacobiSym n p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : ((n : ℤ) : ZMod p) = a := by
      rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 hn2, ZMod.natCast_zmod_val]
    rwa [this]
  have hJ : jacobiChar q n = -1 := by
    rw [jacobiChar_natCast, hq, jacobiSym.mul_right, hJ1, hJ2]
    norm_num
  -- but `χ` factors through `c ∣ c j`, and `n ≡ 1 (mod c)`
  have hunit : IsUnit (n : ZMod q) := by
    by_contra h
    rw [MulChar.map_nonunit _ h] at hJ
    norm_num at hJ
  have hcop : IsCoprime (n : ℤ) (q : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (ZMod.isUnit_iff_coprime n q).1 hunit
  have h1 : ((n : ℤ) : ZMod c) = 1 := by
    rw [Int.cast_natCast]
    have : n ≡ 1 [MOD c] := Nat.ModEq.of_mul_right j hn1
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 this, Nat.cast_one]
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hc hcop
  rw [← hχ₀, h1, MulChar.map_one] at this
  rw [show ((n : ℤ) : ZMod q) = (n : ZMod q) by simp, hJ] at this
  norm_num at this

lemma jacobiChar_ne_one (hq1 : 1 < q) (hodd : Odd q) (hsq : Squarefree q) : jacobiChar q ≠ 1 := by
  intro h
  have := jacobiChar_isPrimitive hodd hsq
  rw [h, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
  omega

end Jacobi

/-- The class number formula for an odd fundamental discriminant `−q`, in the form used below:
`‖L(1, J(· | q))‖ = π h(−q)/√q`. -/
lemma norm_L1_jacobi_eq (hCNF : ClassNumberFormula) (K : Type) [Field K] [NumberField K]
    (h2 : finrank ℚ K = 2) {q : ℕ} [NeZero q] (h4 : q % 4 = 3) (hD : discr K = -q)
    (hq : 4 < q) :
    ‖DirichletCharacter.LFunction (jacobiChar q) 1‖ = π * classNumber K / √q := by
  rw [hCNF K q h2 hD hq (jacobiChar q) (jacobiChar_kronecker h4), Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

lemma four_lt_of_ge {q : ℕ} (hq10 : (10 : ℝ) ^ 10 ≤ q) : 4 < q := by
  have : (4 : ℝ) < q := lt_of_lt_of_le (by norm_num) hq10
  exact_mod_cast this

/-- **Upper bound** `h(−q) ≤ (2e^γ/π) √q (log log q + 5)` for odd fundamental discriminants
`−q`, `q ≥ 10¹⁰`, under GRH and the class number formula. -/
theorem classNumberUpperBoundOddWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberUpperBoundOddWith 5 := by
  intro K _ _ h2 q h4 hsq hD hq10
  have hq4 := four_lt_of_ge hq10
  have : NeZero q := ⟨by omega⟩
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  have hU := l1UpperBoundWith_of_GRH hGRH q hq10 (jacobiChar q) (jacobiChar_isPrimitive hodd hsq)
  rw [norm_L1_jacobi_eq hCNF K h2 h4 hD hq4] at hU
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < q by omega))
  rw [div_le_iff₀ hs] at hU
  rw [show 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + 5)
      = 2 * exp eulerMascheroniConstant * (log (log q) + 5) * √q / π by ring,
    le_div_iff₀ Real.pi_pos]
  linarith

/-- **Lower bound** `h(−q) ≥ √q / (2πe^γ (log log q + 5))` for odd fundamental discriminants
`−q`, `q ≥ 10¹⁰`, under GRH and the class number formula. -/
theorem classNumberLowerBoundOddWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberLowerBoundOddWith 5 := by
  intro K _ _ h2 q h4 hsq hD hq10
  have hq4 := four_lt_of_ge hq10
  have : NeZero q := ⟨by omega⟩
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  have hL := l1LowerBoundWith_of_GRH hGRH q hq10 (jacobiChar q) (jacobiChar_isPrimitive hodd hsq)
  rw [norm_L1_jacobi_eq hCNF K h2 h4 hD hq4] at hL
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
