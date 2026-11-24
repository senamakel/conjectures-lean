import Weinberger.Elementary
import Weinberger.Character
import Weinberger.GRH
import Weinberger.Sieve
import Weinberger.Numerics
import Erdos985.Analytic.Principal

/-!
# Under GRH, no `n ≥ 10^8` is idoneal

Let `n ≥ 10^8` be idoneal, `x = ⌊√n⌋` and `ψ` the primitive character inducing `χ_{−4n}`. By
`not_isSquare_of_isIdoneal`, `ψ(p) = −1` at every odd prime `p < x` with `p ∤ n`. Let `P` be the
primes `p < x` with `p² < x` or `p ∣ 2n`; then `ψ(p) = −1` at every prime `p < x` outside `P`.

* If some prime `p < x` lies outside `P`, then `ψ ≠ 1`, and
  `S₀ + Re S_ψ = splitSum ψ x ≤ 2 #P log x` (`splitSum_le`), while under GRH
  `S₀ ≥ x/2 − √x/20 − 3` (`bach_principal_of_GRH`) and `‖S_ψ‖ ≤ B` (`bach_primitive_of_GRH`).
* Otherwise every prime `p < x` is in `P`, and `2 S₀ = splitSum 1 x ≤ 2 #P log x`.

Since `#P ≤ √x + 1 + ω(2n)` and `2^{ω(2n)} ≤ 2n`, both contradict `numerics`.
-/

namespace Weinberger

open ArithmeticFunction Finset Erdos985 Idoneal

/-- `splitSum` splits as the principal sum plus the real part of Bach's sum. -/
theorem splitSum_eq {N : ℕ} (ψ : DirichletCharacter ℂ N) (x : ℕ) :
    splitSum ψ x = ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) + (bachSum ψ x).re := by
  rw [splitSum, bachSum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (Λ m : ℂ) * ψ m * (1 - (m : ℂ) / x) = (((Λ m : ℝ) * (1 - (m : ℝ) / x) : ℝ) : ℂ) * ψ m := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  ring

theorem splitSum_one (x : ℕ) :
    splitSum (1 : DirichletCharacter ℂ 1) x = 2 * ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) := by
  rw [splitSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (1 : DirichletCharacter ℂ 1) m = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  rw [this]; simp only [Complex.one_re]; ring

/-- **The GRH step.** Under GRH, every `n ≥ 10^8` has an odd prime `p ∤ n` with `p² < n` at
which `−n` is a square mod `p` (a prime that splits in `ℚ(√−n)`). -/
theorem exists_split_prime_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) {n : ℕ}
    (hn : 10 ^ 8 ≤ n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ n ∧ p * p < n ∧ IsSquare (-(n : ZMod p)) := by
  by_contra hcon
  have hns : ∀ p, p.Prime → p ≠ 2 → ¬ p ∣ n → p * p < n → ¬ IsSquare (-(n : ZMod p)) :=
    fun p hp hp2 hpn hpp hsq => hcon ⟨p, hp, hp2, hpn, hpp, hsq⟩
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  set x := Nat.sqrt n with hx_def
  have hxx : x * x ≤ n := Nat.sqrt_le n
  have hnx : n < (x + 1) * (x + 1) := Nat.lt_succ_sqrt n
  have hx4 : 10 ^ 4 ≤ x := Nat.le_sqrt.2 (by norm_num; omega)
  have hx1 : 1 ≤ x := by omega
  set χ := kroneckerChar n
  set ψ := χ.primitiveCharacter
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set P : Finset ℕ := (range x).filter (fun p => p.Prime ∧ (p * p < x ∨ p ∣ 2 * n)) with hP_def
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.1 hp).2.1
  have hsq : ∀ p, p.Prime → p < x → p * p < x → p ∈ P := fun p hp hpx hpp =>
    mem_filter.2 ⟨mem_range.2 hpx, hp, Or.inl hpp⟩
  -- the values of `χ` and `ψ` at good primes
  have hgood : ∀ p, p.Prime → p < x → p ∉ P → χ p = -1 ∧ ψ p = -1 := by
    intro p hp hpx hpP
    have hn2 : ¬ p ∣ 2 * n := fun h => hpP (mem_filter.2 ⟨mem_range.2 hpx, hp, Or.inr h⟩)
    have hp2 : p ≠ 2 := by rintro rfl; exact hn2 (dvd_mul_right 2 n)
    have hpn : ¬ p ∣ n := fun h => hn2 (Dvd.dvd.mul_left h 2)
    have hpp : p * p < n := lt_of_lt_of_le (Nat.mul_self_lt_mul_self hpx) hxx
    haveI := Fact.mk hp
    have hns := hns p hp hp2 hpn hpp
    have hleg : legendreSym p (-(n : ℤ)) = -1 := by
      rw [legendreSym.eq_neg_one_iff]; push_cast; exact hns
    have hχp : χ p = -1 := by
      rw [kroneckerChar_prime n hp2 hpn, hleg]; simp
    have hcop : Nat.Coprime p (4 * n) := by
      refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hψp : ψ p = χ p := by
      have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ (a := (p : ℤ))
        (by exact_mod_cast Nat.isCoprime_iff_coprime.2 hcop)
      simpa using this
    exact ⟨hχp, hψp.trans hχp⟩
  -- the card of `P`
  set ω := (2 * n).primeFactors.card
  have hPcard : (P.card : ℝ) ≤ √(x : ℝ) + 1 + ω := by
    have hsub : P ⊆ range (Nat.sqrt x + 1) ∪ (2 * n).primeFactors := by
      intro p hp
      obtain ⟨-, hpr, h⟩ := mem_filter.1 hp
      rcases h with h | h
      · exact mem_union_left _ (mem_range.2 (Nat.lt_succ_of_le (Nat.le_sqrt.2 h.le)))
      · exact mem_union_right _ (Nat.mem_primeFactors.2 ⟨hpr, h, by omega⟩)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at h1
    have h2 : (P.card : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 + ω := by exact_mod_cast h1
    have h3 := Real.nat_sqrt_le_real_sqrt (a := x)
    linarith
  have hω : (ω : ℝ) * Real.log 2 ≤ Real.log (2 * n) := by
    have h := two_pow_card_primeFactors_le (m := 2 * n) (by omega)
    have : Real.log ((2 : ℝ) ^ ω) ≤ Real.log (2 * n) :=
      Real.log_le_log (by positivity) (by exact_mod_cast h)
    rwa [Real.log_pow] at this
  -- the analytic inputs
  have hxR : (10 : ℝ) ^ 4 ≤ x := by exact_mod_cast hx4
  have hnR : (n : ℝ) < ((x : ℝ) + 1) ^ 2 := by
    have : (n : ℝ) < ((x + 1) * (x + 1) : ℕ) := by exact_mod_cast hnx
    push_cast at this; nlinarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx1)
  have hprin := Analytic.bach_principal_of_GRH hGRH x hx1
  set S₀ := ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x)
  have hS₀ : (x : ℝ) / 2 - √(x : ℝ) / 20 - 3 ≤ S₀ := by
    have := (abs_le.mp hprin).1; linarith
  have hN1 : (1 : ℝ) ≤ χ.conductor := by
    have := Nat.pos_of_ne_zero χ.conductor_ne_zero; exact_mod_cast this
  have hN : (χ.conductor : ℝ) ≤ 4 * n := by
    have := Nat.le_of_dvd (by omega) χ.conductor_dvd_level; exact_mod_cast this
  have hnum := numerics hxR hN1 hN hnR (by exact_mod_cast hn0) (by positivity) hω
  have hB0 : 0 ≤ (√(x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log χ.conductor + 5 / 3))
      + (Real.log x + 1) + 0.6 := by
    have : 0 ≤ Real.log χ.conductor := Real.log_nonneg hN1
    positivity
  by_cases hex : ∃ p, p.Prime ∧ p < x ∧ p ∉ P
  · obtain ⟨p, hp, hpx, hpP⟩ := hex
    have hψ1 : ψ ≠ 1 := by
      intro h1
      have hval := (hgood p hp hpx hpP).2
      have hunit : IsUnit (p : ZMod χ.conductor) := by
        rw [ZMod.isUnit_iff_coprime]
        have hpn : ¬ p ∣ 2 * n := fun h => hpP (mem_filter.2 ⟨mem_range.2 hpx, hp, Or.inr h⟩)
        refine Nat.Coprime.coprime_dvd_right χ.conductor_dvd_level ?_
        have hp2 : p ≠ 2 := by rintro rfl; exact hpn (dvd_mul_right 2 n)
        have hpn' : ¬ p ∣ n := fun h => hpn (Dvd.dvd.mul_left h 2)
        refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn')
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      rw [h1, MulChar.one_apply hunit] at hval
      norm_num at hval
    have hbach := bach_primitive_of_GRH hGRH (χ.primitiveCharacter_isPrimitive) hψ1 x hx1
    have hsplit := splitSum_le ψ hx1 P hPp hsq (fun p hp hpx hpP => (hgood p hp hpx hpP).2)
    rw [splitSum_eq] at hsplit
    have hre : -‖bachSum ψ x‖ ≤ (bachSum ψ x).re := by
      have := Complex.abs_re_le_norm (bachSum ψ x)
      have := neg_abs_le (bachSum ψ x).re
      linarith
    have : 2 * (P.card : ℝ) * Real.log x ≤ 2 * (√(x : ℝ) + 1 + ω) * Real.log x := by
      have := mul_le_mul_of_nonneg_right hPcard hlogx; nlinarith
    linarith
  · push_neg at hex
    have hsplit := splitSum_le (1 : DirichletCharacter ℂ 1) hx1 P hPp hsq
      (fun p hp hpx hpP => absurd (hex p hp hpx) hpP)
    rw [splitSum_one] at hsplit
    have : 2 * (P.card : ℝ) * Real.log x ≤ 2 * (√(x : ℝ) + 1 + ω) * Real.log x := by
      have := mul_le_mul_of_nonneg_right hPcard hlogx; nlinarith
    have hsx : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
    have hω0 : (0 : ℝ) ≤ ω := by positivity
    nlinarith

/-- Under GRH, no `n ≥ 10^8` is idoneal. -/
theorem not_isIdoneal_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) {n : ℕ}
    (hn : 10 ^ 8 ≤ n) : ¬ IsIdoneal n := by
  intro hid
  obtain ⟨p, hp, hp2, hpn, hpp, hsq⟩ := exists_split_prime_of_GRH hGRH hn
  exact not_isSquare_of_isIdoneal hid hp hp2 hpn hpp hsq

end Weinberger
