import SunA243164.Assembly
import SunA243164.TwistedSieve
import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.Principal

/-!
# The GRH step: a bad prime violates every sieve inequality

Let `P` be a prime that is not a `GoodPrime`, `x = π(P)` and `a = x mod P`. Then no prime
`q < x` makes `a q` a primitive root, so `SunA243164.Sieve.principal_le_sieve_twisted` applies
with erdos-985's GRH bounds `bach_nonprincipal_of_GRH` (for every `χ ≠ 1`, at this `x`) and
`bach_principal_of_GRH` (`S₀ ≥ x/2 - √x/20 - 3`). The result is that the explicit inequality
`SieveIneq P S` fails for every admissible sieving set `S`.

`SieveNumerics N` is the purely numerical statement that for every prime `P ≥ N` some
admissible `S` satisfies `SieveIneq P S`. It contains no L-function and no GRH; together with
GRH it gives `GoodFrom N` (`goodFrom_of_GRH`).
-/

namespace SunA243164

open ArithmeticFunction Finset Erdos985 Sieve

/-- `δ_S = 1 - Σ_{ℓ ∈ S} 1/ℓ`. -/
noncomputable def deltaOf (S : Finset ℕ) : ℝ := 1 - ∑ ℓ ∈ S, 1 / (ℓ : ℝ)

/-- The sieve constant `K = 2^{|E|}(2 + (|S| - 1)/δ) - 1`, `E = F \ S`. -/
noncomputable def sieveK (P : ℕ) (S : Finset ℕ) : ℝ :=
  (2 : ℝ) ^ ((P - 1).primeFactors.card - S.card) * (2 + ((S.card : ℝ) - 1) / deltaOf S) - 1

/-- The explicit inequality that rules out a bad prime `P` with sieving set `S`, at the search
length `x = π(P)`. -/
def SieveIneq (P : ℕ) (S : Finset ℕ) : Prop :=
  let x := Nat.primeCounting P
  Epp x < deltaOf S * θ ((P - 1).primeFactors \ S) *
    ((x : ℝ) / 2 - (√(x : ℝ) / 20 + 3) - sieveK P S * (bachC P x * √(x : ℝ) * Real.log P))

/-- The numerical input: every prime `P ≥ N` has an admissible `S` with `SieveIneq P S`. -/
def SieveNumerics (N : ℕ) : Prop :=
  ∀ P : ℕ, P.Prime → N ≤ P →
    ∃ S ⊆ (P - 1).primeFactors, 0 < deltaOf S ∧ SieveIneq P S

lemma primeCounting_lt_self {P : ℕ} (hP : 2 ≤ P) : Nat.primeCounting P < P := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range (P + 1)).filter Nat.Prime ⊆ ((range (P + 1)).erase 0).erase 1 := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    simp only [mem_erase, mem_range]
    exact ⟨hn.2.one_lt.ne', hn.2.ne_zero, hn.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (by simp; omega), card_erase_of_mem (by simp; omega), card_range] at this
  omega

lemma primeCounting_pos {P : ℕ} (hP : 2 ≤ P) : 0 < Nat.primeCounting P :=
  lt_of_lt_of_le (by decide : 0 < Nat.primeCounting 2) (Nat.monotone_primeCounting hP)

/-- **GRH step.** Under GRH a prime `P ≠ 2` that is not good violates `SieveIneq P S` for
every admissible `S`. -/
theorem not_sieveIneq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) {P : ℕ} (hP : P.Prime)
    (hP2 : P ≠ 2) (hbad : ¬ GoodPrime P) {S : Finset ℕ} (hS : S ⊆ (P - 1).primeFactors)
    (hδ : 0 < deltaOf S) : ¬ SieveIneq P S := by
  haveI : Fact P.Prime := ⟨hP⟩
  have hP2' : 2 ≤ P := hP.two_le
  set x := Nat.primeCounting P with hx
  have hx1 : 1 ≤ x := primeCounting_pos hP2'
  have hxP : x ≤ P := (primeCounting_lt_self hP2').le
  set a : ZMod P := (x : ZMod P) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hx1 h
    have := primeCounting_lt_self hP2'
    omega
  have hno : ∀ q, q.Prime → q < x → orderOf (a * (q : ZMod P)) ≠ P - 1 := by
    intro q hq hqx hord
    refine hbad ⟨q, hq, hqx, ?_⟩
    rw [Nat.cast_mul, mul_comm]
    exact hord
  have hB := fun χ hχ => Analytic.bach_nonprincipal_of_GRH hGRH P χ hχ x hx1
  have key := principal_le_sieve_twisted P hP2 a ha0 x hxP _ hB hno S hS hδ
  have hprin := (abs_le.mp (Analytic.bach_principal_of_GRH hGRH x hx1)).1
  have hθ : 0 < θ ((P - 1).primeFactors \ S) :=
    Finset.prod_pos fun ℓ hℓ => aR_pos (two_le_of_mem P (Finset.sdiff_subset hℓ))
  intro hineq
  simp only [SieveIneq] at hineq
  rw [← hx] at hineq
  change Epp x < deltaOf S * θ _ * _ at hineq
  have hpos : 0 < deltaOf S * θ ((P - 1).primeFactors \ S) := mul_pos hδ hθ
  have hmono : deltaOf S * θ ((P - 1).primeFactors \ S) *
      ((x : ℝ) / 2 - (√(x : ℝ) / 20 + 3) - sieveK P S * (bachC P x * √(x : ℝ) * Real.log P))
      ≤ deltaOf S * θ ((P - 1).primeFactors \ S) *
      (∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)
        - sieveK P S * (bachC P x * √(x : ℝ) * Real.log P)) := by
    apply mul_le_mul_of_nonneg_left _ hpos.le
    linarith
  unfold sieveK deltaOf at hmono
  unfold deltaOf at hineq
  linarith

/-- GRH plus the numerics give every prime `P ≥ N` (`N ≥ 3`). -/
theorem goodFrom_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) {N : ℕ} (hN : 3 ≤ N)
    (hnum : SieveNumerics N) : GoodFrom N := by
  intro P hP hNP
  by_contra hbad
  obtain ⟨S, hS, hδ, hineq⟩ := hnum P hP hNP
  exact not_sieveIneq_of_GRH hGRH hP (by omega) hbad hS hδ hineq

end SunA243164
