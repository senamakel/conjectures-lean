import Mathlib.NumberTheory.LSeries.WeakPNT

/-!
# A finite arithmetic-progression sieve for prime indices

For a fixed modulus, the prime number theorem in arithmetic progressions gives the exact
asymptotic mass of any finite collection of reduced residue classes. This is the analytic input
needed by the finite-prime sieve for McEachen's recurrence: after a finite set of small primes is
fixed, exceptional prime indices lie in an explicitly specified collection of classes modulo
their product. The theorem here packages that input without assuming any unproved distribution
statement about the recurrence.
-/

open Filter Finset Nat Real Topology

namespace McEachenDensity

/-- The number of primes at most `x` in the residue class `a` modulo `q`. -/
noncomputable def primeCountInClass (q a : ℕ) (x : ℝ) : ℕ :=
  #{p ∈ Ioc 0 ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD q]}

/-- The normalized mass of a finite list of prime residue classes. -/
noncomputable def finiteSieveMass (q : ℕ) (A : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ a ∈ A, (primeCountInClass q a x : ℝ)) * Real.log x / x

/-- The prime number theorem in arithmetic progressions, summed over a finite set of reduced
residue classes. This is useful for turning a finite congruence sieve into a relative-density
bound among primes. -/
theorem tendsto_finiteSieveMass {q : ℕ} [NeZero q] (A : Finset ℕ)
    (hA : ∀ a ∈ A, a.Coprime q) :
    Tendsto (finiteSieveMass q A) atTop (𝓝 ((A.card : ℝ) / q.totient)) := by
  have hclass (a : ℕ) (ha : a ∈ A) :
      Tendsto (fun x : ℝ => (primeCountInClass q a x : ℝ) * Real.log x / x)
        atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
    simpa [primeCountInClass, div_eq_mul_inv, mul_assoc] using
      Nat.tendsto_card_prime_modEq_mul_log_div_atTop (q := q) (a := a) (hA a ha)
  have hsum : Tendsto
      (fun x : ℝ => ∑ a ∈ A,
        (primeCountInClass q a x : ℝ) * Real.log x / x)
      atTop (𝓝 (∑ _a ∈ A, (q.totient : ℝ)⁻¹)) := by
    apply tendsto_finsetSum A
    intro a ha
    exact hclass a ha
  convert hsum using 1
  · ext x
    simp [finiteSieveMass, Finset.sum_mul, div_eq_mul_inv, mul_assoc]
  · simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end McEachenDensity
