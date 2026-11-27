import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.Exponential

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

/-- The reciprocal-prime term, written as a sequence on all naturals. -/
noncomputable def primeReciprocalTerm (n : ℕ) : ℝ :=
  if n.Prime then 1 / n else 0

/-- The finite Euler product over primes below `n` with local factor `1 - 1/p`. -/
noncomputable def reciprocalPrimeProduct (n : ℕ) : ℝ :=
  ∏ p ∈ range n, (1 - primeReciprocalTerm p)

/-- The finite Euler products over the primes tend to zero. The proof uses only the divergence of
the sum of reciprocal primes and `1 - x ≤ exp (-x)`. -/
theorem tendsto_reciprocalPrimeProduct_zero :
    Tendsto reciprocalPrimeProduct atTop (𝓝 0) := by
  have hnot : ¬ Summable primeReciprocalTerm := by
    convert not_summable_one_div_on_primes using 1 <;>
      ext n <;> simp [primeReciprocalTerm, Set.indicator_apply]
  have hnonneg : ∀ n, 0 ≤ primeReciprocalTerm n := by
    intro n
    simp only [primeReciprocalTerm]
    split_ifs <;> positivity
  have hsum : Tendsto (fun n : ℕ => ∑ p ∈ range n, primeReciprocalTerm p) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnot
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (-∑ p ∈ range n, primeReciprocalTerm p)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact Filter.tendsto_neg_atBot_iff.mpr hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℕ => (0 : ℝ)) (h := fun n =>
        Real.exp (-∑ p ∈ range n, primeReciprocalTerm p))
  · exact tendsto_const_nhds
  · exact hexp
  · intro n
    unfold reciprocalPrimeProduct
    calc
      (0 : ℝ) ≤ ∏ p ∈ range n, (1 - primeReciprocalTerm p) := by
        apply Finset.prod_nonneg
        intro p hp
        apply Finset.prod_nonneg
        intro p hp
        have hp1 : primeReciprocalTerm p ≤ 1 := by
          simp only [primeReciprocalTerm]
          split_ifs with hprime
          · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
            have hp0 : (0 : ℝ) < p := by linarith
            rw [one_div]
            exact (inv_le_one₀ hp0).2 (by linarith)
          · simp
        linarith
  · intro n
    unfold reciprocalPrimeProduct
    calc
      ∏ p ∈ range n, (1 - primeReciprocalTerm p) ≤
          ∏ p ∈ range n, Real.exp (-primeReciprocalTerm p) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp1 : primeReciprocalTerm p ≤ 1 := by
            simp only [primeReciprocalTerm]
            split_ifs with hprime
            · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
              have hp0 : (0 : ℝ) < p := by linarith
              rw [one_div]
              exact (inv_le_one₀ hp0).2 (by linarith)
            · simp
          linarith
        · intro p hp
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-∑ p ∈ range n, primeReciprocalTerm p) := by
        rw [Finset.prod_exp]
        congr 1
        simp [Finset.sum_neg_distrib]

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
