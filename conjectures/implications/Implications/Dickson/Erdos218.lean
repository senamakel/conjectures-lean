import Implications.Dickson.Consecutive

/-!
# Erdős Problem 218, equal consecutive prime gaps, from Dickson's conjecture

Source: `FormalConjectures/ErdosProblems/218.lean`, `Erdos218.erdos_218.variants.infinite_equal_prime_gap`,
formal-conjectures `9097e2f` (research open). The conclusion below is verbatim, and so is
`primeGap` (`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, root namespace there; here in
`Implications.Dickson`).

Three consecutive primes in arithmetic progression (`infinite_index_ap_of_dickson` with `k = 3`)
give two equal consecutive gaps.
-/

namespace Implications.Dickson

/-- Source: `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, `primeGap`,
formal-conjectures `9097e2f`, verbatim.

The prime gap: the difference between the $n+1$-th and $n$-th prime.
-/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- Source: `FormalConjectures/ErdosProblems/218.lean`,
`Erdos218.erdos_218.variants.infinite_equal_prime_gap`, formal-conjectures `9097e2f`
(research open); conclusion verbatim, under Dickson's conjecture. -/
theorem erdos_218_infinite_equal_prime_gap_of_dickson (hD : DicksonConjecture) :
    {n | primeGap n = primeGap (n + 1)}.Infinite := by
  refine (infinite_index_ap_of_dickson hD 3 (by norm_num)).mono ?_
  intro c hc
  have h1 := hc 1 (by norm_num)
  have h2 := hc 2 (by norm_num)
  simp only [Set.mem_ofPred_eq, primeGap]
  rw [show c + 1 + 1 = c + 2 by ring, h1, h2]
  omega

end Implications.Dickson
