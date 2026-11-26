import Implications.Dickson.Linear

/-!
# Dickson's conjecture implies the twin, cousin, sexy and Sophie Germain prime conjectures

Each conclusion is copied word for word from formal-conjectures `9097e2f`:

* `TwinPrimes.twin_primes` (`FormalConjectures/Wikipedia/TwinPrimes.lean`);
* `Dickson.generalized_twin_primes`, `Dickson.infinite_safe_primes`,
  `Dickson.infinite_cousin_primes`, `Dickson.infinite_sexy_primes`
  (`FormalConjectures/Wikipedia/Dickson.lean`).

Several of them use `Prime p` (the general `_root_.Prime`) rather than `Nat.Prime`; on `ℕ` the two
agree (`Nat.prime_iff`). Each follows by applying Dickson's conjecture to two linear forms and
checking the Schinzel condition by hand.
-/

open Polynomial

namespace Implications.Dickson

/-- The Schinzel condition for `{n, n + c}` with `c` even. For `p ∤ c + 1` take `n = 1`;
otherwise `p` is odd and `n = 2` works. -/
theorem schinzel_pair_even (c : ℕ) (hc : Even c) (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ¬ p ∣ 1 * n + 0 ∧ ¬ p ∣ 1 * n + c := by
  obtain ⟨r, rfl⟩ := hc
  have hp1 := hp.one_lt
  by_cases h : p ∣ 1 + (r + r)
  · refine ⟨2, ?_, ?_⟩
    · intro h2
      have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using h2)
      subst this
      omega
    · intro h2
      have : p ∣ 1 := by
        have h2' : p ∣ (1 + (r + r)) + 1 := by simpa [add_comm, add_left_comm, add_assoc] using h2
        exact (Nat.dvd_add_right h).mp h2'
      exact hp.ne_one (Nat.dvd_one.mp this)
  · refine ⟨1, ?_, ?_⟩
    · intro h1
      exact hp.ne_one (Nat.dvd_one.mp (by simpa using h1))
    · simpa [add_comm] using h

/-- Dickson's conjecture gives infinitely many `n` with `n` and `n + c` prime, for `c` even. -/
theorem infinite_prime_add_even_of_dickson (h : DicksonConjecture) (c : ℕ) (hc : Even c) :
    {p : ℕ | p.Prime ∧ (p + c).Prime}.Infinite := by
  have H := infinite_pair_of_dickson h 1 0 1 c one_pos one_pos (by simp) (by simp)
    (schinzel_pair_even c hc)
  simpa using H

/-- Source: `FormalConjectures/Wikipedia/TwinPrimes.lean`, `TwinPrimes.twin_primes`,
formal-conjectures `9097e2f`; conclusion verbatim. -/
theorem twin_primes_of_dickson (h : DicksonConjecture) :
    {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  simpa [← Nat.prime_iff] using infinite_prime_add_even_of_dickson h 2 even_two

/-- Source: `FormalConjectures/Wikipedia/Dickson.lean`, `Dickson.generalized_twin_primes`,
formal-conjectures `9097e2f`; binders and conclusion verbatim. -/
theorem generalized_twin_primes_of_dickson (h : DicksonConjecture) (k : ℕ) (hk : 0 < k) :
    Infinite {p : ℕ | p.Prime ∧ (p + 2 * k).Prime} :=
  Set.infinite_coe_iff.mpr (infinite_prime_add_even_of_dickson h (2 * k) (even_two_mul k))

/-- Source: `FormalConjectures/Wikipedia/Dickson.lean`, `Dickson.infinite_cousin_primes`,
formal-conjectures `9097e2f`; conclusion verbatim. -/
theorem infinite_cousin_primes_of_dickson (h : DicksonConjecture) :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 4)} := by
  rw [Set.infinite_coe_iff]
  simpa [← Nat.prime_iff] using infinite_prime_add_even_of_dickson h 4 (by decide)

/-- Source: `FormalConjectures/Wikipedia/Dickson.lean`, `Dickson.infinite_sexy_primes`,
formal-conjectures `9097e2f`; conclusion verbatim. -/
theorem infinite_sexy_primes_of_dickson (h : DicksonConjecture) :
    Infinite {p : ℕ | Prime p ∧ Prime (p + 6)} := by
  rw [Set.infinite_coe_iff]
  simpa [← Nat.prime_iff] using infinite_prime_add_even_of_dickson h 6 (by decide)

/-- Source: `FormalConjectures/Wikipedia/Dickson.lean`, `Dickson.infinite_safe_primes`,
formal-conjectures `9097e2f`; conclusion verbatim. (The set is the Sophie Germain primes `p`;
the safe primes are the `2p + 1`.) The Schinzel condition for `{n, 2n + 1}`: `n = 1` gives
`1, 3`, which works for `p ≠ 3`; for `p = 3` take `n = 2`, giving `2, 5`. -/
theorem infinite_safe_primes_of_dickson (h : DicksonConjecture) :
    Infinite {p : ℕ | Prime p ∧ Prime (2 * p + 1)} := by
  have H := infinite_pair_of_dickson h 1 0 2 1 one_pos two_pos (by simp) (by simp) ?_
  · rw [Set.infinite_coe_iff]
    simpa [← Nat.prime_iff] using H
  · intro p hp
    by_cases h3 : p = 3
    · subst h3
      exact ⟨2, by decide, by decide⟩
    · refine ⟨1, ?_, ?_⟩
      · intro h1
        exact hp.ne_one (Nat.dvd_one.mp (by simpa using h1))
      · intro h1
        exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using h1))

end Implications.Dickson
