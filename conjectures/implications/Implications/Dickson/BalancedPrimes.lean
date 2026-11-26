import Implications.Dickson.Consecutive

/-!
# Balanced primes from Dickson's conjecture

Source: `FormalConjectures/Wikipedia/BalancedPrimes.lean`, `BalancedPrimes.balanced_primes` and
`BalancedPrimes.balanced_primes_order`, formal-conjectures `9097e2f` (both research open). The
conclusions below are verbatim. As in the source, `Prime` is `_root_.Prime`, which agrees with
`Nat.Prime` on `ℕ` (`Nat.prime_iff`), and `Nat.nth Prime n` is the `n`-th prime counting from
`0` (`Nat.nth Prime 0 = 2`).

Both follow from runs of consecutive primes in arithmetic progression
(`infinite_index_ap_of_dickson`):

* `balanced_primes`: if `p_n, p_{n+1}, p_{n+2}` are in arithmetic progression then
  `(p_n + p_{n+2}) / 2 = p_{n+1}` is prime;
* `balanced_primes_order`: if `p_{n-k}, …, p_{n+k}` are in arithmetic progression then
  `p_{n-i} + p_{n+i} = 2 p_n` for each `i ≤ k`, so the sum is `2 k p_n`.
-/

namespace Implications.Dickson

theorem prime_eq_natPrime : (Prime : ℕ → Prop) = Nat.Prime :=
  funext fun _ => propext Nat.prime_iff.symm

/-- Source: `FormalConjectures/Wikipedia/BalancedPrimes.lean`, `BalancedPrimes.balanced_primes`,
formal-conjectures `9097e2f` (research open); conclusion verbatim, under Dickson's conjecture. -/
theorem balanced_primes_of_dickson (hD : DicksonConjecture) :
    {n : ℕ | Prime ((Nat.nth Prime n + Nat.nth Prime (n + 2)) / 2)}.Infinite := by
  rw [prime_eq_natPrime]
  refine (infinite_index_ap_of_dickson hD 3 (by norm_num)).mono ?_
  intro c hc
  have h1 := hc 1 (by norm_num)
  have h2 := hc 2 (by norm_num)
  simp only [Set.mem_ofPred_eq]
  rw [h2, show Nat.nth Nat.Prime c + (Nat.nth Nat.Prime c + 2 * Nat.factorial 3) =
      (Nat.nth Nat.Prime c + 1 * Nat.factorial 3) * 2 by ring, Nat.mul_div_cancel _ two_pos,
    ← h1]
  exact Nat.prime_nth_prime _

/-- Source: `FormalConjectures/Wikipedia/BalancedPrimes.lean`,
`BalancedPrimes.balanced_primes_order`, formal-conjectures `9097e2f` (research open); conclusion
verbatim, under Dickson's conjecture. -/
theorem balanced_primes_order_of_dickson (hD : DicksonConjecture) :
    ∀ k > 0, {n : ℕ | k ≤ n ∧ 2 * k * Nat.nth Prime n = ∑ i ∈ .Ioc 0 k,
      ((n - i).nth Prime + (n + i).nth Prime)}.Infinite := by
  intro k hk
  rw [prime_eq_natPrime]
  set K := 2 * k + 1
  have H := infinite_index_ap_of_dickson hD K (by omega)
  have hinj : Set.InjOn (· + k) {c : ℕ | ∀ i < K,
      Nat.nth Nat.Prime (c + i) = Nat.nth Nat.Prime c + i * K.factorial} :=
    fun a _ b _ h => by simpa using h
  refine (H.image hinj).mono ?_
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨Nat.le_add_left k c, ?_⟩
  set P := Nat.nth Nat.Prime c
  set d := K.factorial
  have hterm : ∀ i ∈ Finset.Ioc 0 k,
      (c + k - i).nth Nat.Prime + (c + k + i).nth Nat.Prime = 2 * (P + k * d) := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    rw [show c + k - i = c + (k - i) by omega, show c + k + i = c + (k + i) by ring,
      hc (k - i) (by omega), hc (k + i) (by omega)]
    have : (k - i) * d + (k + i) * d = 2 * (k * d) := by
      rw [← add_mul, show k - i + (k + i) = 2 * k by omega]; ring
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc, smul_eq_mul,
    hc k (by omega), Nat.sub_zero]
  ring

end Implications.Dickson
