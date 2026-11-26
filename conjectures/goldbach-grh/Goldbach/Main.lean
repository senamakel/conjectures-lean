import Goldbach.Statement
import Goldbach.Compute.BinaryAll
import Goldbach.Compute.LadderAll

/-!
# Ternary Goldbach up to `10²⁰`, and the assembly with Zinoviev's theorem

1. `binary_goldbach_upTo`: every even `4 ≤ m ≤ 2·10¹²` is a sum of two primes (200 sieve
   chunks, `Goldbach/Compute/BinaryAll.lean`).
2. `ladder_covers`: every `y ∈ [2·10¹², 10²⁰]` has a prime `q ≤ y` with `y − q < 2·10¹² − 4`
   (100 ladder chunks, `Goldbach/Compute/LadderAll.lean`).
3. `ternary_goldbach_upTo`: every odd `5 < n ≤ 10²⁰` is a sum of three primes. For
   `n ≤ 2·10¹² + 3` take `n = 3 + (n − 3)`; above, take the ladder prime `q` for `y = n − 4`,
   so that `n − q` is even with `4 ≤ n − q ≤ 2·10¹²`.
4. `ternary_goldbach_of_GRH`: with Zinoviev's theorem (a cited hypothesis) for `n > 10²⁰`.
-/

namespace Goldbach

open Goldbach.Check Erdos985

theorem binary_goldbach_upTo : BinaryGoldbachUpTo (2 * 10 ^ 12) := by
  intro m hm2 hm hmN
  by_cases h4 : m = 4
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by omega⟩
  have hm6 : 6 ≤ m := by obtain ⟨c, hc⟩ := hm; omega
  set j := (m - 6) / 10000000000 with hj
  have hjlt : j < 200 := by omega
  have hchunk := binary_chunks_ok j hjlt
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbachChunk_sound hchunk m hm (by omega) (by omega)
  exact ⟨p, q, hp, hq, hpq.symm⟩

theorem ladder_covers : Covers 1999999999996 2000000000000 100000000000000000000 := by
  intro y h1 h2
  have hG : 0 < 1999999999996 := by norm_num
  by_cases h0 : y < 1000000000000000000
  · have := ladderCover_sound hG (ladder_chunks_ok 0 (by norm_num))
    simp only [ite_true, zero_add, one_mul] at this
    exact this y h1 (by omega)
  · set j := min (y / 1000000000000000000) 99 with hj
    have hj1 : 1 ≤ j := by omega
    have hj99 : j < 100 := by omega
    have := ladderCover_sound hG (ladder_chunks_ok j hj99)
    rw [ite_eq_right (by omega)] at this
    exact this y (by omega) (by omega)

theorem ternary_goldbach_upTo : TernaryGoldbachUpTo (10 ^ 20) := by
  intro n hn5 hn hnN
  have hnN' : n ≤ 100000000000000000000 := by norm_num at hnN; exact hnN
  have hbin : BinaryGoldbachUpTo 2000000000000 := by
    have := binary_goldbach_upTo; norm_num at this; exact this
  obtain ⟨a, ha⟩ := hn
  by_cases hsmall : n ≤ 2000000000003
  · obtain ⟨p, q, hp, hq, hpq⟩ := hbin (n - 3) (by omega) ⟨a - 1, by omega⟩ (by omega)
    exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩
  · obtain ⟨q, hq, hqy, hyq⟩ := ladder_covers (n - 4) (by omega) (by omega)
    have hq2 : q ≠ 2 := by intro h; subst h; omega
    obtain ⟨b, hb⟩ := hq.odd_of_ne_two hq2
    obtain ⟨p, r, hp, hr, hpr⟩ := hbin (n - q) (by omega) ⟨a - b, by omega⟩ (by omega)
    exact ⟨q, p, r, hq, hp, hr, by omega⟩

/-- Ternary Goldbach from any proof of the range above `10²⁰` (for instance Zinoviev's
theorem under GRH, or Helfgott's unconditional theorem). -/
theorem ternary_goldbach_of_large
    (hlarge : ∀ n : ℕ, 10 ^ 20 < n → Odd n →
      ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) :
    TernaryGoldbachStatement := by
  intro n hn5 hn
  by_cases h : n ≤ 10 ^ 20
  · exact ternary_goldbach_upTo n hn5 hn h
  · exact hlarge n (Nat.lt_of_not_le h) hn

/-- **Ternary Goldbach under GRH, given Zinoviev's theorem** (Deshouillers–Effinger–te Riele–
Zinoviev 1997, with the finite range `n ≤ 10²⁰` checked here). -/
theorem ternary_goldbach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hZ : ZinovievTheorem) : TernaryGoldbachStatement :=
  ternary_goldbach_of_large (hZ hGRH)

end Goldbach
