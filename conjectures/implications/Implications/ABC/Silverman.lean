import Implications.ABC.Erdos936
import Implications.ABC.Variants
import Implications.Wieferich.Rotkiewicz

/-!
# abc implies infinitely many non-Wieferich primes (Silverman 1988)

Target: `{p : ℕ | p.Prime ∧ ¬ IsWieferichPrime p}.Infinite`, the conclusion of
formal-conjectures `Mersenne.rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne`
(`FormalConjectures/Wikipedia/Mersenne.lean`, commit `9097e2f`), with `IsWieferichPrime` copied
verbatim from `FormalConjecturesForMathlib/NumberTheory/WieferichPrime.lean` (the copies live in
`Implications.Wieferich.Rotkiewicz`). formal-conjectures has no standalone statement of it.

Deduction (Silverman, *J. Number Theory* 30 (1988) 226–237, unverified; this is the usual
elementary form of his argument). Suppose the non-Wieferich primes form a finite set `T`, with
product `Q`. Let `m = 2^n − 1`. A Wieferich prime dividing `m` divides it at least twice
(`sq_dvd_two_pow_sub_one_of_isWieferichPrime`), so every prime dividing `m` exactly once lies in
`T`. Splitting the prime factors of `m` by whether `p² ∣ m` gives `rad(m)² ≤ Q² m`
(`radical_sq_le_of_sq_dvd`). For the triple `(1, m, 2^n)`, `rad(abc) = 2 rad(m) =: X` and
`X⁶ ≤ 64 Q⁶ m³ < (m + 1)⁴ = c⁴` once `m > 64 Q⁶`. So every large `n` gives an exceptional triple
at `ε = 1/2`, against abc.
-/

namespace Implications.Abc

open _root_.ABC Implications.Wieferich Nat

/-- If every prime dividing `m` exactly once lies in a finite set `T` of primes, then
`rad(m)² ≤ (∏ T)² · m`. -/
lemma radical_sq_le_of_sq_dvd {m : ℕ} (hm : m ≠ 0) (T : Finset ℕ) (hTp : ∀ p ∈ T, p.Prime)
    (hT : ∀ p ∈ m.primeFactors, ¬ p ^ 2 ∣ m → p ∈ T) :
    radical m ^ 2 ≤ (∏ p ∈ T, p) ^ 2 * m := by
  unfold radical
  rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p ^ 2 ∣ m)]
  have hA : (∏ p ∈ m.primeFactors.filter (fun p => p ^ 2 ∣ m), id p) ^ 2 ≤ m := by
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
    rw [← Finset.prod_pow]
    calc ∏ p ∈ m.primeFactors.filter (fun p => p ^ 2 ∣ m), id p ^ 2
        ∣ ∏ p ∈ m.primeFactors.filter (fun p => p ^ 2 ∣ m), p ^ m.factorization p :=
          Finset.prod_dvd_prod_of_dvd _ _ fun p hp => by
            have h := Finset.mem_filter.1 hp
            exact pow_dvd_pow _
              (((Nat.prime_of_mem_primeFactors h.1).pow_dvd_iff_le_factorization hm).1 h.2)
      _ ∣ ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      _ = m := (Nat.prod_primeFactors_pow_factorization hm).symm
  have hB : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ^ 2 ∣ m), id p ≤ ∏ p ∈ T, p := by
    refine Finset.prod_le_prod_of_subset_of_one_le' (fun p hp => ?_)
      (fun p hp _ => (hTp p hp).one_le)
    have h := Finset.mem_filter.1 hp
    exact hT p h.1 h.2
  calc ((∏ p ∈ m.primeFactors.filter (fun p => p ^ 2 ∣ m), id p) *
        ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ^ 2 ∣ m), id p) ^ 2
      = (∏ p ∈ m.primeFactors.filter (fun p => p ^ 2 ∣ m), id p) ^ 2 *
        (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ^ 2 ∣ m), id p) ^ 2 := mul_pow _ _ _
    _ ≤ m * (∏ p ∈ T, p) ^ 2 := Nat.mul_le_mul hA (Nat.pow_le_pow_left hB 2)
    _ = (∏ p ∈ T, p) ^ 2 * m := mul_comm _ _

/-- Arithmetic core: `rad(m)² ≤ Q² m` and `64 Q⁶ < m` give `(2 rad m)³ < (m + 1)²`. -/
lemma two_mul_radical_cube_lt {r Q m : ℕ} (hr : r ^ 2 ≤ Q ^ 2 * m) (hm : 64 * Q ^ 6 < m) :
    (2 * r) ^ 3 < (m + 1) ^ 2 := by
  have h6 : ((2 * r) ^ 3) ^ 2 < ((m + 1) ^ 2) ^ 2 := by
    have e1 : ((2 * r) ^ 3) ^ 2 = 64 * (r ^ 2) ^ 3 := by ring
    rw [e1]
    have hm3 : 0 < m ^ 3 := by positivity
    calc 64 * (r ^ 2) ^ 3 ≤ 64 * (Q ^ 2 * m) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 3)
      _ = (64 * Q ^ 6) * m ^ 3 := by ring
      _ < m * m ^ 3 := Nat.mul_lt_mul_of_pos_right hm hm3
      _ = m ^ 4 := by ring
      _ ≤ (m + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ m) 4
      _ = ((m + 1) ^ 2) ^ 2 := by ring
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h6

/-- **Silverman (1988).** abc implies there are infinitely many non-Wieferich primes. -/
theorem infinite_non_wieferich_of_abc (habc : ABCConjecture) :
    {p : ℕ | p.Prime ∧ ¬ IsWieferichPrime p}.Infinite := by
  intro hfin
  set T := hfin.toFinset
  set Q := ∏ p ∈ T, p
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => ((Set.Finite.mem_toFinset hfin).1 hp).1
  have hev := eventually_of_abcSet_finite (abcSet_finite habc (by norm_num : (0 : ℝ) < 1 / 2))
    (fun _ => True) (fun n => (1, 2 ^ n - 1, 2 ^ n)) (64 * Q ^ 6 + 2) (fun n hn _ => ?_)
    (fun n => Nat.lt_two_pow_self.le)
  · obtain ⟨n, hn⟩ := hev.exists
    exact hn trivial
  -- the triple `(1, 2^n - 1, 2^n)` is exceptional
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hpos : 0 < 2 ^ n := by positivity
  have hn0 : n ≠ 0 := by omega
  set m := 2 ^ n - 1 with hm_def
  have hm0 : m ≠ 0 := by omega
  have hmQ : 64 * Q ^ 6 < m := by omega
  have hrad : radical m ^ 2 ≤ Q ^ 2 * m := by
    refine radical_sq_le_of_sq_dvd hm0 T hTp fun p hp hnsq => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine (Set.Finite.mem_toFinset hfin).2 ⟨hpp, fun hW => hnsq ?_⟩
    exact sq_dvd_two_pow_sub_one_of_isWieferichPrime hW (Nat.dvd_of_mem_primeFactors hp)
  have hc : 2 ^ n = m + 1 := by omega
  refine mem_abcSet_of_le Nat.one_pos (by omega) (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) (coprime_pred_self hpos) (by omega)
    (X := 2 * radical m) ?_ (by rw [hc]; exact two_mul_radical_cube_lt hrad hmQ)
  rw [one_mul, radical_mul (coprime_pred_self hpos), radical_prime_pow Nat.prime_two hn0,
    mul_comm]

end Implications.Abc
