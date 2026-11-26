import Erdos985.Compute.Checker
import SunA243164.Assembly

/-!
# A counting checker for the finite range, with a soundness proof

The finite range needs the index `n = π(P)` of each prime `P`, so the checker walks through
`[lo, lo + k)` carrying the number `c` of primes below the current point. Primality is decided
exactly (`isPrimeB`): a base-2 Fermat test discards most composites cheaply and `Nat.minFac`
settles the rest. For each prime `P` of index `n > 6` it looks for a small prime `q < n` with
`(q n)^((P-1)/r) ≢ 1 (mod P)` for every prime `r ∣ P - 1`, which makes `q n` a primitive root
(`orderOf_eq_of_pow_and_pow_div_prime`).

`countFrom_sound` is the soundness theorem: if `countFrom lo k c = some c'` and `c` is the number
of primes below `lo`, then `c'` is the number of primes below `lo + k` and every prime in
`[lo, lo + k)` of index `> 6` is a `GoodPrime`. The arithmetic (`powMod`, `smallPrimes`) is
erdos-985's.
-/

namespace SunA243164.Compute

open Erdos985.Compute

/-- Exact primality test. -/
def isPrimeB (m : ℕ) : Bool :=
  decide (2 ≤ m) && (m == 2 || (m % 2 == 1 && powMod 2 (m - 1) m == 1 && m.minFac == m))

theorem isPrimeB_iff (m : ℕ) : isPrimeB m = true ↔ m.Prime := by
  constructor
  · intro h
    simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨h2, h | ⟨⟨-, -⟩, h⟩⟩ := h
    · subst h; exact Nat.prime_two
    · exact Nat.prime_def_minFac.mpr ⟨h2, h⟩
  · intro hp
    simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    refine ⟨hp.two_le, ?_⟩
    by_cases h2 : m = 2
    · exact Or.inl h2
    right
    have hodd : m % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    have hm3 : 3 ≤ m := by have := hp.two_le; omega
    refine ⟨⟨hodd, ?_⟩, (Nat.prime_def_minFac.mp hp).2⟩
    have : Fact m.Prime := ⟨hp⟩
    rw [← zmod_pow_eq_one_iff (by omega)]
    apply ZMod.pow_card_sub_one_eq_one
    intro h0
    have h0' : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    have := Nat.le_of_dvd (by norm_num) h0'
    omega

/-- A small prime `q < n` with `q n` a primitive root modulo the prime `P`. -/
def goodB (P n : ℕ) : Bool :=
  let fs := (P - 1).primeFactorsList.dedup
  smallPrimes.any fun q =>
    decide (q < n) && (q * n) % P != 0 && fs.all fun r => powMod (q * n) ((P - 1) / r) P != 1

theorem goodB_sound {P n : ℕ} (h : goodB P n = true) (hP : P.Prime) :
    ∃ q, q.Prime ∧ q < n ∧ orderOf ((q * n : ℕ) : ZMod P) = P - 1 := by
  have : Fact P.Prime := ⟨hP⟩
  have hP2 : 2 ≤ P := hP.two_le
  simp only [goodB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨q, hq, ⟨hqn, h0⟩, hfs⟩ := h
  refine ⟨q, prime_of_mem_smallPrimes hq, hqn, ?_⟩
  apply orderOf_eq_of_pow_and_pow_div_prime
  · have : 0 < P := by omega
    · apply ZMod.pow_card_sub_one_eq_one
      intro hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      exact h0 (Nat.eq_zero_of_dvd_of_lt hz (Nat.mod_lt _ this) |>.symm ▸
        (Nat.mod_eq_zero_of_dvd hz))
  · intro r hr hrd
    rw [ne_eq, zmod_pow_eq_one_iff hP2]
    apply hfs r
    rw [List.mem_dedup, Nat.mem_primeFactorsList (by omega)]
    exact ⟨hr, hrd⟩

/-- Walk through `[lo, lo + k)` carrying the prime count `c`; `none` on a failure. -/
def countFrom : ℕ → ℕ → ℕ → Option ℕ
  | _, 0, c => some c
  | lo, k + 1, c =>
    if isPrimeB lo then
      if decide (c + 1 ≤ 6) || goodB lo (c + 1) then countFrom (lo + 1) k (c + 1) else none
    else countFrom (lo + 1) k c

lemma primeCounting_of_prime {P : ℕ} (hP : P.Prime) :
    Nat.primeCounting P = Nat.count Nat.Prime P + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]; simp [hP]

theorem countFrom_sound : ∀ (k lo c c' : ℕ), countFrom lo k c = some c' →
    c = Nat.count Nat.Prime lo →
    c' = Nat.count Nat.Prime (lo + k) ∧
      ∀ P, lo ≤ P → P < lo + k → P.Prime → 6 < Nat.primeCounting P → GoodPrime P
  | 0, lo, c, c', h, hc => by
    simp only [countFrom, Option.some.injEq] at h
    exact ⟨by rw [← h, hc]; rfl, fun P h1 h2 => by omega⟩
  | k + 1, lo, c, c', h, hc => by
    simp only [countFrom] at h
    by_cases hp : isPrimeB lo = true
    · rw [if_pos hp] at h
      have hlo : lo.Prime := (isPrimeB_iff lo).mp hp
      split_ifs at h with hg
      have hc1 : c + 1 = Nat.count Nat.Prime (lo + 1) := by
        rw [Nat.count_succ, ← hc]; simp [hlo]
      obtain ⟨ih1, ih2⟩ := countFrom_sound k (lo + 1) (c + 1) c' h hc1
      refine ⟨by rw [ih1]; ring_nf, fun P h1 h2 hP h6 => ?_⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · have hπ : Nat.primeCounting P = c + 1 := by rw [primeCounting_of_prime hP, hc]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
        rcases hg with hg | hg
        · omega
        · obtain ⟨q, hq, hqn, hord⟩ := goodB_sound hg hP
          exact ⟨q, hq, hπ ▸ hqn, hπ ▸ hord⟩
      · exact ih2 P h1 (by omega) hP h6
    · rw [if_neg hp] at h
      have hlo : ¬ lo.Prime := fun h' => hp ((isPrimeB_iff lo).mpr h')
      have hc1 : c = Nat.count Nat.Prime (lo + 1) := by
        rw [Nat.count_succ, ← hc]; simp [hlo]
      obtain ⟨ih1, ih2⟩ := countFrom_sound k (lo + 1) c c' h hc1
      refine ⟨by rw [ih1]; ring_nf, fun P h1 h2 hP h6 => ?_⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact absurd hP hlo
      · exact ih2 P h1 (by omega) hP h6

end SunA243164.Compute
