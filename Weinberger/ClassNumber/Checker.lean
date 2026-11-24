import Weinberger.ClassNumber.Elementary

/-!
# A computable checker for `h(ℚ(√−n)) ≠ 1`, with a soundness proof

`okB n` holds when `n = 0`, `4 ∣ n` (`−n` not squarefree), `n ≥ 3` with `n ≡ 1, 2 (mod 4)`
(the prime `2` has an ideal of norm `2`, which is not a norm), when `n ≡ 3 (mod 4)` and some
prime `p < 2000` with `4p < n` divides `t² + t + (n+1)/4` for some `t < p`, or when `n` is one
of the nine Heegner values. Given `ClassNumberOneNorms`, `okB_sound` shows that a squarefree
`−n` of class number one is one of the nine.
-/

namespace Weinberger.ClassNumber

open ClassNumberProblem

/-- Primes below 2000. -/
def smallPrimes : List ℕ := (List.range 2000).filter (fun q => Nat.Prime q)

theorem prime_of_mem_smallPrimes {q : ℕ} (h : q ∈ smallPrimes) : q.Prime := by
  simp only [smallPrimes, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

/-- Is there `t < k` with `p ∣ t² + t + c`? -/
def anyT (c p : ℕ) : ℕ → Bool
  | 0 => false
  | t + 1 => (t * t + t + c) % p == 0 || anyT c p t

theorem anyT_sound {c p : ℕ} : ∀ k, anyT c p k = true → ∃ t, p ∣ t * t + t + c
  | 0, h => by simp [anyT] at h
  | k + 1, h => by
    simp only [anyT, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨k, Nat.dvd_of_mod_eq_zero h⟩
    · exact anyT_sound k h

/-- A small prime `p` with `4p < n` and an ideal of norm `p` in `ℚ(√−n)`, `n ≡ 3 (mod 4)`. -/
def witness3 (n : ℕ) : Bool :=
  smallPrimes.any fun p => decide (4 * p < n) && anyT ((n + 1) / 4) p p

/-- The nine Heegner values of `−d`. -/
def heegnerNat : List ℕ := [1, 2, 3, 7, 11, 19, 43, 67, 163]

/-- Per-`n` check. -/
def okB (n : ℕ) : Bool :=
  n == 0 || n % 4 == 0 || (decide (3 ≤ n) && (n % 4 == 1 || n % 4 == 2))
    || (n % 4 == 3 && witness3 n) || heegnerNat.contains n

theorem okB_sound (hPS : ClassNumberOneNorms) {n : ℕ} (h : okB n = true) (hn : n ≠ 0)
    (hsf : Squarefree (-(n : ℤ))) (hcn : IsClassNumberOne (-(n : ℤ))) : n ∈ heegnerNat := by
  simp only [okB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem] at h
  rcases h with (((h | h) | ⟨h3, h4⟩) | ⟨h4, hw⟩) | h
  · exact absurd h hn
  · exact absurd hsf (not_squarefree_of_four_dvd h)
  · exact (false_of_two hPS h3 h4 hsf hcn).elim
  · simp only [witness3, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨p, hp, hpn, ht⟩ := hw
    obtain ⟨t, ht⟩ := anyT_sound _ ht
    exact (false_of_split3 hPS h4 hsf hcn (prime_of_mem_smallPrimes hp) hpn t ht).elim
  · exact h

/-- `checkFromB lo k` checks `okB n` for all `n ∈ [lo, lo + k)`. -/
def checkFromB : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, k + 1 => okB lo && checkFromB (lo + 1) k

theorem checkFromB_sound : ∀ (k lo : ℕ), checkFromB lo k = true →
    ∀ n, lo ≤ n → n < lo + k → okB n = true
  | 0, lo, _, n, h1, h2 => by omega
  | k + 1, lo, h, n, h1, h2 => by
    simp only [checkFromB, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact checkFromB_sound k (lo + 1) h.2 n h1 (by omega)

theorem checkFromB_add : ∀ (a lo b : ℕ),
    checkFromB lo (a + b) = (checkFromB lo a && checkFromB (lo + a) b)
  | 0, lo, b => by simp [checkFromB]
  | a + 1, lo, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega, checkFromB, checkFromB, checkFromB_add a (lo + 1) b,
      Bool.and_assoc, show lo + 1 + a = lo + (a + 1) by omega]

theorem checkFromB_chunks (c : ℕ) :
    ∀ j, (∀ i < j, checkFromB (i * c) c = true) → checkFromB 0 (j * c) = true
  | 0, _ => by simp [checkFromB]
  | j + 1, h => by
    rw [Nat.succ_mul, checkFromB_add, checkFromB_chunks c j (fun i hi => h i (by omega)),
      Nat.zero_add, h j (by omega), Bool.and_self]

end Weinberger.ClassNumber
