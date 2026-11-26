import Weinberger.ClassNumber.Hypotheses
import Mathlib

/-!
# Small split primes rule out class number one

For `d = −n < 0`: if `ℚ(√d)` has class number one, a prime with an ideal of norm `p` is
`u² + uv + ((1+n)/4) v²` (`n ≡ 3 mod 4`) or `u² + n v²` (otherwise). Since
`4(u² + uv + c v²) = (2u + v)² + n v²`, a prime `p` with `4p < n` (resp. `p < n`) can only be
`u²`, which it is not.
-/

namespace Weinberger

open ClassNumberProblem

lemma not_prime_sq (u : ℤ) (p : ℕ) (hp : p.Prime) (h : u ^ 2 = (p : ℤ)) : False := by
  have h2 : u.natAbs * u.natAbs = p := by
    have := congrArg Int.natAbs h
    rwa [Int.natAbs_pow, sq, Int.natAbs_natCast] at this
  rw [← h2] at hp
  have h1 : u.natAbs ≠ 1 := fun h => by rw [h] at hp; norm_num at hp
  exact Nat.not_prime_mul h1 h1 hp

lemma one_le_sq_of_ne {v : ℤ} (hv : v ≠ 0) : 1 ≤ v ^ 2 := by
  have : 0 < v ^ 2 := lt_of_le_of_ne (sq_nonneg v) (Ne.symm (pow_ne_zero 2 hv))
  omega

theorem not_squarefree_of_four_dvd {n : ℕ} (h : n % 4 = 0) : ¬ Squarefree (-(n : ℤ)) := by
  intro hsf
  have h4 : (2 : ℤ) * 2 ∣ -(n : ℤ) := by
    rw [dvd_neg]; exact_mod_cast (show 2 * 2 ∣ n by omega)
  have := hsf 2 h4
  norm_num [Int.isUnit_iff] at this

/-- `p = 2` ramifies (or splits) when `n ≡ 1, 2 (mod 4)`, and is not a norm once `n ≥ 3`. -/
theorem false_of_two (hPS : ClassNumberOneNorms) {n : ℕ} (hn : 3 ≤ n) (h4 : n % 4 = 1 ∨ n % 4 = 2)
    (hsf : Squarefree (-(n : ℤ))) (hcn : IsClassNumberOne (-(n : ℤ))) : False := by
  have hd4 : (-(n : ℤ)) % 4 ≠ 1 := by omega
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (2 : ℤ) ∣ t ^ 2 - -(n : ℤ) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨0, ⟨k, by rw [hk]; push_cast; ring⟩⟩
    · exact ⟨1, ⟨k + 1, by rw [hk]; push_cast; ring⟩⟩
  obtain ⟨u, v, huv⟩ := (hPS _ hsf (by omega) hcn 2 Nat.prime_two t).2 hd4 (by simpa using ht)
  push_cast at huv
  have hv : v = 0 := by
    by_contra hv
    have := one_le_sq_of_ne hv
    have : (3 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [hv] at huv
  exact not_prime_sq u 2 Nat.prime_two (by push_cast; simpa using huv)

/-- A prime `p` with `4p < n` and an ideal of norm `p` rules out class number one,
for `n ≡ 3 (mod 4)`. -/
theorem false_of_split3 (hPS : ClassNumberOneNorms) {n : ℕ} (h4 : n % 4 = 3)
    (hsf : Squarefree (-(n : ℤ))) (hcn : IsClassNumberOne (-(n : ℤ))) {p : ℕ} (hp : p.Prime)
    (hpn : 4 * p < n) (t : ℕ) (ht : p ∣ t * t + t + (n + 1) / 4) : False := by
  have hd4 : (-(n : ℤ)) % 4 = 1 := by omega
  have hc : (1 - -(n : ℤ)) / 4 = (((n + 1) / 4 : ℕ) : ℤ) := by
    have : (n + 1) % 4 = 0 := by omega
    push_cast
    rw [show (1 - -(n : ℤ)) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
    exact_mod_cast rfl
  obtain ⟨u, v, huv⟩ := (hPS _ hsf (by omega) hcn p hp (t : ℤ)).1 hd4 (by
    rw [hc]
    have : ((p : ℕ) : ℤ) ∣ ((t * t + t + (n + 1) / 4 : ℕ) : ℤ) := by exact_mod_cast ht
    push_cast at this ⊢
    simpa [sq] using this)
  rw [hc] at huv
  have h4c : 4 * (((n + 1) / 4 : ℕ) : ℤ) = n + 1 := by
    have : 4 * ((n + 1) / 4) = n + 1 := by omega
    exact_mod_cast this
  have key : (2 * u + v) ^ 2 + (n : ℤ) * v ^ 2 = 4 * p := by
    linear_combination 4 * huv - v ^ 2 * h4c
  have hv : v = 0 := by
    by_contra hv
    have := one_le_sq_of_ne hv
    have : (4 * p : ℤ) < n := by exact_mod_cast hpn
    nlinarith [sq_nonneg (2 * u + v)]
  rw [hv] at huv
  exact not_prime_sq u p hp (by simpa using huv)

end Weinberger
