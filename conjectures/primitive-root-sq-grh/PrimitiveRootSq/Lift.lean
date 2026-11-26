import Mathlib

/-!
# From a primitive root modulo `p` to a primitive root modulo every `p ^ k`

Classical (e.g. Ireland–Rosen, *A classical introduction to modern number theory*, §4.1):
for an odd prime `p`, if `q` is a primitive root modulo `p` and `q ^ (p - 1) ≢ 1 (mod p²)`,
then `q` is a primitive root modulo `p ^ k` for every `k ≥ 1`. Mathlib has the ingredient
`ZMod.orderOf_one_add_mul_prime` (the order of `1 + p a` modulo `p ^ (n + 1)` is `p ^ n` when
`p ∤ a`) but not this statement, so we prove it here.

Conversely (`pow_sub_one_eq_one_of_not_primitive_sq`), a primitive root modulo `p` that is not
a primitive root modulo `p²` satisfies `q ^ (p - 1) ≡ 1 (mod p²)`.
-/

namespace PrimitiveRootSq

/-- The order of `q` modulo `p ^ (n + 1)` is `p ^ n * (p - 1)` when `q` is a primitive root
modulo the odd prime `p` and `q ^ (p - 1) ≢ 1 (mod p²)`. -/
theorem orderOf_prime_pow_succ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ}
    (hq : orderOf (q : ZMod p) = p - 1) (hsq : (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) (n : ℕ) :
    orderOf (q : ZMod (p ^ (n + 1))) = p ^ n * (p - 1) := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  -- `q` is a unit modulo `p`
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h; rw [h, orderOf_eq_zero_iff'.mpr] at hq
    · omega
    · intro m hm h0; rw [zero_pow hm.ne'] at h0; exact zero_ne_one h0
  have hpq : ¬ p ∣ q := by rwa [Ne, ZMod.natCast_eq_zero_iff] at hq0
  -- Fermat: `q ^ (p - 1) = 1 + p * a` with `p ∤ a`
  have hferm : (q : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hq0
  have hq1 : 1 ≤ q ^ (p - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hpq))
  have hdvd : p ∣ q ^ (p - 1) - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1]; push_cast; rw [hferm, sub_self]
  obtain ⟨a, ha⟩ := hdvd
  have hqa : q ^ (p - 1) = 1 + p * a := by omega
  have hpa : ¬ (p : ℤ) ∣ (a : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    rintro ⟨b, rfl⟩
    apply hsq
    have : ((q ^ (p - 1) : ℕ) : ZMod (p ^ 2)) = 1 := by
      rw [hqa, show 1 + p * (p * b) = 1 + p ^ 2 * b by ring]
      push_cast
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
    simpa using this
  -- the order of `q ^ (p - 1)` modulo `p ^ (n + 1)`
  have hord1 : orderOf ((q : ZMod (p ^ (n + 1))) ^ (p - 1)) = p ^ n := by
    have e : ((q : ZMod (p ^ (n + 1))) ^ (p - 1)) = 1 + (p : ZMod (p ^ (n + 1))) * ((a : ℤ) : ZMod _) := by
      rw [← Nat.cast_pow, hqa]; push_cast; ring
    rw [e]
    exact ZMod.orderOf_one_add_mul_prime hp hp2 a hpa n
  -- `p - 1` divides the order modulo `p ^ (n + 1)`
  set m := orderOf (q : ZMod (p ^ (n + 1))) with hm
  have hdm : p - 1 ∣ m := by
    have hd : p ∣ p ^ (n + 1) := dvd_pow_self p (Nat.succ_ne_zero n)
    have := orderOf_map_dvd (ZMod.castHom hd (ZMod p)).toMonoidHom (q : ZMod (p ^ (n + 1)))
    simpa [hq] using this
  have hpos : p - 1 ≠ 0 := by omega
  rw [orderOf_pow' _ hpos, ← hm, Nat.gcd_eq_right hdm] at hord1
  rw [← hord1, Nat.div_mul_cancel hdm]

/-- A primitive root `q` modulo the odd prime `p` with `q ^ (p - 1) ≢ 1 (mod p²)` is a
primitive root modulo `p ^ k` for every `k ≥ 1`. -/
theorem orderOf_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ}
    (hq : orderOf (q : ZMod p) = p - 1) (hsq : (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) {k : ℕ}
    (hk : 1 ≤ k) : orderOf (q : ZMod (p ^ k)) = (p ^ k).totient := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [orderOf_prime_pow_succ hp hp2 hq hsq n, Nat.totient_prime_pow_succ hp]

/-- The case `k = 2`. -/
theorem orderOf_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ}
    (hq : orderOf (q : ZMod p) = p - 1) (hsq : (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) :
    orderOf (q : ZMod (p ^ 2)) = p * (p - 1) := by
  simpa using orderOf_prime_pow_succ hp hp2 hq hsq 1

/-- The converse direction used by the analytic argument. -/
theorem pow_sub_one_eq_one_of_not_primitive_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ}
    (hq : orderOf (q : ZMod p) = p - 1) (hnot : orderOf (q : ZMod (p ^ 2)) ≠ p * (p - 1)) :
    (q : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
  by_contra h
  exact hnot (orderOf_prime_sq hp hp2 hq h)

end PrimitiveRootSq
