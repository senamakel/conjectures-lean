import Weinberger.Statement
import Mathlib

/-!
# The elementary reduction

`n = ab + bc + ca` is the same as `n + a² = (a + b)(a + c)`. So a factorisation
`n + a² = u · v` with `2a < u < v` gives a representation with `0 < a < b = u − a < c = v − a`.
For an odd prime `p ∤ n` with `p² < n` and `−n` a square mod `p`, the root `a ∈ [1, (p−1)/2]`
of `a² ≡ −n` gives such a factorisation with `u = p`. Hence an idoneal `n` has `(−n / p) = −1`
for every odd prime `p ∤ n` with `p² < n`.
-/

namespace Weinberger

open Idoneal

/-- A factorisation `n + a² = u · v` with `0 < a`, `2a < u`, `u² < n + a²` makes `n` non-idoneal. -/
theorem not_isIdoneal_of_witness {n a u : ℕ} (ha : 0 < a) (hau : 2 * a < u)
    (hdvd : u ∣ n + a * a) (hlt : u * u < n + a * a) : ¬ IsIdoneal n := by
  rintro ⟨-, hno⟩
  obtain ⟨v, hv⟩ := hdvd
  have huv : u < v := by
    by_contra h
    replace h := not_lt.mp h
    have : u * v ≤ u * u := Nat.mul_le_mul_left u h
    omega
  obtain ⟨b, rfl⟩ : ∃ b, u = a + b := ⟨u - a, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, v = a + c := ⟨v - a, by omega⟩
  refine hno ⟨a, b, c, ha, by omega, by omega, ?_⟩
  have : n + a * a = a * a + (a * b + b * c + a * c) := by rw [hv]; ring
  omega

/-- For an idoneal `n` and an odd prime `p ∤ n` with `p² < n`, `−n` is not a square mod `p`. -/
theorem not_isSquare_of_isIdoneal {n p : ℕ} (hn : IsIdoneal n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hpp : p * p < n) : ¬ IsSquare (-(n : ZMod p)) := by
  have := Fact.mk hp
  rintro ⟨r, hr⟩
  -- pick the representative `a ∈ [0, p/2]` of `±r`
  set a : ℕ := (r : ZMod p).valMinAbs.natAbs with ha_def
  have hsq : ((a : ℤ) : ZMod p) ^ 2 = r ^ 2 := by
    have : ((a : ℤ)) = |r.valMinAbs| := by simp [ha_def]
    rw [this]
    rcases abs_choice r.valMinAbs with h | h <;> rw [h] <;> simp [ZMod.coe_valMinAbs]
  have hale : 2 * a ≤ p := by
    have := ZMod.natAbs_valMinAbs_le r
    omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hdvd : p ∣ n + a * a := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have h1 : ((a : ℤ) : ZMod p) = (a : ZMod p) := by simp
    rw [h1] at hsq
    rw [show (a : ZMod p) * a = (a : ZMod p) ^ 2 by ring, hsq, sq, ← hr]
    ring
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      rw [h] at hdvd
      simp at hdvd
      exact hpn hdvd
    · exact h
  exact not_isIdoneal_of_witness ha0 (by omega) hdvd (by nlinarith) hn

end Weinberger
