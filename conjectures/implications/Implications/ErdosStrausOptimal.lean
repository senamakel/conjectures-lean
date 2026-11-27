import Mathlib

/-!
# The sharp denominator in the Erdős–Straus quadratic family

For `p = 4 t^2 + 2 t - 1`, the displayed Type II solution has denominators
`t (t + 1)`, `p t`, and `p (t + 1)`.  This file records the exact algebraic
certificate and the sharpness/rigidity argument for Type II solutions.
-/

namespace Implications.ErdosStrausOptimal

/-- The denominator-cleared Erdős–Straus equation for numerator `p`. -/
def IsRep (p x y z : ℕ) : Prop :=
  4 * x * y * z = p * (x * y + x * z + y * z)

/-- The prime in the quadratic family. -/
def familyPrime (t : ℕ) : ℕ := 4 * t ^ 2 + 2 * t - 1

/-- The standard Type II family gives a representation. -/
theorem family_rep (t : ℕ) (ht : 0 < t) :
    IsRep (familyPrime t) (t * (t + 1)) (familyPrime t * t)
      (familyPrime t * (t + 1)) := by
  unfold IsRep familyPrime
  have ht' : 1 ≤ 4 * t ^ 2 + 2 * t := by omega
  rw [Nat.sub_add_cancel ht']
  ring

/-- In a Type II representation the non-multiple denominator is `x`, and the other
two denominators are `p*u` and `p*v`, with `u < v`. This lemma proves the exact
sharp lower bound and the equality case directly from the cleared equation. -/
theorem typeII_sharp (t p x u v : ℕ)
    (ht : 0 < t)
    (hp : p = familyPrime t)
    (hpp : p.Prime) (hpx : ¬ p ∣ x)
    (hu : 0 < u) (huv : u < v)
    (heq : 4 * x * u * v = x * (u + v) + p * u * v) :
    p * (t + 1) ≤ p * v ∧
      (p * v = p * (t + 1) → u = t ∧ x = t * (t + 1)) := by
  have hpform : p = 4 * t ^ 2 + 2 * t - 1 := by simpa [familyPrime] using hp
  have hv2 : 2 ≤ v := by omega
  have hraw : u + v ≤ 4 * u * v := by nlinarith
  have hDpos : 0 < 4 * u * v - u - v := by omega
  have hDnorm : 4 * u * v - u - v + u + v = 4 * u * v := by omega
  have hmul : x * (4 * u * v - u - v) = p * u * v := by
    nlinarith [heq, hDnorm]
  have hpdiv : p ∣ 4 * u * v - u - v := by
    have hpd : p ∣ x * (4 * u * v - u - v) := by rw [hmul]; exact dvd_mul_right p (u * v)
    rcases hpp.dvd_mul.mp hpd with hpx' | hD
    · exact (hpx hpx').elim
    · exact hD
  have hple : p ≤ 4 * u * v - u - v := Nat.le_of_dvd hDpos hpdiv
  have hbound : p ≤ 4 * v ^ 2 - 6 * v + 1 := by
    have huv' : u ≤ v - 1 := by omega
    calc
      p ≤ 4 * u * v - u - v := hple
      _ ≤ 4 * v ^ 2 - 6 * v + 1 := by nlinarith
  have hv : t + 1 ≤ v := by
    by_contra hn
    have hvsmall : v ≤ t := by omega
    have hpoly : 4 * v ^ 2 - 6 * v + 1 < 4 * t ^ 2 + 2 * t - 1 := by
      nlinarith [sq_nonneg ((t : ℤ) - v)]
    omega
  refine ⟨Nat.mul_le_mul_left p hv, ?_⟩
  intro heqv
  have hvEq : v = t + 1 := by
    exact Nat.eq_of_mul_eq_mul_left (by omega) heqv
  subst v
  have hDle' : 4 * u * (t + 1) - u - (t + 1) ≤ p := hDle
  have huEq : u = t := by
    rw [hpform] at hDle'
    have : u ≤ t := by omega
    omega
  subst u
  have hx : x = t * (t + 1) := by
    rw [hpform] at hmul
  have hp' : 4 * t ^ 2 + 2 * t - 1 = 4 * t * (t + 1) - t - (t + 1) := by omega
    rw [hp'] at hmul
    have hn : t + (t + 1) ≤ 4 * t * (t + 1) := by nlinarith
    have hDn : 4 * t * (t + 1) - t - (t + 1) + t + (t + 1) = 4 * t * (t + 1) := by omega
    nlinarith [hmul, hDn]
  exact ⟨huEq, hx⟩

end Implications.ErdosStrausOptimal
