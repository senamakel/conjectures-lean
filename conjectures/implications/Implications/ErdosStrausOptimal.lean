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
  unfold IsRep
  have hp : familyPrime t + 1 = 4 * t ^ 2 + 2 * t := by
    unfold familyPrime
    have : t ^ 2 ≥ 1 := by positivity
    omega
  linear_combination (familyPrime t)^2 * t^2 * (t+1)^2 * hp

/-- In a Type II representation the non-multiple denominator is x, and the two
multiples are p*u and p*v, with u < v. -/
theorem typeII_sharp (t p x u v : ℕ)
    (ht : 0 < t) (hp : p = familyPrime t)
    (hpp : p.Prime) (hpx : ¬ p ∣ x)
    (hu : 0 < u) (huv : u < v)
    (heq : 4 * x * u * v = x * (u + v) + p * u * v) :
    p * (t + 1) ≤ p * v ∧
      (p * v = p * (t + 1) → u = t ∧ x = t * (t + 1)) := by
  have hpform : p + 1 = 4 * t ^ 2 + 2 * t := by
    unfold familyPrime at hp
    have : t ^ 2 ≥ 1 := by positivity
    omega
  have hv2 : 2 ≤ v := by omega
  have hraw : u + v < 4 * u * v := by
    have h₁ : u ≤ u * v := Nat.le_mul_of_pos_right _ (by omega)
    have h₂ : v ≤ u * v := Nat.le_mul_of_pos_left _ hu
    nlinarith
  let D := 4 * u * v - (u + v)
  have hDpos : 0 < D := Nat.sub_pos_of_lt hraw
  have hDnorm : D + (u + v) = 4 * u * v := Nat.sub_add_cancel hraw.le
  have hmul : x * D = p * u * v := by
    have hx := congrArg (x * ·) hDnorm
    nlinarith only [heq, hx]
  have hpdiv : p ∣ D := by
    have hpd : p ∣ x * D := by
      rw [hmul, mul_assoc]
      exact dvd_mul_right p (u * v)
    exact (hpp.dvd_mul.mp hpd).resolve_left hpx
  have hple : p ≤ D := Nat.le_of_dvd hDpos hpdiv
  have hv : t + 1 ≤ v := by
    by_contra! he
    have hvt : v ≤ t := by omega
    zify at hpform hDnorm hple huv hv2 hvt
    have h₁ : 0 ≤ ((v : ℤ) - 1 - u) * (4 * v - 1) :=
      mul_nonneg (by omega) (by omega)
    have h₂ : 0 ≤ ((t : ℤ) - v) * (t + v) :=
      mul_nonneg (by omega) (by positivity)
    nlinarith only [hpform, hDnorm, hple, hv2, hvt, h₁, h₂]
  refine ⟨Nat.mul_le_mul_left p hv, ?_⟩
  intro heqv
  have hvEq : v = t + 1 := (Nat.eq_of_mul_eq_mul_left hpp.pos heqv).symm
  subst v
  have huEq : u = t := by
    by_contra he
    have hut : u < t := by omega
    zify at hpform hDnorm hple hut hv2
    have h₁ : 0 ≤ ((t : ℤ) - 1 - u) * (4 * (t + 1) - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith only [hpform, hDnorm, hple, hut, hv2, h₁]
  subst u
  have hDp : D = p := by
    zify at hpform hDnorm ⊢
    nlinarith only [hpform, hDnorm]
  rw [hDp, mul_assoc, mul_comm x p] at hmul
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hpp.pos hmul⟩

end Implications.ErdosStrausOptimal
