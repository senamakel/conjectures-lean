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
    omega
  linear_combination (familyPrime t)^2 * t * (t+1) * hp

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
  have hvEq : v = t + 1 := Nat.eq_of_mul_eq_mul_left hpp.pos heqv
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

private theorem familyPrime_add_one (t : ℕ) (ht : 0 < t) :
    familyPrime t + 1 = 4 * t^2 + 2*t := by
  unfold familyPrime
  omega

private theorem familyPrime_gt (t : ℕ) (ht : 0 < t) : t + 1 < familyPrime t := by
  nlinarith [familyPrime_add_one t ht]

private theorem not_one_multiple (t p a b w : ℕ) (ht : 0 < t)
    (hp : p = familyPrime t) (hpp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (hw : 0 < w) (hsmall : w ≤ t + 1) (h : IsRep p a b (p * w)) : False := by
  unfold IsRep at h
  have h' : 4 * a * b * w = a*b + p*w*(a+b) := by
    apply Nat.eq_of_mul_eq_mul_left hpp.pos
    nlinarith only [h]
  have h'' : (4*w-1) * (a*b) = p*w*(a+b) := by
    have hnorm : 4*w-1+1 = 4*w := by omega
    have hmul := congrArg ((a*b) * ·) hnorm
    nlinarith only [h', hmul]
  have hd : p ∣ 4*w-1 := by
    have hmul : p ∣ (4*w-1)*(a*b) := by
      rw [h'', mul_assoc]
      exact dvd_mul_right _ _
    exact (hpp.dvd_mul.mp hmul).resolve_right (fun he =>
      (hpp.dvd_mul.mp he).elim ha hb)
  by_cases ht' : t = 1
  · subst t
    norm_num [familyPrime] at hp
    subst p
    interval_cases w <;> norm_num at hd
  · have hp' := familyPrime_add_one t ht
    rw [← hp] at hp'
    have htwo : 2 ≤ t := by omega
    have hdle := Nat.le_of_dvd (show 0 < 4*w-1 by omega) hd
    nlinarith [mul_nonneg (show 0 ≤ (t : ℤ) - 2 by omega) (show 0 ≤ (t : ℤ) by positivity)]

private theorem not_three_multiples (p a b c : ℕ) (hp : 0 < p) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (he : IsRep p (p*a) (p*b) (p*c)) : False := by
  unfold IsRep at he
  have he' : 4*a*b*c = a*b+a*c+b*c := by
    apply Nat.eq_of_mul_eq_mul_left (m := p^3) (by positivity)
    nlinarith only [he]
  have hab : a*b ≤ a*b*c := Nat.le_mul_of_pos_right _ hc
  have hac : a*c ≤ a*b*c := by
    rw [mul_right_comm]
    exact Nat.le_mul_of_pos_right _ hb
  have hbc : b*c ≤ a*b*c := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ ha
  have hpos : 0 < a*b*c := by positivity
  nlinarith only [he', hab, hac, hbc, hpos]

private theorem typeII_at_most (t p a u v : ℕ) (ht : 0 < t)
    (hp : p = familyPrime t) (hpp : p.Prime) (ha : ¬p ∣ a)
    (hu : 0 < u) (huv : u < v) (hv : p*v ≤ p*(t+1))
    (he : IsRep p a (p*u) (p*v)) :
    a = t*(t+1) ∧ u = t ∧ v = t+1 := by
  have he' : 4*a*u*v = a*(u+v)+p*u*v := by
    unfold IsRep at he
    apply Nat.eq_of_mul_eq_mul_left (m := p^2) (by positivity)
    nlinarith only [he]
  obtain ⟨hle, huniq⟩ := typeII_sharp t p a u v ht hp hpp ha hu huv he'
  have heq := Nat.le_antisymm hv hle
  exact ⟨(huniq heq).2, (huniq heq).1, Nat.eq_of_mul_eq_mul_left hpp.pos heq⟩

end Implications.ErdosStrausOptimal
