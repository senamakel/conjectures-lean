import Mathlib

/-!
# Finiteness at a fixed crystal cross multiplier

Elimination produces an integer polynomial whose reduction modulo the
multiplier is monic. Its finite root set contains every allowed first
component for fixed quotients. The order constraints bound both quotients.
-/

open Polynomial

namespace CrystalFixedMultiplier

/-- For a fixed multiplier and fixed quotients, there are finitely many smaller components
that can satisfy the two crystal equations. -/
theorem finite_first_component {m : ℕ} (hm : 2 ≤ m) (p q : ℤ) :
    Set.Finite {a : ℤ | ∃ c : ℤ,
      (a + (m : ℤ) * c)^2 = p * ((a + 1) * (m * c + 1)) ∧
      (c + (m : ℤ) * a)^2 = q * ((c + 1) * (m * a + 1))} := by
  let L : ℤ[X] := C ((m : ℤ)^3*q - 2*m^3 - m*p + 2*m)*X + C ((m : ℤ)^2*q - m*p)
  let M : ℤ[X] := C (1 - (m : ℤ)^4)*X^2 + C ((m : ℤ)^3*q-p)*X + C ((m : ℤ)^2*q-p)
  let B : ℤ[X] := C (2*(m : ℤ)-(m : ℤ)*q)*X - C q
  let D : ℤ[X] := C ((m : ℤ)^2)*X^2 - C ((m : ℤ)*q)*X - C q
  let P : ℤ[X] := M^2 - B*M*L + D*L^2
  have hP : P ≠ 0 := by
    let : Fact (1 < m) := ⟨by omega⟩
    let f : ℤ →+* ZMod m := Int.castRingHom _
    have he : P.map f = (X^2 - C (f p) * (X+1))^2 := by
      simp [P,L,M,B,D, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow]
      ring
    have hm2 : (X^2 - C (f p) * (X+1) : (ZMod m)[X]).Monic := by
      rw [sub_eq_add_neg]
      apply monic_X_pow_add
      apply lt_of_le_of_lt (degree_le_of_natDegree_le (n := 1) ?_) (by norm_num)
      rw [natDegree_neg]
      have hdeg : (X + (1 : (ZMod m)[X])).natDegree = 1 := by
        simpa using natDegree_X_add_C (1 : ZMod m)
      exact (natDegree_C_mul_le _ _).trans hdeg.le
    intro h
    rw [h, Polynomial.map_zero] at he
    exact (hm2.pow 2).ne_zero he.symm
  apply (finite_setOfPred_isRoot hP).subset
  intro a ha
  obtain ⟨c, hf, hg⟩ := ha
  change P.eval a = 0
  have hb : c^2 + B.eval a*c + D.eval a = 0 := by
    simp [B,D]
    linear_combination hg
  have hl : L.eval a*c + M.eval a = 0 := by
    simp [L,M]
    linear_combination hf - (m : ℤ)^2 * hg
  have hm' : M.eval a = -(L.eval a*c) := by linarith
  simp [P,hm']
  linear_combination (L.eval a)^2 * hb

private theorem quotient_bound {m p : ℕ} {a c : ℤ} (hm : 2 ≤ m)
    (ha : 0 < a) (hc : 0 < c) (hs : a ≤ m*c) (ht : c ≤ m*a)
    (he : (a + (m : ℤ)*c)^2 = p*((a+1)*(m*c+1))) : p < m^2 + 3 := by
  have hm' : 0 < (m : ℤ) := by exact_mod_cast (show 0 < m by omega)
  have h1 := mul_le_mul_of_nonneg_left hs ha.le
  have h2 := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ (m : ℤ)^2*c by positivity)
  have h3 : (a + (m : ℤ)*c)^2 ≤ ((m : ℤ)^2 + 3)*((m : ℤ)*a*c) := by
    nlinarith only [h1, h2]
  have h4 : (m : ℤ)*a*c < (a+1)*(m*c+1) := by nlinarith [mul_pos hm' hc]
  have h5 := h3.trans_lt (mul_lt_mul_of_pos_left h4 (show 0 < (m : ℤ)^2+3 by positivity))
  rw [he] at h5
  exact_mod_cast (lt_of_mul_lt_mul_right h5 (by positivity) : (p : ℤ) < (m : ℤ)^2+3)

/-- For fixed cross multiplier, the ordered crystal equations have finitely many
possible first components even when both integer quotients are allowed to vary. -/
theorem finite_ordered_first_component {m : ℕ} (hm : 2 ≤ m) :
    Set.Finite {a : ℤ | ∃ (c : ℤ) (p q : ℕ),
      0 < a ∧ 0 < c ∧ a ≤ m*c ∧ c ≤ m*a ∧
      (a + (m : ℤ)*c)^2 = p*((a+1)*(m*c+1)) ∧
      (c + (m : ℤ)*a)^2 = q*((c+1)*(m*a+1))} := by
  let T (p q : Fin (m^2+3)) : Set ℤ := {a : ℤ | ∃ c : ℤ,
    (a + (m : ℤ)*c)^2 = (p.val : ℤ)*((a+1)*(m*c+1)) ∧
    (c + (m : ℤ)*a)^2 = (q.val : ℤ)*((c+1)*(m*a+1))}
  have hf : (⋃ p, ⋃ q, T p q).Finite :=
    Set.finite_iUnion (fun p => Set.finite_iUnion (fun q =>
      finite_first_component hm (p.val : ℤ) (q.val : ℤ)))
  apply hf.subset
  rintro a ⟨c,p,q,ha,hc,hs,ht,hp,hq⟩
  exact Set.mem_iUnion.mpr ⟨⟨p, quotient_bound hm ha hc hs ht hp⟩,
    Set.mem_iUnion.mpr ⟨⟨q, quotient_bound hm hc ha ht hs hq⟩, c,hp,hq⟩⟩

#print axioms finite_ordered_first_component

end CrystalFixedMultiplier
