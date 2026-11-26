import Mathlib

/-!
# The quadratic character of `ℚ(√−n)` as a Dirichlet character mod `4n`

`kroneckerChar n` is the Dirichlet character mod `4n` with `χ(m) = J(−n | m)` on `m` coprime to
`4n`. It is well defined because the Jacobi symbol `J(−n | ·)` depends on odd `m` only through
`m mod 4n` (`jacobiSym.mod_right`). At an odd prime `p ∤ n` it is the Legendre symbol `(−n / p)`.
-/

namespace Weinberger

open scoped NumberTheorySymbols

variable (n : ℕ)

lemma odd_of_coprime_four_mul {b : ℕ} (h : Nat.Coprime b (4 * n)) : Odd b := by
  rw [Nat.odd_iff]
  by_contra h2
  have : 2 ∣ Nat.gcd b (4 * n) := Nat.dvd_gcd (by omega) (Dvd.intro (2 * n) (by ring))
  rw [h] at this
  omega

lemma gcd_neg_eq_one_of_coprime {b : ℕ} (h : Nat.Coprime b (4 * n)) :
    (-(n : ℤ)).gcd b = 1 := by
  rw [Int.neg_gcd, Int.gcd_natCast_natCast]
  exact (Nat.Coprime.coprime_dvd_right (Dvd.intro_left 4 rfl) h).symm

lemma jacobi_isUnit (u : (ZMod (4 * n))ˣ) :
    IsUnit (J(-(n : ℤ) | (u : ZMod (4 * n)).val)) :=
  Int.isUnit_iff.mpr (jacobiSym.eq_one_or_neg_one
    (gcd_neg_eq_one_of_coprime n (ZMod.val_coe_unit_coprime u)))

variable [NeZero n]

/-- `u ↦ J(−n | u)` as a homomorphism on units mod `4n`. -/
noncomputable def jacobiHom : (ZMod (4 * n))ˣ →* ℤˣ where
  toFun u := (jacobi_isUnit n u).unit
  map_one' := by
    ext
    have h1 : (1 : ZMod (4 * n)).val = 1 := ZMod.val_one'' (by have := NeZero.ne n; omega)
    simp [h1, jacobiSym.one_right]
  map_mul' u v := by
    ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    have hu := ZMod.val_coe_unit_coprime u
    have hv := ZMod.val_coe_unit_coprime v
    have hou := odd_of_coprime_four_mul n hu
    have hov := odd_of_coprime_four_mul n hv
    rw [ZMod.val_mul]
    have hmod := jacobiSym.mod_right (-(n : ℤ)) (hou.mul hov)
    rw [show (-(n : ℤ)).natAbs = n by simp] at hmod
    rw [← hmod, jacobiSym.mul_right' _ hou.pos.ne' hov.pos.ne']

/-- The Dirichlet character `χ_{−4n}` mod `4n`. -/
noncomputable def kroneckerChar : DirichletCharacter ℂ (4 * n) :=
  MulChar.ofUnitHom ((Units.map (Int.castRingHom ℂ).toMonoidHom).comp (jacobiHom n))

/-- At an odd prime `p ∤ n`, `kroneckerChar n p` is the Legendre symbol `(−n / p)`. -/
theorem kroneckerChar_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    kroneckerChar n p = (legendreSym p (-(n : ℤ)) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p (4 * n) := by
    refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  set u := ZMod.unitOfCoprime p hcop
  have hu : (u : ZMod (4 * n)) = (p : ZMod (4 * n)) := rfl
  rw [← hu, kroneckerChar, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, jacobiHom,
    MonoidHom.coe_mk, OneHom.coe_mk, IsUnit.unit_spec]
  rw [hu, ZMod.val_natCast, jacobiSym.legendreSym.to_jacobiSym]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hmod := jacobiSym.mod_right (-(n : ℤ)) hodd
  rw [show (-(n : ℤ)).natAbs = n by simp] at hmod
  rw [← hmod]
  rfl

end Weinberger
