import Mathlib

/-!
# The Kronecker symbol `χ_{−q}` for even fundamental discriminants `−q`

For `4 ∣ q`, `n ↦ J(−q | n)` (Jacobi symbol, `n` odd; `0` for `n` even) is periodic mod `q`
(`jacobiSym_neg_mod`, from `jacobiSym.mod_right` and `J(4 | n) = 1`), so it is a Dirichlet
character mod `q`: `kroneckerChar q h4`. It is the Kronecker symbol `χ_{−q}`: its value at odd
`n` is `J(−q | n)` (`kroneckerChar_natCast_of_odd`), the condition in `LLS.ClassNumberFormula`.

`kroneckerChar_isPrimitive`: when `q = 4m` with `m` squarefree and `m ≡ 1, 2 (mod 4)` (that is,
`−q` is a fundamental discriminant) the character is primitive. The criterion
`isPrimitive_of_witness`: a character mod `q` is primitive if for every prime `p ∣ q` some
`n ≡ 1 (mod q/p)` has `χ(n) = −1`. The witnesses:
* `p = 2`: `n = 1 + 2m`. For `m ≡ 1 (mod 4)`, `J(−m | n) = χ₄(n) J(n | m) = −1`; for
  `m = 2m'`, `J(−2m' | n) = χ₈'(n) J(n | m') = −1` (`n ≡ 5 (mod 8)`).
* `p` odd: `n ≡ 1 (mod 4q/p)` a non-residue mod `p` (Chinese remainder theorem; `p ∤ q/p`
  since `m` is squarefree), so `J(−q | n) = J(−q/p | n) J(p | n) = 1 · J(n | p) = −1`.
-/

namespace LLS

open scoped NumberTheorySymbols

lemma jacobiSym_neg_four_mul (m : ℕ) {n : ℕ} (hn : Odd n) :
    J(-((4 * m : ℕ) : ℤ) | n) = J(-(m : ℤ) | n) := by
  rw [show -((4 * m : ℕ) : ℤ) = 4 * (-(m : ℤ)) by push_cast; ring, jacobiSym.mul_left,
    jacobiSym.at_four hn, one_mul]

/-- For `4 ∣ q` and odd `n`, `J(−q | n)` depends only on `n mod q`. -/
lemma jacobiSym_neg_mod {q : ℕ} (h4 : 4 ∣ q) {n : ℕ} (hn : Odd n) :
    J(-(q : ℤ) | n) = J(-(q : ℤ) | n % q) := by
  obtain ⟨m, rfl⟩ := h4
  have hn' : Odd (n % (4 * m)) := by
    rw [Nat.odd_iff] at hn ⊢
    rw [Nat.mod_mod_of_dvd _ (Dvd.dvd.mul_right (by norm_num : 2 ∣ 4) m)]
    exact hn
  rw [jacobiSym_neg_four_mul m hn, jacobiSym_neg_four_mul m hn', jacobiSym.mod_right _ hn,
    jacobiSym.mod_right _ hn']
  simp

lemma odd_mod_iff {q : ℕ} (h2 : 2 ∣ q) (n : ℕ) : Odd (n % q) ↔ Odd n := by
  rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd _ h2]

/-- The Kronecker symbol `χ_{−q}` as a Dirichlet character mod `q`, for `4 ∣ q`. -/
noncomputable def kroneckerChar (q : ℕ) [NeZero q] (h4 : 4 ∣ q) : DirichletCharacter ℂ q where
  toFun x := if Odd x.val then ((J(-(q : ℤ) | x.val) : ℤ) : ℂ) else 0
  map_one' := by
    have hq : 1 < q := by
      obtain ⟨m, hm⟩ := h4
      have := NeZero.ne q
      omega
    have : (1 : ZMod q).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hq]
    simp [this, jacobiSym.one_right]
  map_mul' x y := by
    have h2 : 2 ∣ q := (by norm_num : 2 ∣ 4).trans h4
    show (if Odd (x * y).val then ((J(-(q : ℤ) | (x * y).val) : ℤ) : ℂ) else 0)
      = (if Odd x.val then ((J(-(q : ℤ) | x.val) : ℤ) : ℂ) else 0)
        * (if Odd y.val then ((J(-(q : ℤ) | y.val) : ℤ) : ℂ) else 0)
    simp only [ZMod.val_mul, odd_mod_iff h2, Nat.odd_mul]
    by_cases hx : Odd x.val <;> by_cases hy : Odd y.val <;> simp only [hx, hy, and_self,
      and_false, false_and, ↓reduceIte, zero_mul, mul_zero]
    rw [← jacobiSym_neg_mod h4 (hx.mul hy), jacobiSym.mul_right' _ hx.pos.ne' hy.pos.ne',
      Int.cast_mul]
  map_nonunit' x hx := by
    show (if Odd x.val then ((J(-(q : ℤ) | x.val) : ℤ) : ℂ) else 0) = 0
    split_ifs with ho
    · rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
      rw [Int.cast_eq_zero, jacobiSym.eq_zero_iff]
      refine ⟨ho.pos.ne', ?_⟩
      rw [Int.neg_gcd, Int.gcd_natCast_natCast]
      exact fun h => hx (Nat.Coprime.symm h)
    · rfl

variable {q : ℕ} [NeZero q] (h4 : 4 ∣ q)

lemma kroneckerChar_natCast_of_odd {n : ℕ} (hn : Odd n) :
    kroneckerChar q h4 n = ((J(-(q : ℤ) | n) : ℤ) : ℂ) := by
  have h2 : 2 ∣ q := (by norm_num : 2 ∣ 4).trans h4
  change (if Odd (n : ZMod q).val then ((J(-(q : ℤ) | (n : ZMod q).val) : ℤ) : ℂ) else 0) = _
  rw [ZMod.val_natCast, ← jacobiSym_neg_mod h4 hn]
  simp [(odd_mod_iff h2 n).2 hn]

end LLS

namespace LLS

/-- A Dirichlet character mod `q` is primitive if for every prime `p ∣ q` some `n ≡ 1 (mod q/p)`
has `χ n = −1`. -/
lemma isPrimitive_of_witness {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : ∀ p : ℕ, p.Prime → p ∣ q → ∃ n : ℕ, n ≡ 1 [MOD q / p] ∧ χ n = -1) : χ.IsPrimitive := by
  by_contra hne
  set c := χ.conductor with hcdef
  obtain ⟨hc, χ₀, hχ₀⟩ := χ.factorsThrough_conductor
  have ⟨k, hk⟩ := hc
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (by rw [DirichletCharacter.isPrimitive_def]; simpa using hk.symm)
  obtain ⟨p, hp, j, rfl⟩ := Nat.exists_prime_and_dvd hk1
  have hq : q = c * j * p := by rw [hk]; ring
  obtain ⟨n, hn1, hJ⟩ := h p hp ⟨c * j, by rw [hq]; ring⟩
  have hqp : q / p = c * j := by rw [hq, Nat.mul_div_cancel _ hp.pos]
  rw [hqp] at hn1
  have hunit : IsUnit (n : ZMod q) := by
    by_contra h'
    rw [MulChar.map_nonunit _ h'] at hJ
    norm_num at hJ
  have hcop : IsCoprime (n : ℤ) (q : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (ZMod.isUnit_iff_coprime n q).1 hunit
  have h1 : ((n : ℤ) : ZMod c) = 1 := by
    rw [Int.cast_natCast]
    have : n ≡ 1 [MOD c] := Nat.ModEq.of_mul_right j hn1
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 this, Nat.cast_one]
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hc hcop
  rw [← hχ₀, h1, MulChar.map_one] at this
  rw [show ((n : ℤ) : ZMod q) = (n : ZMod q) by simp, hJ] at this
  norm_num at this

open scoped NumberTheorySymbols

/-- `J(−4m | 1 + 2m) = −1` for `m ≡ 1, 2 (mod 4)`: the witness at `p = 2`. -/
lemma jacobiSym_witness_two {m : ℕ} (hm : m % 4 = 1 ∨ m % 4 = 2) :
    J(-((4 * m : ℕ) : ℤ) | 1 + 2 * m) = -1 := by
  have hodd : Odd (1 + 2 * m) := ⟨m, by ring⟩
  rw [jacobiSym_neg_four_mul m hodd]
  rcases hm with hm | hm
  · rw [show -(m : ℤ) = -1 * m by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hodd,
      jacobiSym.quadratic_reciprocity_one_mod_four hm hodd,
      ZMod.χ₄_nat_three_mod_four (by omega)]
    rw [jacobiSym.mod_left' (a₂ := 1) (by push_cast; simp [Int.add_mul_emod_self_right]),
      jacobiSym.one_left]
    norm_num
  · obtain ⟨m', rfl⟩ : 2 ∣ m := by omega
    have hm' : Odd m' := Nat.odd_iff.2 (by omega)
    rw [show -((2 * m' : ℕ) : ℤ) = -2 * m' by push_cast; ring, jacobiSym.mul_left,
      jacobiSym.at_neg_two hodd, jacobiSym.quadratic_reciprocity_one_mod_four' hm' (by omega),
      ZMod.χ₈'_nat_eq_if_mod_eight,
      show (1 + 2 * (2 * m')) % 2 = 1 by omega, show (1 + 2 * (2 * m')) % 8 = 5 by omega]
    rw [jacobiSym.mod_left' (a₂ := 1) (by
        push_cast
        rw [show (1 : ℤ) + 2 * (2 * m') = 1 + m' * 4 by ring, Int.add_mul_emod_self_left]),
      jacobiSym.one_left]
    norm_num

/-- **Primitivity.** For `q = 4m`, `m` squarefree, `m ≡ 1, 2 (mod 4)` (i.e. `−q` a fundamental
discriminant), the Kronecker character `χ_{−q}` is primitive mod `q`. -/
lemma kroneckerChar_isPrimitive {m : ℕ} (hsq : Squarefree m) (hm : m % 4 = 1 ∨ m % 4 = 2)
    [NeZero (4 * m)] : (kroneckerChar (4 * m) (dvd_mul_right 4 m)).IsPrimitive := by
  have h4 : 4 ∣ 4 * m := dvd_mul_right 4 m
  have hm0 : m ≠ 0 := by rintro rfl; omega
  refine isPrimitive_of_witness _ fun p hp hpq => ?_
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1 + 2 * m, ?_, ?_⟩
    · rw [show 4 * m / 2 = 2 * m by omega]
      show (1 + 2 * m) % (2 * m) = 1 % (2 * m)
      rw [Nat.add_mod_right]
    · rw [kroneckerChar_natCast_of_odd h4 ⟨m, by ring⟩, jacobiSym_witness_two hm]
      norm_num
  · have hpodd : Odd p := hp.odd_of_ne_two hp2
    have := Fact.mk hp
    -- `q = r p` with `p ∤ r`
    have hcop4 : p.Coprime 4 := by
      simpa using Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hpm : p ∣ m := (Nat.Coprime.dvd_mul_left hcop4).1 hpq
    obtain ⟨r', hr'⟩ := hpm
    set r := 4 * r' with hr
    have hqr : 4 * m = r * p := by rw [hr', hr]; ring
    have hpr : ¬ p ∣ r' := by
      rintro ⟨s, rfl⟩
      have := hsq p ⟨s, by rw [hr']; ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
    have hcop : (4 * r).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      rw [hr, ← mul_assoc] at h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 by simpa using h)))
      · exact hpr h
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop 1 a.val
    have hn1' : n % (4 * r) = 1 := by
      have := (hn1 : n % (4 * r) = 1 % (4 * r))
      rw [this, Nat.mod_eq_of_lt (by have : 0 < r' := Nat.pos_of_ne_zero (by
        rintro rfl; simp at hr'; exact hm0 hr'); omega)]
    have hn4 : n % 4 = 1 := by
      have : n % 4 = n % (4 * r) % 4 := (Nat.mod_mod_of_dvd n (dvd_mul_right 4 r)).symm
      rw [this, hn1']
    have hnodd : Odd n := Nat.odd_iff.2 (by omega)
    refine ⟨n, ?_, ?_⟩
    · rw [show 4 * m / p = r by rw [hqr, Nat.mul_div_cancel _ hp.pos]]
      exact Nat.ModEq.of_mul_left 4 hn1
    · rw [kroneckerChar_natCast_of_odd h4 hnodd]
      have hJ1 : J(-(r : ℤ) | n) = 1 := by
        rw [jacobiSym.mod_right _ hnodd, show (-(r : ℤ)).natAbs = r by simp, hn1',
          jacobiSym.one_right]
      have hJ2 : J((p : ℤ) | n) = -1 := by
        rw [jacobiSym.quadratic_reciprocity_one_mod_four' hpodd hn4,
          ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
        have : ((n : ℤ) : ZMod p) = a := by
          rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 hn2, ZMod.natCast_zmod_val]
        rwa [this]
      rw [hqr, show -((r * p : ℕ) : ℤ) = -(r : ℤ) * p by push_cast; ring, jacobiSym.mul_left,
        hJ1, hJ2]
      norm_num

end LLS
