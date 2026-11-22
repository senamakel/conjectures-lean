import Artin.Kummer.Degree

/-!
# Quadratic subfields of cyclotomic fields

For `a = a₀ c²` with `a₀` squarefree and `k` squarefree, `√a ∈ ℚ(ζ_k)` exactly when `a₀ ≡ 1 (mod 4)`
and `|a₀| ∣ k` (`exists_sq_cyclotomicField_iff'`).

* `⇒`: Mathlib knows that the ring of integers of `ℚ(ζ_n)` is `ℤ[ζ_n]`
  (`IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`). For a prime `p ∤ n`,
  `ℤ[ζ_n]/p = 𝔽_p[X]/Φ_n` is reduced since `Φ_n ∣ X^n - 1` is separable mod `p`; so if `x` is
  integral and `x²/p` is integral then `x/p` is integral (`exists_eq_mul_of_sq_eq_mul`). Applied to
  `x = √a₀` it shows that every prime factor of `a₀` divides `n`. Replacing `k` by its odd part `n`
  (same field), `p = 2` and `x = 1 + √a₀` show that `(1 + √a₀)/2` is integral, so `a₀ ≡ 1 (mod 4)`.
* `⇐`: quadratic Gauss sums, `g_p² = χ₄(p) p` for odd `p`, and `∏_{p ∣ a₀} χ₄(p) p = a₀`.
-/

namespace Artin.Kummer

open Polynomial IntermediateField

section Unramified

variable {n : ℕ} [NeZero n] {L : Type*} [Field L] [CharZero L]
  [hL : IsCyclotomicExtension {n} ℚ L]

/-- Integral elements of `ℚ(ζ_n)` are integer polynomials in `ζ_n`. -/
lemma exists_aeval_of_isIntegral {ζ : L} (hζ : IsPrimitiveRoot ζ n) {x : L}
    (hx : IsIntegral ℤ x) : ∃ h : ℤ[X], aeval ζ h = x := by
  have := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ {ζ})).1 hx
  have hy2 : (y : L) ∈ (aeval (R := ℤ) ζ).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact y.2
  obtain ⟨h, hh⟩ := hy2
  exact ⟨h, by rw [← hy]; exact hh⟩

omit [CharZero L] hL in
lemma isIntegral_aeval {ζ : L} (hζ : IsPrimitiveRoot ζ n) (h : ℤ[X]) :
    IsIntegral ℤ (aeval ζ h) := by
  have hint : IsIntegral ℤ ζ := hζ.isIntegral (NeZero.pos n)
  have : aeval ζ h ∈ Algebra.adjoin ℤ {ζ} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨h, rfl⟩
  exact adjoin_le_integralClosure hint this

/-- **`p ∤ n` is unramified in `ℚ(ζ_n)`**, in the form needed: if `x` and `y` are integral and
`x² = p y`, then `x = p z` with `z` integral. -/
lemma exists_eq_mul_of_sq_eq_mul {ζ : L} (hζ : IsPrimitiveRoot ζ n) {p : ℕ} (hp : p.Prime)
    (hpn : ¬ p ∣ n) {x y : L} (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (hxy : x ^ 2 = p * y) : ∃ z : L, IsIntegral ℤ z ∧ x = p * z := by
  obtain ⟨h, rfl⟩ := exists_aeval_of_isIntegral hζ hx
  obtain ⟨g, rfl⟩ := exists_aeval_of_isIntegral hζ hy
  have hint : IsIntegral ℤ ζ := hζ.isIntegral (NeZero.pos n)
  have hmin : minpoly ℤ ζ = cyclotomic n ℤ := (cyclotomic_eq_minpoly hζ (NeZero.pos n)).symm
  have hdvd : cyclotomic n ℤ ∣ h ^ 2 - C (p : ℤ) * g := by
    rw [← hmin]; apply minpoly.isIntegrallyClosed_dvd hint; simp [hxy]
  have := Fact.mk hp
  have hdvd' : cyclotomic n (ZMod p) ∣ (h.map (Int.castRingHom (ZMod p))) ^ 2 := by
    have := Polynomial.map_dvd (Int.castRingHom (ZMod p)) hdvd
    simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_cyclotomic] using this
  have hn0 : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpn
  have hsq : Squarefree (cyclotomic n (ZMod p)) :=
    ((X_pow_sub_one_separable_iff.2 hn0).of_dvd (cyclotomic.dvd_X_pow_sub_one n _)).squarefree
  obtain ⟨q, hq⟩ := (hsq.dvd_pow_iff_dvd two_ne_zero).1 hdvd'
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    (ZMod.ringHom_surjective _) q
  have hker : (h - cyclotomic n ℤ * q').map (Int.castRingHom (ZMod p)) = 0 := by
    simp [hq, map_cyclotomic]
  have hcoeff : ∀ i, (p : ℤ) ∣ (h - cyclotomic n ℤ * q').coeff i := fun i => by
    have := congrArg (fun f => f.coeff i) hker
    simp only [Polynomial.coeff_map, coeff_zero, eq_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  obtain ⟨r, hr⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 hcoeff
  refine ⟨aeval ζ r, isIntegral_aeval hζ r, ?_⟩
  have := congrArg (aeval ζ) hr
  have hcyc : aeval ζ (cyclotomic n ℤ) = 0 := by rw [← hmin]; exact minpoly.aeval ℤ ζ
  simp only [map_sub, map_mul, hcyc, zero_mul, sub_zero, map_natCast] at this
  exact this

omit [NeZero n] hL in
/-- An integer `c = m z` with `z` integral is divisible by `m`. -/
lemma dvd_of_eq_mul_isIntegral {c m : ℤ} (hm : m ≠ 0) {z : L} (hz : IsIntegral ℤ z)
    (h : (c : L) = m * z) : m ∣ c := by
  have hzq : z = algebraMap ℚ L ((c : ℚ) / m) := by
    have hm' : (m : L) ≠ 0 := by exact_mod_cast hm
    rw [map_div₀, map_intCast, map_intCast, h]; field_simp
  rw [hzq] at hz
  have hq : IsIntegral ℤ ((c : ℚ) / m) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ L).restrictScalars ℤ)
      (algebraMap ℚ L).injective).1 hz
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  refine ⟨y, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have : (c : ℚ) = m * y := by rw [algebraMap_int_eq, eq_intCast] at hy; rw [hy]; field_simp
  exact_mod_cast this

/-- **`⇒` in an odd cyclotomic field.** If `n` is odd and `a₀` squarefree has a square root in
`ℚ(ζ_n)`, then `a₀ ≡ 1 (mod 4)` and `|a₀| ∣ n`. -/
theorem mod_four_and_dvd_of_sq_eq {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hn : Odd n) {a₀ : ℤ}
    (h₀ : Squarefree a₀) {β : L} (hβ : β ^ 2 = a₀) : a₀ % 4 = 1 ∧ a₀.natAbs ∣ n := by
  have hβi : IsIntegral ℤ β :=
    ⟨X ^ 2 - C a₀, monic_X_pow_sub_C _ two_ne_zero, by rw [← aeval_def]; simp [hβ]⟩
  -- every prime factor of `a₀` divides `n`
  have hprime : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a₀ → p ∣ n := by
    intro p hp hpa
    by_contra hpn
    obtain ⟨e, he⟩ := hpa
    obtain ⟨z, hz, hβz⟩ := exists_eq_mul_of_sq_eq_mul hζ hp hpn hβi
      (y := (e : L)) (by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L e)))
      (by rw [hβ, he]; push_cast; ring)
    have h2 : ((p : ℤ) * p) ∣ a₀ := by
      refine dvd_of_eq_mul_isIntegral
        (mul_ne_zero (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hp.ne_zero)) (hz.pow 2) ?_
      rw [← hβ, hβz]; push_cast; ring
    have := h₀ p h2
    rw [Int.isUnit_iff] at this
    have := hp.two_le
    omega
  have hodd : ¬ (2 : ℤ) ∣ a₀ := fun h2 =>
    (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (hprime 2 Nat.prime_two (by exact_mod_cast h2)))
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, a₀ = 2 * t + 1 := ⟨a₀ / 2, by omega⟩
    have h2n : ¬ 2 ∣ n := fun h => (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h)
    have hti : IsIntegral ℤ (((t + 1 : ℤ) : L)) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L (t + 1)))
    obtain ⟨z, hz, h1z⟩ := exists_eq_mul_of_sq_eq_mul hζ Nat.prime_two h2n
      (isIntegral_one.add hβi) (hti.add hβi)
      (x := 1 + β) (y := ((t + 1 : ℤ) : L) + β) (by
        rw [add_sq, hβ, ht]; push_cast; ring)
    have h4 : (4 : ℤ) ∣ a₀ - 1 := by
      refine dvd_of_eq_mul_isIntegral (by norm_num) ((hz.pow 2).sub hz) ?_
      have hβ' : β = 2 * z - 1 := by push_cast at h1z; linear_combination h1z
      have : (a₀ : L) = (2 * z - 1) ^ 2 := by rw [← hβ, hβ']
      push_cast; rw [this]; ring
    omega
  · have hsq : Squarefree a₀.natAbs := Int.squarefree_natAbs.2 h₀
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      fun p hp => hprime p (Nat.prime_of_mem_primeFactors hp) ?_
    exact Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hp)

end Unramified

section GaussSum

open ZMod in
/-- **Quadratic Gauss sum.** For an odd prime `p` and a primitive `p`-th root of unity `ζ`,
`p* = χ₄(p) p` has a square root in `ℚ(ζ)`. -/
lemma exists_sq_eq_chi_four_mul {L : Type*} [Field L] [CharZero L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    ∃ g : L, g ^ 2 = ((χ₄ (p : ZMod 4) * p : ℤ) : L) := by
  have := Fact.mk hp
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hL : ringChar L ≠ 2 := by rw [ringChar.eq_zero]; norm_num
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom L)
  have hχ₁ : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [MulChar.ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char_ne_two hL
  refine ⟨gaussSum χ (AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left), ?_⟩
  rw [gaussSum_sq hχ₁ ((quadraticChar_isQuadratic _).comp _)
    (AddChar.zmodChar_primitive_of_primitive_root p hζ)]
  simp [χ, quadraticChar_neg_one hF, ZMod.card]

end GaussSum

section CyclotomicField

variable {k : ℕ}

/-- **`⇒`** in any `k`-th cyclotomic field, `k` squarefree: if `a₀` is squarefree and a square,
then `a₀ ≡ 1 (mod 4)` and `|a₀| ∣ k`. -/
theorem mod_four_and_dvd_of_sq_eq' {L : Type*} [Field L] [CharZero L] (hk : Squarefree k)
    [hL : IsCyclotomicExtension {k} ℚ L] {a₀ : ℤ} (h₀ : Squarefree a₀) {β : L}
    (hβ : β ^ 2 = a₀) : a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  have : NeZero k := ⟨hk.ne_zero⟩
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ L
  set ζ := IsCyclotomicExtension.zeta k ℚ L
  -- `k = e n` with `n` odd and `e ∈ {1, 2}`
  obtain ⟨n, e, hn, he, hkne⟩ : ∃ n e, Odd n ∧ (e = 1 ∨ e = 2) ∧ k = e * n := by
    by_cases h2 : 2 ∣ k
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨n, 2, Nat.not_even_iff_odd.1 fun ⟨m, hm⟩ => ?_, Or.inr rfl, rfl⟩
      have := hk 2 ⟨m, by rw [hm]; ring⟩
      exact absurd this (by decide)
    · exact ⟨k, 1, Nat.not_even_iff_odd.1 (fun h => h2 (even_iff_two_dvd.1 h)), Or.inl rfl,
        (one_mul k).symm⟩
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hη : IsPrimitiveRoot (ζ ^ e) n := hζ.pow (NeZero.pos k) hkne
  have hζmem : ζ ∈ ℚ⟮ζ ^ e⟯ := by
    rcases he with rfl | rfl
    · simpa using mem_adjoin_simple_self ℚ ζ
    · have hneg : ζ ^ n = -1 := by
        have h1 : (ζ ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, ← hkne]; exact hζ.pow_eq_one
        have h2 : ζ ^ n ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hn0 (by omega)
        have : (ζ ^ n - 1) * (ζ ^ n + 1) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (sub_eq_zero.1 h) h2
        · exact eq_neg_of_add_eq_zero_left h
      have : ζ = -((ζ ^ 2) ^ ((n + 1) / 2)) := by
        rw [← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.1 (hn.add_one)), pow_succ, hneg]
        ring
      have hmem : -((ζ ^ 2) ^ ((n + 1) / 2)) ∈ ℚ⟮ζ ^ 2⟯ :=
        neg_mem (pow_mem (mem_adjoin_simple_self ℚ (ζ ^ 2)) _)
      exact Eq.mpr (congrArg (fun x => x ∈ ℚ⟮ζ ^ 2⟯) this) hmem
  have hβmem : β ∈ ℚ⟮ζ ^ e⟯ := by
    have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hζ
    have : β ∈ Algebra.adjoin ℚ {ζ} := htop ▸ Algebra.mem_top
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.2 hζmem) :
      Algebra.adjoin ℚ {ζ} ≤ (ℚ⟮ζ ^ e⟯).toSubalgebra) this
  have : NeZero n := ⟨hn0⟩
  have hcyc := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hη' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ e)) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hη
  obtain ⟨h1, h2⟩ := mod_four_and_dvd_of_sq_eq (hL := by convert hcyc) hη' hn h₀
    (β := ⟨β, hβmem⟩) (Subtype.ext (by simpa using hβ))
  exact ⟨h1, h2.trans ⟨e, by rw [hkne, mul_comm]⟩⟩

/-- **`⇒`** for `CyclotomicField k ℚ`. -/
theorem mod_four_and_dvd_of_exists_sq (hk : Squarefree k) {a₀ : ℤ} (h₀ : Squarefree a₀)
    {β : CyclotomicField k ℚ} (hβ : β ^ 2 = a₀) : a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  have : NeZero k := ⟨hk.ne_zero⟩
  exact mod_four_and_dvd_of_sq_eq' hk
    (hL := by convert CyclotomicField.isCyclotomicExtension k ℚ; exact Subsingleton.elim _ _) h₀ hβ

open ZMod in
/-- **`⇐`.** If `a₀ ≡ 1 (mod 4)` is squarefree and `|a₀| ∣ k`, then `a₀` is a square in
`ℚ(ζ_k)`: it is the square of a product of quadratic Gauss sums. -/
theorem exists_sq_of_mod_four (hk : k ≠ 0) {a₀ : ℤ} (h₀ : Squarefree a₀) (h4 : a₀ % 4 = 1)
    (hdvd : a₀.natAbs ∣ k) : ∃ β : CyclotomicField k ℚ, β ^ 2 = a₀ := by
  have : NeZero k := ⟨hk⟩
  let _ : Algebra ℚ (CyclotomicField k ℚ) := CyclotomicField.algebra k ℚ
  set F := CyclotomicField k ℚ
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ F
  set ζ := IsCyclotomicExtension.zeta k ℚ F
  set s := a₀.natAbs.primeFactors
  have hg : ∀ p ∈ s, ∃ g : F, g ^ 2 = ((χ₄ (p : ZMod 4) * p : ℤ) : F) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpk : p ∣ k := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (2 : ℤ) ∣ a₀ := Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hp)
      omega
    obtain ⟨m, hm⟩ := hpk
    exact exists_sq_eq_chi_four_mul hp' hp2 (hζ.pow (NeZero.pos k) (by rw [hm, mul_comm]))
  choose! g hg' using hg
  refine ⟨∏ p ∈ s, g p, ?_⟩
  rw [← Finset.prod_pow, Finset.prod_congr rfl hg', ← Int.cast_prod]
  congr 1
  have hsq : Squarefree a₀.natAbs := Int.squarefree_natAbs.2 h₀
  rw [Finset.prod_mul_distrib, ← map_prod, ← Nat.cast_prod, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq, χ₄_nat_eq_if_mod_four]
  have habs := Int.natAbs_eq a₀
  generalize a₀.natAbs = m at habs ⊢
  rcases habs with h | h
  · have : m % 4 = 1 := by omega
    have h2 : m % 2 = 1 := by omega
    simp only [h2, this]
    norm_num
    omega
  · have : m % 4 = 3 := by omega
    have h2 : m % 2 = 1 := by omega
    simp only [h2, this]
    norm_num
    omega

end CyclotomicField

end Artin.Kummer
