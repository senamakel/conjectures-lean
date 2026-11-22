import Artin.Analytic.Interface

/-!
# Splitting of primes in Kummer fields (blueprint step A5)

For `a ≠ 0`, `k ≠ 0` and a prime `p ∤ k a`, the prime `p` splits completely in
`K_k = ℚ(ζ_k, a^{1/k})` iff `k ∣ p - 1` and `a^((p-1)/k) = 1` in `ZMod p`, the condition in
`kummerCount`.

Dedekind–Kummer needs a monogenic order of index prime to `p`, which `K_k` need not have, so we
argue with the decomposition group instead.

* `⇒` (`kummerCond_of_absNorm_eq`): if some prime `𝔓 ∣ p` has residue field `𝔽_p`, the images
  of the `k` roots of `X^k - a` in `𝓞 K` are `k` distinct roots in `𝔽_p`. Distinct, because two
  roots differ by a root of unity `ζ ≠ 1`, and `1 + ζ + ⋯ + ζ^{k-1} = 0` would give `k = 0` in
  `𝔽_p`. So `𝔽_p^×` has an element of order `k`, and `a = b^k` has `a^((p-1)/k) = b^(p-1) = 1`.
* `⇐` (`stabilizer_trivial`): if the condition holds, every root `r` of `X^k - a` satisfies
  `r^p ≡ r` modulo any `𝔓 ∣ p`, so `r ≡ m` for an integer `m`. An element `σ` of the
  decomposition group of `𝔓` then has `σ r ≡ m ≡ r`, hence `σ r = r` (roots stay distinct
  mod `𝔓`), so `σ = 1`. The decomposition group has order `e f` (`Ideal.card_stabilizer_eq`),
  so `e = f = 1`, and there are `n = [K_k : ℚ]` primes above `p`.

Main results:

* `mem_primesAbove`: `primesAbove K p` is the set of primes of `𝓞 K` over `p`;
* `card_primesAbove_le`: at most `[K : ℚ]` primes lie over `p`, in any number field;
* `kummerCond_iff_exists_absNorm_eq`: for `p ∤ k a`, the Kummer condition holds iff some prime
  of `𝓞 K_k` above `p` has norm `p`;
* `absNorm_eq_of_kummerCond`, `card_primesAbove_of_kummerCond`: under the condition, every
  prime above `p` has norm `p` and there are `[K_k : ℚ]` of them (`p` splits completely).
-/

namespace Artin.Analytic

open Polynomial NumberField Ideal Artin.Kummer
open scoped Pointwise

/-! ### Primes above `p` -/

section General

variable {K : Type*} [Field K] [NumberField K]

lemma span_ne_bot {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simpa using hp.ne_zero

lemma mem_primesAbove {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} :
    P ∈ primesAbove K p ↔ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have := Int.ideal_span_isMaximal_of_prime p
  exact IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) (𝓞 K)

lemma coe_primesAbove {p : ℕ} (hp : p.Prime) :
    (primesAbove K p : Set (Ideal (𝓞 K))) = (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  ext P; exact mem_primesAbove hp

lemma ncard_primesOver_eq {p : ℕ} (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = (primesAbove K p).card := by
  rw [← coe_primesAbove hp, Set.ncard_coe_finset]

/-- The norm of a prime `𝔓` above `p` is `p ^ f(𝔓)`. -/
lemma absNorm_eq_pow {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p) :
    p ^ P.inertiaDeg ℤ = Ideal.absNorm P := by
  obtain ⟨h1, h2⟩ := (mem_primesAbove hp).1 hP
  exact Ideal.pow_inertiaDeg p P

lemma one_le_inertiaDeg {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p) :
    1 ≤ P.inertiaDeg ℤ := by
  obtain ⟨h1, h2⟩ := (mem_primesAbove hp).1 hP
  exact Ideal.inertiaDeg_pos P ℤ

lemma le_absNorm {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p) :
    p ≤ Ideal.absNorm P := by
  rw [← absNorm_eq_pow hp hP]
  exact Nat.le_self_pow (Nat.one_le_iff_ne_zero.1 (one_le_inertiaDeg hp hP)) p

/-- At most `[K : ℚ]` primes lie above a rational prime. -/
lemma card_primesAbove_le {p : ℕ} (hp : p.Prime) :
    (primesAbove K p).card ≤ Module.finrank ℚ K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Int.ideal_span_isMaximal_of_prime p
  have : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver _).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [← RingOfIntegers.rank K, ← hsum, ← ncard_primesOver_eq hp, Set.ncard_eq_toFinset_card',
    Set.toFinset_card, Fintype.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro q _
  have := q.2.1
  have := q.2.2
  have h1 := Ideal.ramificationIdx_pos (R := ℤ) q.1
  have h2 := Ideal.inertiaDeg_pos q.1 ℤ
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')

end General

/-! ### Two finite-field lemmas -/

/-- In a field of characteristic `p`, the solutions of `y^p = y` are the elements of the prime
field. -/
lemma exists_castHom_eq_of_pow_eq {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    {y : F} (hy : y ^ p = y) : ∃ z : ZMod p, ZMod.castHom dvd_rfl F z = y := by
  classical
  have h1 : 1 < p := hp.out.one_lt
  set T := (X ^ p - X : F[X]).roots.toFinset
  set I := (Finset.univ : Finset (ZMod p)).image (ZMod.castHom dvd_rfl F)
  have hne : (X ^ p - X : F[X]) ≠ 0 := X_pow_sub_X_ne_zero h1
  have hmem : ∀ w : F, w ^ p = w → w ∈ T := by
    intro w hw
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp [hw]
  have hIT : I ⊆ T := by
    intro w hw
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hw
    apply hmem
    rw [← map_pow, ZMod.pow_card]
  have hcard : T.card ≤ I.card := by
    rw [Finset.card_image_of_injective _ (ZMod.castHom dvd_rfl F).injective, Finset.card_univ,
      ZMod.card]
    calc T.card ≤ (X ^ p - X : F[X]).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X ^ p - X : F[X]).natDegree := card_roots' _
      _ = p := natDegree_X_pow_sub_X h1
  have := Finset.eq_of_subset_of_card_le hIT hcard
  have hyT := hmem y hy
  rw [← this] at hyT
  obtain ⟨z, -, hz⟩ := Finset.mem_image.1 hyT
  exact ⟨z, hz⟩

/-- In a field of characteristic `p`, `a^m = 1` iff it holds in `ZMod p`. -/
lemma intCast_pow_eq_one_iff {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] (a : ℤ)
    (m : ℕ) : (a : F) ^ m = 1 ↔ (a : ZMod p) ^ m = 1 := by
  rw [← (ZMod.castHom (dvd_refl p) F).injective.eq_iff, map_pow, map_intCast, map_one]

/-- An element of `K` integral over `ℤ`, as an element of `𝓞 K`. -/
def mkInt {K : Type*} [Field K] (x : K) (hx : IsIntegral ℤ x) : 𝓞 K := ⟨x, hx⟩

@[simp] lemma algebraMap_mkInt {K : Type*} [Field K] (x : K) (hx : IsIntegral ℤ x) :
    algebraMap (𝓞 K) K (mkInt x hx) = x := rfl

/-! ### Roots of `X^k - a` in `𝓞 K_k` -/

section Kummer

variable {a : ℤ} {k : ℕ}

lemma isGalois_kField (ha : a ≠ 0) (hk : k ≠ 0) : IsGalois ℚ (KField a k) := by
  have h : (X ^ k - C (a : ℚ)).Separable :=
    separable_X_pow_sub_C _ (by exact_mod_cast hk) (by exact_mod_cast ha)
  exact IsGalois.of_separable_splitting_field h

lemma isIntegral_of_pow_eq_intCast {L : Type*} [Field L] [CharZero L] (hk : k ≠ 0) {x : L}
    (hx : x ^ k = a) : IsIntegral ℤ x :=
  IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hx ▸ isIntegral_algebraMap (x := a))

lemma isIntegral_of_pow_eq_one {L : Type*} [Field L] [CharZero L] (hk : k ≠ 0) {x : L}
    (hx : x ^ k = 1) : IsIntegral ℤ x :=
  IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hx ▸ isIntegral_one)

variable {K : Type*} [Field K] [NumberField K]

/-- Two roots of `X^k - a` in `𝓞 K` with the same image in a field `F` with `k ≠ 0` and `a ≠ 0`
are equal. Their quotient `ζ` is a `k`-th root of unity, and if `ζ ≠ 1` then
`1 + ζ + ⋯ + ζ^(k-1) = 0` maps to `k = 0` in `F`. -/
lemma eq_of_map_eq {F : Type*} [Field F] (φ : 𝓞 K →+* F) (hk : (k : F) ≠ 0) (ha : (a : F) ≠ 0)
    {r s : 𝓞 K} (hr : r ^ k = a) (hs : s ^ k = a) (h : φ r = φ s) : r = s := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  set ι := algebraMap (𝓞 K) K
  have hrK : ι r ^ k = a := by rw [← map_pow, hr, map_intCast]
  have hsK : ι s ^ k = a := by rw [← map_pow, hs, map_intCast]
  have hs0 : ι s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk0] at hsK
    apply ha
    have ha0 : a = 0 := by exact_mod_cast hsK.symm
    simp [ha0]
  have hζk : (ι r / ι s) ^ k = 1 := by
    rw [div_pow, hrK, ← hsK, div_self (pow_ne_zero k hs0)]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : 𝓞 K, ι ζ = ι r / ι s :=
    ⟨⟨ι r / ι s, isIntegral_of_pow_eq_one hk0 hζk⟩, rfl⟩
  have hζs : ζ * s = r := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, hζ, div_mul_cancel₀ _ hs0]
  have hζpow : ζ ^ k = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hζ, hζk, map_one]
  by_contra hne
  have hζ1 : ζ ≠ 1 := by
    intro h1; exact hne (by rw [← hζs, h1, one_mul])
  have hgeom : ∑ i ∈ Finset.range k, ζ ^ i = 0 := by
    have := geom_sum_mul ζ k
    rw [hζpow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hζ1)
  have hφs : φ s ≠ 0 := by
    intro h0
    apply ha
    have := congrArg φ hs
    rw [map_pow, h0, zero_pow hk0, map_intCast] at this
    exact this.symm
  have hφζ : φ ζ = 1 := by
    have := congrArg φ hζs
    rw [map_mul, h] at this
    exact (mul_eq_right₀ hφs).1 this
  apply hk
  have := congrArg φ hgeom
  simpa [map_sum, hφζ] using this

end Kummer

/-! ### The splitting criterion -/

/-- The Kummer condition at `p`, as in `kummerCount`: `k ∣ p - 1` and `a^((p-1)/k) = 1` in
`ZMod p`, that is, `p ≡ 1 (mod k)` and `a` is a `k`-th power mod `p`. -/
def KummerCond (a : ℤ) (k p : ℕ) : Prop :=
  k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1

section Kummer

variable {a : ℤ} {k : ℕ}

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma smul_natCast' {G : Type*} [Group G] [MulSemiringAction G K] (σ : G) (n : ℕ) :
    σ • (n : 𝓞 K) = n :=
  map_natCast (MulSemiringAction.toRingHom G _ σ) n

omit [NumberField K] in
lemma smul_intCast' {G : Type*} [Group G] [MulSemiringAction G K] (σ : G) (n : ℤ) :
    σ • (n : 𝓞 K) = n :=
  map_intCast (MulSemiringAction.toRingHom G _ σ) n

omit [NumberField K] in
lemma natCast_mem_of_liesOver {p : ℕ} (P : Ideal (𝓞 K)) [h : P.LiesOver (Ideal.span {(p : ℤ)})] :
    (p : 𝓞 K) ∈ P := by
  have : (p : ℤ) ∈ P.under ℤ := by rw [← h.over]; exact Ideal.mem_span_singleton_self _
  simpa using this

lemma exists_root_int (hk : k ≠ 0) {α : K} (hα : α ^ k = a) : ∃ s : 𝓞 K, s ^ k = a :=
  ⟨mkInt α (isIntegral_of_pow_eq_intCast hk hα),
    RingOfIntegers.coe_injective (by simpa using hα)⟩

lemma exists_isPrimitiveRoot_int (hk : k ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ k) :
    ∃ ζ' : 𝓞 K, IsPrimitiveRoot ζ' k := by
  refine ⟨mkInt ζ (isIntegral_of_pow_eq_one hk hζ.pow_eq_one), ?_⟩
  exact (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap (𝓞 K) K)
    RingOfIntegers.coe_injective).1 (by simpa using hζ)

/-- **Splitting, `⇒`.** If a prime `𝔓` of `𝓞 K_k` above `p ∤ k a` has norm `p`, the Kummer
condition holds at `p`. -/
theorem kummerCond_of_absNorm_eq' (ha : a ≠ 0) (hk : k ≠ 0) {s ζ : 𝓞 K} (hs : s ^ k = a)
    (hζ : IsPrimitiveRoot ζ k) {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ k) (hpa : ¬ (p : ℤ) ∣ a) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p)
    (hN : Ideal.absNorm P = p) : KummerCond a k p := by
  have : Fact p.Prime := ⟨hp⟩
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨hP1, hP2⟩ := (mem_primesAbove hp).1 hP
  have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  let := Ideal.Quotient.field P
  set φ := Ideal.Quotient.mk P
  have hpF : ((p : ℕ) : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast φ]; exact Ideal.Quotient.eq_zero_iff_mem.2 (natCast_mem_of_liesOver P)
  have : CharP (𝓞 K ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp).2 hpF
  have hcard : Nat.card (𝓞 K ⧸ P) = p := by rw [← Ideal.absNorm_eq_natCard, hN]
  have : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let := Fintype.ofFinite (𝓞 K ⧸ P)
  have hcard' : Fintype.card (𝓞 K ⧸ P) = p := by rw [← Nat.card_eq_fintype_card, hcard]
  have hkF : ((k : ℕ) : 𝓞 K ⧸ P) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff _ p]
  have haF : ((a : ℤ) : 𝓞 K ⧸ P) ≠ 0 := by rwa [Ne, CharP.intCast_eq_zero_iff _ p]
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hs; exact ha (by exact_mod_cast hs.symm)
  have hφζ : IsPrimitiveRoot (φ ζ) k := by
    refine IsPrimitiveRoot.mk_of_lt _ (Nat.pos_of_ne_zero hk) (by rw [← map_pow, hζ.pow_eq_one,
      map_one]) fun l hl0 hlk h => ?_
    have hroot : (ζ ^ l * s) ^ k = a := by
      rw [mul_pow, ← pow_mul, mul_comm l k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hs]
    have := eq_of_map_eq φ hkF haF hroot hs (by rw [map_mul, map_pow, h, one_mul])
    have hl1 : ζ ^ l = 1 := mul_right_cancel₀ hs0 (by rw [one_mul]; exact this)
    exact hζ.pow_ne_one_of_pos_of_lt hl0.ne' hlk hl1
  have hφs : φ s ≠ 0 := by
    intro h0; apply haF; rw [← map_intCast φ, ← hs, map_pow, h0, zero_pow hk]
  have hdvd : k ∣ p - 1 := by
    apply hφζ.dvd_of_pow_eq_one
    rw [← hcard']
    exact FiniteField.pow_card_sub_one_eq_one _ (hφζ.ne_zero hk)
  refine ⟨hdvd, ?_⟩
  rw [← intCast_pow_eq_one_iff (F := 𝓞 K ⧸ P), ← map_intCast φ, ← hs, map_pow, ← pow_mul,
    Nat.mul_div_cancel' hdvd, ← hcard']
  exact FiniteField.pow_card_sub_one_eq_one _ hφs

/-- **Splitting, `⇐`.** Under the Kummer condition at `p ∤ k a`, the decomposition group of
every prime `𝔓` above `p` is trivial. -/
theorem eq_one_of_smul_eq' (hk : k ≠ 0)
    (hgen : ∀ σ : Gal(K/ℚ), (∀ x : K, x ^ k = a → σ x = x) → σ = 1) {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ k) (hpa : ¬ (p : ℤ) ∣ a) (hc : KummerCond a k p) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K p) {σ : Gal(K/ℚ)} (hσ : σ • P = P) : σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨hP1, hP2⟩ := (mem_primesAbove hp).1 hP
  have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  let := Ideal.Quotient.field P
  set φ := Ideal.Quotient.mk P
  have hpF : ((p : ℕ) : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast φ]; exact Ideal.Quotient.eq_zero_iff_mem.2 (natCast_mem_of_liesOver P)
  have : CharP (𝓞 K ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp).2 hpF
  have hkF : ((k : ℕ) : 𝓞 K ⧸ P) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff _ p]
  have haF : ((a : ℤ) : 𝓞 K ⧸ P) ≠ 0 := by rwa [Ne, CharP.intCast_eq_zero_iff _ p]
  -- every root of `X^k - a` in `𝓞 K` is fixed by `σ`
  have hfix : ∀ r : 𝓞 K, r ^ k = a → σ • r = r := by
    intro r hr
    have hy : φ r ^ p = φ r := by
      have h1 : φ r ^ (p - 1) = 1 := by
        rw [← Nat.mul_div_cancel' hc.1, pow_mul, ← map_pow, hr, map_intCast]
        exact (intCast_pow_eq_one_iff a _).2 hc.2
      calc φ r ^ p = φ r ^ (p - 1) * φ r := by
            rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
        _ = φ r := by rw [h1, one_mul]
    obtain ⟨z, hz⟩ := exists_castHom_eq_of_pow_eq hy
    have hzr : r - (z.val : 𝓞 K) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_natCast, ← hz]
      simp
    have hσr : σ • r - (z.val : 𝓞 K) ∈ P := by
      have := Ideal.smul_mem_pointwise_smul σ _ P hzr
      rwa [hσ, smul_sub, smul_natCast'] at this
    have hroot : (σ • r) ^ k = a := by rw [← smul_pow', hr, smul_intCast']
    refine eq_of_map_eq φ hkF haF hroot hr ?_
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have := P.sub_mem hσr hzr
    rwa [sub_sub_sub_cancel_right] at this
  refine hgen σ fun x hx => ?_
  have := congrArg (algebraMap (𝓞 K) K)
    (hfix (mkInt x (isIntegral_of_pow_eq_intCast hk hx)) (RingOfIntegers.coe_injective
      (by simpa using hx)))
  rw [algebraMap_mkInt] at this
  exact this

/-- Under the Kummer condition, `p` splits completely: every prime above `p` has norm `p`, and
there are `[K : ℚ]` of them. -/
theorem split_of_kummerCond' [IsGalois ℚ K] (hk : k ≠ 0)
    (hgen : ∀ σ : Gal(K/ℚ), (∀ x : K, x ^ k = a → σ x = x) → σ = 1) {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ k) (hpa : ¬ (p : ℤ) ∣ a) (hc : KummerCond a k p) :
    (∀ P ∈ primesAbove K p, Ideal.absNorm P = p) ∧
      (primesAbove K p).card = Module.finrank ℚ K := by
  have : Fact p.Prime := ⟨hp⟩
  have := Int.ideal_span_isMaximal_of_prime p
  have hef : ∀ P ∈ primesAbove K p, (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
      (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 ∧ P.inertiaDeg ℤ =
      (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 K) := by
    intro P hP
    obtain ⟨hP1, hP2⟩ := (mem_primesAbove hp).1 hP
    have hbot : MulAction.stabilizer Gal(K/ℚ) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      exact eq_one_of_smul_eq' hk hgen hp hpk hpa hc hP hσ
    have := Ideal.card_stabilizer_eq (G := Gal(K/ℚ)) (Ideal.span {(p : ℤ)}) P
    rw [hbot, Subgroup.card_bot] at this
    exact ⟨this.symm, (Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ)).symm⟩
  obtain ⟨⟨P₀, hP₀⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have hP₀' : P₀ ∈ primesAbove K p := (mem_primesAbove hp).2 hP₀
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨hP1, hP2⟩ := (mem_primesAbove hp).1 hP
    obtain ⟨h1, h2⟩ := hef P hP
    rw [← Ideal.pow_inertiaDeg p P, h2, Nat.eq_one_of_mul_eq_one_left h1, pow_one]
  · have := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
    rw [(hef P₀ hP₀').1, mul_one, ncard_primesOver_eq hp,
      IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at this
    exact this

end Kummer

/-! ### Specialisation to `K_k` -/

section KField

variable {a : ℤ} {k : ℕ}

/-- An automorphism of `K_k` fixing the roots of `X^k - a` is the identity. -/
lemma eq_one_of_forall_root (hk : k ≠ 0) (σ : Gal(KField a k/ℚ))
    (h : ∀ x : KField a k, x ^ k = a → σ x = x) : σ = 1 := by
  have hext : (σ : KField a k →ₐ[ℚ] KField a k) = AlgHom.id ℚ (KField a k) := by
    apply AlgHom.ext_of_adjoin_eq_top (SplittingField.adjoin_rootSet _)
    intro x hx
    exact h x ((mem_rootSet_iff hk).1 hx)
  ext x
  exact congrArg (fun f : KField a k →ₐ[ℚ] KField a k => f x) hext

/-- **A5.** For `p ∤ k a`, the Kummer condition holds at `p` iff some prime of `𝓞 K_k` above `p`
has norm `p`. -/
theorem kummerCond_iff_exists_absNorm_eq (ha : a ≠ 0) (hk : k ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ k) (hpa : ¬ (p : ℤ) ∣ a) :
    KummerCond a k p ↔ ∃ P ∈ primesAbove (KField a k) p, Ideal.absNorm P = p := by
  have := isGalois_kField ha hk
  constructor
  · intro hc
    obtain ⟨h1, h2⟩ := split_of_kummerCond' hk (eq_one_of_forall_root hk) hp hpk hpa hc
    have : (primesAbove (KField a k) p).Nonempty := by
      rw [← Finset.card_pos, h2]; exact Module.finrank_pos
    obtain ⟨P, hP⟩ := this
    exact ⟨P, hP, h1 P hP⟩
  · rintro ⟨P, hP, hN⟩
    obtain ⟨α, hα⟩ := exists_root ha hk
    obtain ⟨s, hs⟩ := exists_root_int hk hα
    obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot ha hk
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_int hk hζ₀
    exact kummerCond_of_absNorm_eq' ha hk hs hζ hp hpk hpa hP hN

/-- **A5, splitting completely.** Under the Kummer condition at `p ∤ k a`, every prime of
`𝓞 K_k` above `p` has norm `p`, and there are `[K_k : ℚ]` of them. -/
theorem split_of_kummerCond (ha : a ≠ 0) (hk : k ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ k) (hpa : ¬ (p : ℤ) ∣ a) (hc : KummerCond a k p) :
    (∀ P ∈ primesAbove (KField a k) p, Ideal.absNorm P = p) ∧
      (primesAbove (KField a k) p).card = kummerDegree a k := by
  have := isGalois_kField ha hk
  exact split_of_kummerCond' hk (eq_one_of_forall_root hk) hp hpk hpa hc

end KField

end Artin.Analytic
