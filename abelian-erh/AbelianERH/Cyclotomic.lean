import AbelianERH.Factorisation

/-!
# ERH for cyclotomic fields from GRH

For `K = ℚ(ζ_N)` and a prime `q ∤ N`, `q` is unramified in `K` and every prime above it has
inertia degree `f = ord_N(q)` (Mathlib's `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`,
`ramificationIdxIn_eq_of_not_dvd`), so there are `φ(N) / f` of them. Hence
`Λ_K(q^k) = φ(N) log q · [f ∣ k]`. By orthogonality,
`∑_{χ mod N} χ(q^k) Λ(q^k) = φ(N) log q · [q^k ≡ 1 mod N]`, and `q^k ≡ 1 ⟺ f ∣ k`. So
`Λ_K(n) = ∑_{χ mod N} χ(n) Λ(n)` for every `n` coprime to `N` (`coeffIdentity_cyclotomic`), and
`extendedRiemannHypothesis_of_coeff` applies with all characters mod `N`.
-/

namespace AbelianERH

open NumberField Finset ArithmeticFunction Artin.Analytic

variable {N : ℕ} [NeZero N] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

lemma inertiaDeg_cyclotomic {q : ℕ} (hq : q.Prime) (hqN : ¬q ∣ N) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K q) : P.inertiaDeg ℤ = orderOf (q : ZMod N) := by
  have := Fact.mk hq
  obtain ⟨h1, h2⟩ := (mem_primesAbove hq).1 hP
  exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P hqN

lemma card_mul_orderOf_cyclotomic {q : ℕ} (hq : q.Prime) (hqN : ¬q ∣ N) :
    (primesAbove K q).card * orderOf (q : ZMod N) = Module.finrank ℚ K := by
  have := Fact.mk hq
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have := Int.ideal_span_isMaximal_of_prime q
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(q : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd q K hqN,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd q K hqN, one_mul,
    ncard_primesOver_eq hq, IsGalois.card_aut_eq_finrank] at h
  exact h

/-- **The coefficient identity for `ℚ(ζ_N)`**: `Λ_K(n) = ∑_{χ mod N} χ(n) Λ(n)` for `(n, N) = 1`. -/
theorem coeffIdentity_cyclotomic :
    CoeffIdentity K (Finset.univ : Finset (DirichletCharacter ℂ N)) := by
  intro n hn
  rw [← Finset.sum_mul, DirichletCharacter.sum_characters_eq]
  by_cases hΛ : Λ n = 0
  · simp [hΛ, vonMangoldtK_eq_zero K hΛ]
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
  have hqN : ¬q ∣ N := fun h => (Nat.Prime.coprime_iff_not_dvd hq).1
    (Nat.Coprime.coprime_dvd_left (dvd_pow_self q hk.ne') hn) h
  rw [vonMangoldtK_prime_pow K hq (fun P hP => inertiaDeg_cyclotomic K hq hqN hP)
    (card_mul_orderOf_cyclotomic K hq hqN) hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hq]
  have hiff : ((q ^ k : ℕ) : ZMod N) = 1 ↔ orderOf (q : ZMod N) ∣ k := by
    rw [Nat.cast_pow, orderOf_dvd_iff_pow_eq_one]
  have hfin : Module.finrank ℚ K = N.totient :=
    IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))
  by_cases h : orderOf (q : ZMod N) ∣ k
  · rw [ite_eq_left h, ite_eq_left (hiff.2 h), hfin]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right (mt hiff.1 h)]
    simp

omit [NeZero N] [IsCyclotomicExtension {N} ℚ K] in
/-- **ERH for `ℚ(ζ_N)` from GRH for Dirichlet L-functions.** -/
theorem cyclotomic_extendedRiemannHypothesis_of_GRH (hGRH : DirichletLZerosOnLine) (N : ℕ)
    [NeZero N] [IsCyclotomicExtension {N} ℚ K] : ERH.ExtendedRiemannHypothesis K :=
  extendedRiemannHypothesis_of_coeff K hGRH (coeffIdentity_cyclotomic (N := N) K)

/-- **Stage 1 headline (tier C).** ERH for every cyclotomic field, given GRH for Dirichlet
L-functions. -/
theorem cyclotomicERH_of_GRH (hGRH : DirichletLZerosOnLine) : CyclotomicERHStatement :=
  fun N _ K _ _ _ => cyclotomic_extendedRiemannHypothesis_of_GRH K hGRH N

end AbelianERH
