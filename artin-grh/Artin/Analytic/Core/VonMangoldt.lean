import Artin.Analytic.Splitting
import Artin.Analytic.Continuation

/-!
# The von Mangoldt function of a number field

`Λ_K(n) = ∑_{𝔭, m ≥ 1, N𝔭^m = n} log N𝔭`, so that `ψ_K(x) = ∑_{n < x} Λ_K(n)` (`psiK_eq_sum`)
and `-ζ_K'/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for `Re s > 1` (`LSeries_vonMangoldtK`).

* `vonMangoldtK_le`: `Λ_K(n) ≤ [K : ℚ] Λ(n)`. For `n = p^j` the ideals `𝔭^m` of norm `p^j` have
  `f(𝔭) m = j`, each contributes `f(𝔭) log p`, and `∑_{𝔭 ∣ p} f(𝔭) ≤ ∑ e f = [K : ℚ]`.
* `log_mul_idealCount`: `log n · a(n) = ∑_{d ∣ n} Λ_K(d) a(n/d)`, `a(n)` the number of ideals of
  norm `n` (`idealCount`). Both sides count the pairs `(𝔭^m, J)` with `N(𝔭^m J) = n`, weighted by
  `log N𝔭`: `log N I = ∑_{𝔭^m ∣ I} log N𝔭` by unique factorisation (`log_absNorm_eq`), and the
  ideals of norm `n` divisible by `𝔭^m` are the `𝔭^m J` with `N J = n / N𝔭^m` (`card_filter_dvd`).
* `LSeries_vonMangoldtK_mul_dedekindZeta`: `L(Λ_K, s) ζ_K(s) = -ζ_K'(s)` for `Re s > 1`, from the
  convolution identity, Mathlib's `LSeries_convolution'` and `LSeries_deriv`.
* `dedekindZeta_eq_exp`: `ζ_K(s) = exp(∑ Λ_K(n)/log n · n^{-s})` for `Re s > 1`: both sides have
  logarithmic derivative `-L(Λ_K, s)` on the connected half-plane and tend to `1` as `s → +∞`.
  This replaces the Euler product: it gives `dedekindZeta_ne_zero` and, since the coefficients of
  `log ζ_K` are non-negative, Mertens' inequality (`Artin/Analytic/Core/NonvanishingOne.lean`).
* `LSeries_vonMangoldtK`: `-ζ_K'/ζ_K = ∑ Λ_K(n) n^{-s}` for `Re s > 1`.
-/

namespace Artin.Analytic

open NumberField Finset ArithmeticFunction UniqueFactorizationMonoid

variable (K : Type*) [Field K] [NumberField K]

/-- The von Mangoldt function of `K`: `Λ_K(n) = ∑_{𝔭, m ≥ 1, N𝔭^m = n} log N𝔭`, the sum over
prime ideals `𝔭` (grouped by the rational prime `p` below them) and exponents `m ≥ 1`. The ranges
`p ≤ n` and `m ≤ n` are no restriction, since `N𝔭^m ≥ p` and `N𝔭^m ≥ 2^m > m`. -/
noncomputable def vonMangoldtK (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p, ∑ m ∈ Icc 1 n,
    if Ideal.absNorm P ^ m = n then Real.log (Ideal.absNorm P) else 0

lemma vonMangoldtK_nonneg (n : ℕ) : 0 ≤ vonMangoldtK K n := by
  unfold vonMangoldtK
  refine sum_nonneg fun p _ => sum_nonneg fun P _ => sum_nonneg fun m _ => ?_
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

/-- `ψ_K(x) = ∑_{n < x} Λ_K(n)`, the sum over `n < ⌈x⌉`. Both sides run over the pairs
`(𝔭, m)` with `N𝔭^m < x`. -/
theorem psiK_eq_sum {x : ℝ} (hx : 0 ≤ x) :
    psiK K x = ∑ n ∈ range ⌈x⌉₊, vonMangoldtK K n := by
  classical
  set X := ⌈x⌉₊
  have key : ∀ {p : ℕ}, p.Prime → ∀ {P : Ideal (𝓞 K)}, P ∈ primesAbove K p → ∀ {m : ℕ}, 1 ≤ m →
      p ≤ Ideal.absNorm P ^ m ∧ m < Ideal.absNorm P ^ m := by
    intro p hp P hP m hm
    have h2 : 2 ≤ Ideal.absNorm P := hp.two_le.trans (le_absNorm hp hP)
    refine ⟨(le_absNorm hp hP).trans (Nat.le_self_pow (by omega) _), ?_⟩
    exact (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left h2 m)
  -- Step 1: each `Λ_K(n)`, `n < X`, as a sum over the box `p ≤ X`, `1 ≤ m ≤ X`.
  have step1 : ∀ n ∈ range X, vonMangoldtK K n =
      ∑ p ∈ (range (X + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p, ∑ m ∈ Icc 1 X,
        if Ideal.absNorm P ^ m = n then Real.log (Ideal.absNorm P) else 0 := by
    intro n hn
    have hnX : n < X := mem_range.1 hn
    unfold vonMangoldtK
    rw [sum_subset (filter_subset_filter _ (range_subset_range.2 (by omega : n + 1 ≤ X + 1)))]
    · refine sum_congr rfl fun p hp => sum_congr rfl fun P hP => ?_
      have hp' := (mem_filter.1 hp).2
      refine sum_subset (Icc_subset_Icc le_rfl hnX.le) fun m hm hm' => ?_
      have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
      have hmn : n < m := by rw [mem_Icc] at hm'; omega
      have := (key hp' hP hm1).2
      rw [if_neg (by omega)]
    · intro p hp hp'
      have hpr := (mem_filter.1 hp).2
      have hpn : n < p := by
        by_contra hc; push Not at hc
        exact hp' (mem_filter.2 ⟨mem_range.2 (by omega), hpr⟩)
      refine sum_eq_zero fun P hP => sum_eq_zero fun m hm => ?_
      have := (key hpr hP (mem_Icc.1 hm).1).1
      rw [if_neg (by omega)]
  rw [sum_congr rfl step1, sum_comm]
  -- Step 2: the left side over the same box.
  unfold psiK
  rw [sum_subset (filter_subset_filter _ (range_subset_range.2
    (by have := Nat.floor_le_ceil x; omega : ⌊x⌋₊ + 1 ≤ X + 1)))]
  · refine sum_congr rfl fun p hp => ?_
    have hpr := (mem_filter.1 hp).2
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun P hP => ?_
    conv_rhs => rw [sum_comm]
    rw [sum_subset (Icc_subset_Icc le_rfl (Nat.floor_le_ceil x))]
    · refine sum_congr rfl fun m hm => ?_
      rw [sum_ite_eq]
      have hiff : Ideal.absNorm P ^ m ∈ range X ↔ ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x := by
        rw [mem_range, ← Nat.cast_pow]; exact Nat.lt_ceil
      by_cases hc : ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x
      · rw [if_pos hc, if_pos (hiff.2 hc)]
      · rw [if_neg hc, if_neg (fun h => hc (hiff.1 h))]
    · intro m hm hm'
      have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
      have hmx : ⌊x⌋₊ < m := by rw [mem_Icc] at hm'; omega
      have hxm : x < m := by
        have := Nat.lt_floor_add_one x
        have : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hmx
        push_cast at this; linarith
      have := (key hpr hP hm1).2
      rw [if_neg]
      intro h
      have : ((m : ℕ) : ℝ) < ((Ideal.absNorm P ^ m : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
  · intro p hp hp'
    have hpr := (mem_filter.1 hp).2
    have hpx : x < p := by
      have hp2 : ⌊x⌋₊ + 1 ≤ p := by
        by_contra hc; push Not at hc
        exact hp' (mem_filter.2 ⟨mem_range.2 (by omega), hpr⟩)
      have := Nat.lt_floor_add_one x
      have : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp2
      push_cast at this; linarith
    refine sum_eq_zero fun P hP => sum_eq_zero fun m hm => ?_
    have := (key hpr hP (mem_Icc.1 hm).1).1
    rw [if_neg]
    intro h
    have : ((p : ℕ) : ℝ) ≤ ((Ideal.absNorm P ^ m : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith

theorem psiK_natCast_eq_sum (x : ℕ) : psiK K x = ∑ n ∈ range x, vonMangoldtK K n := by
  rw [psiK_eq_sum K (Nat.cast_nonneg x), Nat.ceil_natCast]

/-- `∑_{𝔭 ∣ p} f(𝔭) ≤ [K : ℚ]`, from `∑ e f = [K : ℚ]`. -/
lemma sum_inertiaDeg_le {p : ℕ} (hp : p.Prime) :
    ∑ P ∈ primesAbove K p, P.inertiaDeg ℤ ≤ Module.finrank ℚ K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Int.ideal_span_isMaximal_of_prime p
  have : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver _).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [← RingOfIntegers.rank K, ← hsum,
    Finset.sum_subtype (primesAbove K p) (fun P => mem_primesAbove hp)]
  apply Finset.sum_le_sum
  intro q _
  have := q.2.1
  have := q.2.2
  have h1 := Ideal.ramificationIdx_pos (R := ℤ) q.1
  exact Nat.le_mul_of_pos_left _ h1

/-- `Λ_K(n) ≤ [K : ℚ] Λ(n)`. -/
theorem vonMangoldtK_le (n : ℕ) : vonMangoldtK K n ≤ Module.finrank ℚ K * Λ n := by
  classical
  unfold vonMangoldtK
  by_cases hn : IsPrimePow n
  · obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hq]
    have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    -- each prime `p` contributes at most `[p = q] f(𝔭) log q` per `𝔭`
    have hterm : ∀ p ∈ (range (q ^ k + 1)).filter Nat.Prime, ∀ P ∈ primesAbove K p,
        ∑ m ∈ Icc 1 (q ^ k), (if Ideal.absNorm P ^ m = q ^ k then
          Real.log (Ideal.absNorm P) else 0) ≤
        if p = q then (P.inertiaDeg ℤ : ℝ) * Real.log q else 0 := by
      intro p hp P hP
      have hpr := (mem_filter.1 hp).2
      have hN := absNorm_eq_pow hpr hP
      have hf := one_le_inertiaDeg hpr hP
      have h2 : 2 ≤ Ideal.absNorm P := hpr.two_le.trans (le_absNorm hpr hP)
      split_ifs with hpq
      · subst hpq
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Icc 1 (p ^ k)).filter (fun m => Ideal.absNorm P ^ m = p ^ k)).card ≤ 1 := by
          refine Finset.card_le_one.2 fun a ha b hb => ?_
          have ha' := (mem_filter.1 ha).2
          have hb' := (mem_filter.1 hb).2
          exact Nat.pow_right_injective h2 (ha'.trans hb'.symm)
        have hlog : Real.log (Ideal.absNorm P) = (P.inertiaDeg ℤ : ℕ) * Real.log p := by
          rw [← hN, Nat.cast_pow, Real.log_pow]
        rw [hlog]
        have : (0 : ℝ) ≤ P.inertiaDeg ℤ * Real.log p := by positivity
        calc (((Icc 1 (p ^ k)).filter (fun m => Ideal.absNorm P ^ m = p ^ k)).card : ℝ) *
              ((P.inertiaDeg ℤ : ℕ) * Real.log p)
            ≤ 1 * ((P.inertiaDeg ℤ : ℕ) * Real.log p) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) this
          _ = _ := one_mul _
      · refine le_of_eq (Finset.sum_eq_zero fun m hm => if_neg fun h => hpq ?_)
        have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
        have hdvd : p ∣ q ^ k := by
          rw [← h, ← hN, ← pow_mul]
          exact dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))
        exact (Nat.prime_dvd_prime_iff_eq hpr hq).1 (hpr.dvd_of_dvd_pow hdvd)
    calc ∑ p ∈ (range (q ^ k + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p,
          ∑ m ∈ Icc 1 (q ^ k), (if Ideal.absNorm P ^ m = q ^ k then
            Real.log (Ideal.absNorm P) else 0)
        ≤ ∑ p ∈ (range (q ^ k + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p,
          (if p = q then (P.inertiaDeg ℤ : ℝ) * Real.log q else 0) :=
          sum_le_sum fun p hp => sum_le_sum fun P hP => hterm p hp P hP
      _ ≤ ∑ P ∈ primesAbove K q, (P.inertiaDeg ℤ : ℝ) * Real.log q := by
          simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
          rw [Finset.sum_ite_eq']
          split_ifs
          · exact le_rfl
          · exact sum_nonneg fun P _ => by positivity
      _ = (∑ P ∈ primesAbove K q, (P.inertiaDeg ℤ : ℝ)) * Real.log q := by rw [Finset.sum_mul]
      _ ≤ Module.finrank ℚ K * Real.log q := by
          gcongr
          exact_mod_cast sum_inertiaDeg_le K hq
  · have : ∀ p ∈ (range (n + 1)).filter Nat.Prime, ∀ P ∈ primesAbove K p, ∀ m ∈ Icc 1 n,
        (if Ideal.absNorm P ^ m = n then Real.log (Ideal.absNorm P) else 0) = 0 := by
      intro p hp P hP m hm
      refine if_neg fun h => hn ?_
      have hpr := (mem_filter.1 hp).2
      have hf := one_le_inertiaDeg hpr hP
      rw [← absNorm_eq_pow hpr hP, ← pow_mul] at h
      exact (isPrimePow_nat_iff n).2 ⟨p, _, hpr, Nat.mul_pos (by omega) (mem_Icc.1 hm).1, h⟩
    rw [sum_eq_zero fun p hp => sum_eq_zero fun P hP => sum_eq_zero fun m hm => this p hp P hP m hm]
    exact mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg

/-- The Dirichlet series of `Λ_K` converges absolutely for `Re s > 1`. -/
theorem LSeriesSummable_vonMangoldtK {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (vonMangoldtK K n : ℂ)) s := by
  have h := (LSeriesSummable_vonMangoldt hs).norm.mul_left (Module.finrank ℚ K : ℝ)
  refine Summable.of_norm_bounded h fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, Complex.norm_real,
    Real.norm_of_nonneg (vonMangoldtK_nonneg K n), Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg, ← mul_div_assoc]
  gcongr
  exact vonMangoldtK_le K n

/-- The number of ideals of norm `n`, the coefficients of `ζ_K`. -/
noncomputable def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- The ideals of norm `n`, as a finset. -/
noncomputable def idealsOfNorm (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) n).toFinset

variable {K}

lemma mem_idealsOfNorm {n : ℕ} {I : Ideal (𝓞 K)} :
    I ∈ idealsOfNorm K n ↔ Ideal.absNorm I = n := by
  simp [idealsOfNorm]

variable (K)

lemma idealCount_eq_card (n : ℕ) : idealCount K n = (idealsOfNorm K n).card := by
  rw [idealCount, idealsOfNorm, ← Nat.card_eq_card_finite_toFinset]
  rfl

variable {K}

lemma absNorm_pow_bounds {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p)
    {m : ℕ} (hm : 1 ≤ m) : p ≤ Ideal.absNorm P ^ m ∧ m < Ideal.absNorm P ^ m := by
  have h2 : 2 ≤ Ideal.absNorm P := hp.two_le.trans (le_absNorm hp hP)
  refine ⟨(le_absNorm hp hP).trans (Nat.le_self_pow (by omega) _), ?_⟩
  exact (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left h2 m)

variable (K)

/-- `Λ_K(n)` as a sum over a box `p ≤ N`, `1 ≤ m ≤ N` for any `N ≥ n`. -/
lemma vonMangoldtK_eq_box {n N : ℕ} (hnN : n ≤ N) :
    vonMangoldtK K n = ∑ p ∈ (range (N + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p,
      ∑ m ∈ Icc 1 N, if Ideal.absNorm P ^ m = n then Real.log (Ideal.absNorm P) else 0 := by
  unfold vonMangoldtK
  rw [sum_subset (filter_subset_filter _ (range_subset_range.2 (by omega : n + 1 ≤ N + 1)))]
  · refine sum_congr rfl fun p hp => sum_congr rfl fun P hP => ?_
    have hp' := (mem_filter.1 hp).2
    refine sum_subset (Icc_subset_Icc le_rfl hnN) fun m hm hm' => ?_
    have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
    have hmn : n < m := by rw [mem_Icc] at hm'; omega
    have := (absNorm_pow_bounds hp' hP hm1).2
    rw [if_neg (by omega)]
  · intro p hp hp'
    have hpr := (mem_filter.1 hp).2
    have hpn : n < p := by
      by_contra hc; push Not at hc
      exact hp' (mem_filter.2 ⟨mem_range.2 (by omega), hpr⟩)
    refine sum_eq_zero fun P hP => sum_eq_zero fun m hm => ?_
    have := (absNorm_pow_bounds hpr hP (mem_Icc.1 hm).1).1
    rw [if_neg (by omega)]

variable {K}

lemma exists_mem_primesAbove {Q : Ideal (𝓞 K)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    ∃ p, p.Prime ∧ Q ∈ primesAbove K p := by
  have : NeZero Q := ⟨hQ0⟩
  have hp := Nat.absNorm_under_prime Q
  refine ⟨_, hp, ?_⟩
  rw [mem_primesAbove hp]
  exact ⟨hQ, Int.liesOver_span_absNorm Q⟩

lemma eq_of_mem_primesAbove {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K p) (hP' : P ∈ primesAbove K q) : p = q := by
  have h1 := absNorm_eq_pow hp hP
  have h2 := absNorm_eq_pow hq hP'
  have hdvd : p ∣ q ^ P.inertiaDeg ℤ := by
    rw [h2, ← h1]
    exact dvd_pow_self p (by have := one_le_inertiaDeg hp hP; omega)
  exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd)

lemma mem_primesAbove_ne_bot {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p) :
    P ≠ ⊥ := by
  intro h
  have := le_absNorm hp hP
  rw [h, Ideal.absNorm_bot] at this
  exact hp.ne_zero (by omega)

lemma mem_primesAbove_isPrime {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K p) : P.IsPrime :=
  ((mem_primesAbove hp).1 hP).1

/-- `log N(∏ s) = ∑ log N(Q)` for a multiset of nonzero ideals. -/
lemma log_absNorm_prod (s : Multiset (Ideal (𝓞 K))) (hs : ∀ Q ∈ s, Q ≠ ⊥) :
    Real.log (Ideal.absNorm s.prod) = (s.map fun Q => Real.log (Ideal.absNorm Q)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons Q t ih =>
    have hQ : Q ≠ ⊥ := hs Q (Multiset.mem_cons_self _ _)
    have ht : ∀ R ∈ t, R ≠ ⊥ := fun R hR => hs R (Multiset.mem_cons_of_mem hR)
    have htp : t.prod ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact Multiset.prod_ne_zero fun h => ht 0 h rfl
    rw [Multiset.prod_cons, map_mul, Nat.cast_mul, Real.log_mul, ih ht, Multiset.map_cons,
      Multiset.sum_cons]
    · exact_mod_cast (Ideal.absNorm_eq_zero_iff.not).2 hQ
    · exact_mod_cast (Ideal.absNorm_eq_zero_iff.not).2 htp

/-- `P^m ∣ I ↔ m ≤ v_P(I)`. -/
lemma pow_dvd_iff_le_count {P I : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hI : I ≠ ⊥)
    {m : ℕ} : P ^ m ∣ I ↔ m ≤ (normalizedFactors I).count P := by
  have hirr : Irreducible P :=
    (Ideal.prime_iff_isPrime hP0 |>.2 hP).irreducible
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_count_normalizedFactors hirr hI,
    normalize_eq, Nat.cast_le]

variable (K)

open scoped Classical in
/-- `log N(I) = ∑_{𝔭, m ≥ 1, 𝔭^m ∣ I} log N𝔭` over any box containing the prime powers. -/
lemma log_absNorm_eq {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {N : ℕ} (hN : Ideal.absNorm I ≤ N) :
    Real.log (Ideal.absNorm I) = ∑ p ∈ (range (N + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p,
      ∑ m ∈ Icc 1 N, if P ^ m ∣ I then Real.log (Ideal.absNorm P) else 0 := by
  classical
  have hNI : Ideal.absNorm I ≠ 0 := (Ideal.absNorm_eq_zero_iff.not).2 hI
  set c : Ideal (𝓞 K) → ℕ := fun P => (normalizedFactors I).count P
  -- step 1: the inner sum over `m`
  have h1 : ∀ p ∈ (range (N + 1)).filter Nat.Prime, ∀ P ∈ primesAbove K p,
      (∑ m ∈ Icc 1 N, if P ^ m ∣ I then Real.log (Ideal.absNorm P) else 0) =
        c P * Real.log (Ideal.absNorm P) := by
    intro p hp P hP
    have hpr := (mem_filter.1 hp).2
    have hPp := mem_primesAbove_isPrime hpr hP
    have hP0 := mem_primesAbove_ne_bot hpr hP
    have hcN : c P ≤ N := by
      have hdvd : P ^ c P ∣ I := (pow_dvd_iff_le_count hPp hP0 hI).2 le_rfl
      have h2 : Ideal.absNorm P ^ c P ∣ Ideal.absNorm I := by
        rw [← map_pow]; exact map_dvd Ideal.absNorm hdvd
      have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hNI) h2
      have h4 : 2 ≤ Ideal.absNorm P := hpr.two_le.trans (le_absNorm hpr hP)
      have h5 : c P < Ideal.absNorm P ^ c P :=
        (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left h4 _)
      omega
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    congr 2
    have : (Icc 1 N).filter (fun m => P ^ m ∣ I) = Icc 1 (c P) := by
      ext m
      simp only [mem_filter, mem_Icc, pow_dvd_iff_le_count hPp hP0 hI]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hcN⟩, h2⟩
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  rw [sum_congr rfl fun p hp => sum_congr rfl fun P hP => h1 p hp P hP]
  -- step 2: the left side as a sum over the prime factors
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  rw [log_absNorm_prod _ (fun Q hQ => by
      rw [← Ideal.zero_eq_bot]; exact ne_zero_of_mem_normalizedFactors hQ),
    Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  -- step 3: reindex
  have hdisj : Set.PairwiseDisjoint (((range (N + 1)).filter Nat.Prime : Finset ℕ) : Set ℕ)
      (primesAbove K) := by
    intro p hp q hq hpq
    refine Finset.disjoint_left.2 fun P hP hP' => hpq ?_
    exact eq_of_mem_primesAbove (mem_filter.1 hp).2 (mem_filter.1 hq).2 hP hP'
  rw [← sum_biUnion hdisj]
  refine sum_subset (fun Q hQ => ?_) (fun Q _ hQ => ?_)
  · rw [Multiset.mem_toFinset] at hQ
    have hQp : Q.IsPrime := (Ideal.prime_iff_isPrime
      (by rw [← Ideal.zero_eq_bot]; exact ne_zero_of_mem_normalizedFactors hQ)).1
      (prime_of_normalized_factor Q hQ)
    have hQ0 : Q ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact ne_zero_of_mem_normalizedFactors hQ
    obtain ⟨p, hp, hQp'⟩ := exists_mem_primesAbove hQp hQ0
    refine mem_biUnion.2 ⟨p, mem_filter.2 ⟨mem_range.2 ?_, hp⟩, hQp'⟩
    have h2 : Ideal.absNorm Q ∣ Ideal.absNorm I :=
      map_dvd Ideal.absNorm (dvd_of_mem_normalizedFactors hQ)
    have := le_absNorm hp hQp'
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hNI) h2
    omega
  · rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hQ
    simp [hQ]

open scoped Classical in
/-- The ideals of norm `n` divisible by `Q` correspond to the ideals of norm `n / N(Q)`. -/
lemma card_filter_dvd {Q : Ideal (𝓞 K)} (hQ : Q ≠ ⊥) (n : ℕ) :
    ((idealsOfNorm K n).filter (Q ∣ ·)).card =
      if Ideal.absNorm Q ∣ n then idealCount K (n / Ideal.absNorm Q) else 0 := by
  classical
  have hNQ : Ideal.absNorm Q ≠ 0 := (Ideal.absNorm_eq_zero_iff.not).2 hQ
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hNQ), idealCount_eq_card]
    have hQ' : Q ≠ 0 := by rwa [Ideal.zero_eq_bot]
    have : (idealsOfNorm K (Ideal.absNorm Q * k)).filter (Q ∣ ·) =
        (idealsOfNorm K k).image (Q * ·) := by
      ext I
      simp only [mem_filter, mem_idealsOfNorm, mem_image]
      constructor
      · rintro ⟨hI, J, rfl⟩
        refine ⟨J, ?_, rfl⟩
        rw [map_mul] at hI
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hNQ) hI
      · rintro ⟨J, hJ, rfl⟩
        exact ⟨by rw [map_mul, hJ], dvd_mul_right _ _⟩
    rw [this, card_image_of_injective _ (mul_right_injective₀ hQ')]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro I hI hdvd
    rw [mem_idealsOfNorm] at hI
    exact h (hI ▸ map_dvd Ideal.absNorm hdvd)

open scoped Classical in
/-- **The convolution identity** `log · a = Λ_K ⋆ a`, `a(n)` the number of ideals of norm `n`:
both sides count pairs `(𝔭^m, J)` with `N(𝔭^m J) = n`, weighted by `log N𝔭`. -/
theorem log_mul_idealCount {n : ℕ} (hn : n ≠ 0) :
    Real.log n * idealCount K n =
      ∑ d ∈ n.divisors, vonMangoldtK K d * idealCount K (n / d) := by
  classical
  -- the right side
  have hR : ∑ d ∈ n.divisors, vonMangoldtK K d * idealCount K (n / d) =
      ∑ p ∈ (range (n + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p, ∑ m ∈ Icc 1 n,
        if Ideal.absNorm P ^ m ∣ n then
          Real.log (Ideal.absNorm P) * idealCount K (n / Ideal.absNorm P ^ m) else 0 := by
    rw [sum_congr rfl fun d hd => by
      rw [vonMangoldtK_eq_box K (Nat.divisor_le hd), sum_mul]]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    simp_rw [ite_mul, zero_mul]
    rw [sum_ite_eq]
    simp only [Nat.mem_divisors, hn, ne_eq, not_false_eq_true, and_true]
  -- the left side
  have hL : Real.log n * idealCount K n =
      ∑ p ∈ (range (n + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p, ∑ m ∈ Icc 1 n,
        ∑ I ∈ idealsOfNorm K n, if P ^ m ∣ I then Real.log (Ideal.absNorm P) else 0 := by
    rw [idealCount_eq_card, mul_comm, ← nsmul_eq_mul, ← sum_const]
    rw [sum_congr rfl fun I hI => by
      have hI' := mem_idealsOfNorm.1 hI
      have hI0 : I ≠ ⊥ := fun h => hn (by rw [← hI', h, Ideal.absNorm_bot])
      rw [← hI', log_absNorm_eq K hI0 le_rfl, hI']]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_comm]
  rw [hL, hR]
  refine sum_congr rfl fun p hp => sum_congr rfl fun P hP => sum_congr rfl fun m _ => ?_
  have hPm : P ^ m ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact mem_primesAbove_ne_bot (mem_filter.1 hp).2 hP)
  rw [← sum_filter, sum_const, card_filter_dvd K hPm, map_pow, nsmul_eq_mul]
  split_ifs <;> simp [mul_comm]


/-! ### L-series -/

section LSeries

open Filter Topology Complex Asymptotics
open scoped LSeries.notation

lemma dedekindZeta_eq_LSeries :
    dedekindZeta K = LSeries (fun n => (idealCount K n : ℂ)) := rfl

lemma idealCount_one : idealCount K 1 = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊤, Ideal.absNorm_top⟩, fun I => Subtype.ext ?_⟩
  exact Ideal.absNorm_eq_one_iff.1 I.2

/-- The ideal count has linear partial sums (from Mathlib's asymptotic count of ideals). -/
lemma tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 ((2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        Units.regulator K * classNumber K) /
          (Units.torsionOrder K * Real.sqrt |discr K|))) := by
  unfold idealCount
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- `ζ_K` converges absolutely for `Re s > 1`. -/
lemma LSeriesSummable_idealCount {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  have hl := tendsto_sum_idealCount_div K
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
    have h1 := hl.isBigO_one ℝ
    have he : (fun n : ℕ => ∑ k ∈ Icc 1 n, (idealCount K k : ℝ)) =ᶠ[atTop]
        fun n => ((∑ k ∈ Icc 1 n, (idealCount K k : ℝ)) / n) * (n : ℝ) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hn)]
    refine he.trans_isBigO ?_
    simpa using h1.mul (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n => Nat.cast_nonneg _)
    zero_le_one hs
  simpa using this

lemma abscissaOfAbsConv_idealCount_le :
    LSeries.abscissaOfAbsConv (fun n => (idealCount K n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_idealCount K (by simpa using hy)

lemma abscissaOfAbsConv_idealCount_lt {s : ℂ} (hs : 1 < s.re) :
    LSeries.abscissaOfAbsConv (fun n => (idealCount K n : ℂ)) < s.re :=
  (abscissaOfAbsConv_idealCount_le K).trans_lt (by exact_mod_cast hs)

lemma logMul_idealCount_eq {n : ℕ} (hn : n ≠ 0) :
    LSeries.logMul (fun n => (idealCount K n : ℂ)) n =
      ((fun n => (vonMangoldtK K n : ℂ)) ⍟ (fun n => (idealCount K n : ℂ))) n := by
  rw [LSeries.convolution_def]
  simp only [LSeries.logMul]
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (vonMangoldtK K d : ℂ) * (idealCount K e : ℂ))]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (log_mul_idealCount K hn)
  push_cast at h
  exact h

/-- `L(Λ_K, s) ζ_K(s) = -ζ_K'(s)` for `Re s > 1`. -/
theorem LSeries_vonMangoldtK_mul_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldtK K n : ℂ)) s * dedekindZeta K s =
      -deriv (dedekindZeta K) s := by
  rw [dedekindZeta_eq_LSeries, LSeries_deriv (abscissaOfAbsConv_idealCount_lt K hs), neg_neg,
    LSeries_congr (fun hn => logMul_idealCount_eq K hn),
    LSeries_convolution' (LSeriesSummable_vonMangoldtK K hs) (LSeriesSummable_idealCount K hs)]

lemma vonMangoldtK_one : vonMangoldtK K 1 = 0 :=
  le_antisymm (by simpa using vonMangoldtK_le K 1) (vonMangoldtK_nonneg K 1)

/-- The coefficients `Λ_K(n) / log n` of `log ζ_K`. -/
noncomputable def logZetaCoeff (n : ℕ) : ℝ := vonMangoldtK K n / Real.log n

lemma logZetaCoeff_nonneg (n : ℕ) : 0 ≤ logZetaCoeff K n :=
  div_nonneg (vonMangoldtK_nonneg K n) (Real.log_natCast_nonneg n)

lemma logZetaCoeff_le (n : ℕ) : logZetaCoeff K n ≤ Module.finrank ℚ K := by
  unfold logZetaCoeff
  rcases (Real.log_natCast_nonneg n).lt_or_eq with h | h
  · rw [div_le_iff₀ h]
    exact (vonMangoldtK_le K n).trans (by gcongr; exact vonMangoldt_le_log)
  · rw [← h, div_zero]; positivity

lemma LSeriesSummable_logZetaCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (logZetaCoeff K n : ℂ)) s := by
  have h := (LSeriesSummable_one_iff.2 hs).norm.mul_left (Module.finrank ℚ K : ℝ)
  refine Summable.of_norm_bounded h fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, Complex.norm_real,
    Real.norm_of_nonneg (logZetaCoeff_nonneg K n), Pi.one_apply, norm_one, ← mul_div_assoc,
    mul_one]
  gcongr
  exact logZetaCoeff_le K n

lemma abscissaOfAbsConv_logZetaCoeff_le :
    LSeries.abscissaOfAbsConv (fun n => (logZetaCoeff K n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_logZetaCoeff K (by simpa using hy)

lemma logMul_logZetaCoeff {n : ℕ} (hn : n ≠ 0) :
    LSeries.logMul (fun n => (logZetaCoeff K n : ℂ)) n = vonMangoldtK K n := by
  show Complex.log n * ((vonMangoldtK K n / Real.log n : ℝ) : ℂ) = vonMangoldtK K n
  rcases eq_or_ne n 1 with h1 | h1
  · rw [h1, vonMangoldtK_one, zero_div, Complex.ofReal_zero, mul_zero]
  have hlog : Real.log n ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hn, h1⟩)
    exact (Real.log_pos this).ne'
  rw [← Complex.natCast_log, Complex.ofReal_div]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hlog)

/-- `log ζ_K(s) = ∑ Λ_K(n) / log n · n^{-s}`. -/
noncomputable def logDedekindZeta (s : ℂ) : ℂ := LSeries (fun n => (logZetaCoeff K n : ℂ)) s

/-- **`ζ_K = exp(log ζ_K)` for `Re s > 1`.** Both sides have logarithmic derivative `-L(Λ_K, s)`
and tend to `1` as `s → +∞`. -/
theorem dedekindZeta_eq_exp {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = exp (logDedekindZeta K s) := by
  set U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  set F : ℂ → ℂ := fun s => dedekindZeta K s * exp (-logDedekindZeta K s)
  have hζ : ∀ s ∈ U, HasDerivAt (dedekindZeta K)
      (-(LSeries (fun n => (vonMangoldtK K n : ℂ)) s * dedekindZeta K s)) s := by
    intro s hs
    have h := LSeries_hasDerivAt (abscissaOfAbsConv_idealCount_lt K hs)
    rw [← dedekindZeta_eq_LSeries] at h
    rw [LSeries_vonMangoldtK_mul_dedekindZeta K hs, neg_neg]
    exact h.differentiableAt.hasDerivAt
  have hG : ∀ s ∈ U, HasDerivAt (logDedekindZeta K)
      (-LSeries (fun n => (vonMangoldtK K n : ℂ)) s) s := by
    intro s hs
    have h := LSeries_hasDerivAt
      ((abscissaOfAbsConv_logZetaCoeff_le K).trans_lt (show ((1 : ℝ) : EReal) < s.re by
        exact_mod_cast hs))
    rwa [LSeries_congr (fun hn => logMul_logZetaCoeff K hn)] at h
  have hF : ∀ s ∈ U, HasDerivAt F 0 s := by
    intro s hs
    have h := (hζ s hs).mul ((hG s hs).neg.cexp)
    convert h using 1
    ring
  obtain ⟨c, hc⟩ := hU.exists_is_const_of_deriv_eq_zero hUc
    (fun s hs => (hF s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hF s hs).deriv)
  -- the constant is `1`
  have hlim : Tendsto (fun x : ℝ => F x) atTop (𝓝 (1 * exp (-0))) := by
    have h1 := LSeries.tendsto_atTop ((abscissaOfAbsConv_idealCount_le K).trans_lt
      (EReal.coe_lt_top 1))
    have h2 := LSeries.tendsto_atTop ((abscissaOfAbsConv_logZetaCoeff_le K).trans_lt
      (EReal.coe_lt_top 1))
    simp only [idealCount_one, Nat.cast_one, logZetaCoeff, vonMangoldtK_one, zero_div,
      Complex.ofReal_zero] at h1 h2
    exact h1.mul (h2.neg.cexp)
  have hc1 : c = 1 := by
    have : Tendsto (fun x : ℝ => F x) atTop (𝓝 c) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      exact (hc x (by simpa [U] using hx)).symm
    rw [tendsto_nhds_unique this hlim]
    simp
  have := hc s hs
  rw [hc1] at this
  calc dedekindZeta K s = F s * exp (logDedekindZeta K s) := by
        simp only [F, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [this, one_mul]

end LSeries

/-- **`ζ_K` has no zeros for `Re s > 1`**: `ζ_K = exp(log ζ_K)` there (`dedekindZeta_eq_exp`). -/
theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  rw [dedekindZeta_eq_exp K hs]
  exact Complex.exp_ne_zero _

/-- **Euler product, logarithmic derivative form**: `-ζ_K'(s)/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for
`Re s > 1`. From the convolution identity `log · a = Λ_K ⋆ a` (`log_mul_idealCount`), which gives
`L(Λ_K, s) ζ_K(s) = -ζ_K'(s)` (`LSeries_vonMangoldtK_mul_dedekindZeta`), and `ζ_K(s) ≠ 0`. -/
theorem LSeries_vonMangoldtK {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldtK K n : ℂ)) s =
      -(deriv (dedekindZeta K) s / dedekindZeta K s) := by
  have h := LSeries_vonMangoldtK_mul_dedekindZeta K hs
  have h0 := dedekindZeta_ne_zero K hs
  rw [← neg_div, ← h, mul_div_cancel_right₀ _ h0]

end Artin.Analytic
