import Artin.Analytic.Splitting
import Artin.Analytic.Continuation

/-!
# The von Mangoldt function of a number field

`Λ_K(n) = ∑_{𝔭, m ≥ 1, N𝔭^m = n} log N𝔭`, so that `ψ_K(x) = ∑_{n < x} Λ_K(n)` (`psiK_eq_sum`)
and `-ζ_K'/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for `Re s > 1` (`LSeries_vonMangoldtK`).

* `vonMangoldtK_le`: `Λ_K(n) ≤ [K : ℚ] Λ(n)`. For `n = p^j` the ideals `𝔭^m` of norm `p^j` have
  `f(𝔭) m = j`, each contributes `f(𝔭) log p`, and `∑_{𝔭 ∣ p} f(𝔭) ≤ ∑ e f = [K : ℚ]`.
* `LSeries_vonMangoldtK` and `dedekindZeta_ne_zero` are the Euler product of `ζ_K`
  (unique factorisation of ideals); both are left as `sorry` here, see their docstrings.
-/

namespace Artin.Analytic

open NumberField Finset ArithmeticFunction

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

/-- **Euler product, logarithmic derivative form**: `-ζ_K'(s)/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for
`Re s > 1`. Standard (e.g. Neukirch, *Algebraic Number Theory*, VII.5.1, or Lang, *Algebraic
Number Theory*, VIII.2): `ζ_K(s) = ∏_𝔭 (1 - N𝔭^{-s})^{-1}` by unique factorisation of ideals,
then take the logarithmic derivative term by term. Mathlib has the Euler product machinery for
`LSeries` of multiplicative functions (`LSeries_eulerProduct`), but not this instance. -/
theorem LSeries_vonMangoldtK {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldtK K n : ℂ)) s =
      -(deriv (dedekindZeta K) s / dedekindZeta K s) := by
  sorry

/-- **`ζ_K` has no zeros for `Re s > 1`**, from the Euler product (same references as
`LSeries_vonMangoldtK`): a convergent product of non-zero factors. -/
theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  sorry

end Artin.Analytic
