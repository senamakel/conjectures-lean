import Artin.Analytic.Splitting
import Artin.Analytic.Discriminant

/-!
# From `ψ_K` to `kummerCount` (blueprint steps A5 and A7)

Let `K = K_k`, `n = [K_k : ℚ]` and `θ_k(x) = ∑ log p` over the primes `p < x` counted by
`kummerCount a k x`. We show

* `psiK_sub_theta`: `0 ≤ ψ_K(x) - n θ_k(x) ≤ n log x (√x + ω(k |a|))` for natural `x ≥ 2`.
  A prime `p ∤ k a` with the Kummer condition has `n` primes of norm `p` above it
  (`split_of_kummerCond`); one without it has none (`kummerCond_iff_exists_absNorm_eq`). If
  `p² ≥ x` these are the only terms of `ψ_K(x)` above `p`. Every prime contributes at most
  `n log x` in all, and only the `≤ √x` primes with `p² < x` and the `ω(k|a|)` primes dividing
  `k a` can contribute anything else.
* `theta_bound`: with `PsiKBound K_k C` and `log |d_{K_k}| ≤ 4 n log(k |a|)` (A6),
  `|θ_k(x) - x / n| ≤ C₁ √x log x log(k x)`, with `C₁` depending only on `C` and `a`.
* `kummerCount_sub_le`: partial summation against `1 / log p`, applied to
  `θ_k(x) - θ_1(x) / n`, gives `|kummerCount a k x - kummerCount a 1 x / n| ≤ 32 C₁ √x log(kx)`.
  The `k = 1` field is `ℚ` (`kummerDegree_one`), so `θ_1(x) = x + O(√x log² x)` comes from the
  same hypothesis; this is the place of `π(x) - li(x) = O(√x log x)` (blueprint A7), and no
  separate hypothesis on `π(x)` is needed.
* `effectiveKummerChebotarev_of_kummerPsiBounds`: `KummerPsiBounds a → EffectiveKummerChebotarev a`
  for `a ≠ 0`.
-/

namespace Artin.Analytic

open Polynomial NumberField Artin.Kummer Finset

/-- The predicate of `kummerCount`. -/
def KummerPred (a : ℤ) (k p : ℕ) : Prop :=
  p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1

instance (a : ℤ) (k p : ℕ) : Decidable (KummerPred a k p) := by
  unfold KummerPred; infer_instance

/-- The primes counted by `kummerCount a k x`. -/
noncomputable def kummerSet (a : ℤ) (k x : ℕ) : Finset ℕ :=
  (range x).filter (KummerPred a k)

instance (a : ℤ) (k p : ℕ) : Decidable (KummerCond a k p) := by
  unfold KummerCond; infer_instance

lemma kummerCount_eq_card (a : ℤ) (k x : ℕ) : kummerCount a k x = (kummerSet a k x).card := by
  unfold kummerCount kummerSet KummerPred
  congr 1

/-- The weighted count `θ_k(x) = ∑_{p ∈ kummerSet a k x} log p`. -/
noncomputable def kummerTheta (a : ℤ) (k x : ℕ) : ℝ :=
  ∑ p ∈ kummerSet a k x, Real.log p

lemma not_dvd_of_kummerPred {a : ℤ} {k p : ℕ} (h : KummerPred a k p) : ¬ p ∣ k := by
  intro hpk
  have h1 := dvd_trans hpk h.2.2.1
  have h2 : 0 < p - 1 := Nat.sub_pos_of_lt h.1.one_lt
  exact absurd (Nat.le_of_dvd h2 h1) (by have := h.1.one_lt; omega)

lemma kummerPred_iff {a : ℤ} {k p : ℕ} (hp : p.Prime) (hpa : ¬ (p : ℤ) ∣ a) :
    KummerPred a k p ↔ KummerCond a k p := by
  simp [KummerPred, KummerCond, hp, hpa]

/-! ### The terms of `ψ_K` above one prime -/

section PerPrime

variable {K : Type*} [Field K] [NumberField K]

/-- The terms of `ψ_K(x)` above the rational prime `p`. -/
noncomputable def psiTerm (K : Type*) [Field K] [NumberField K] (x : ℝ) (p : ℕ) : ℝ :=
  ∑ P ∈ primesAbove K p, ∑ m ∈ Icc 1 ⌊x⌋₊,
    if ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x then Real.log (Ideal.absNorm P) else 0

lemma psiK_eq (x : ℝ) : psiK K x = ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, psiTerm K x p :=
  rfl

/-- For `q ≥ 2`, `∑_{m ≥ 1, q^m < x} log q ≤ log x`. -/
lemma sum_log_le {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx : 1 ≤ x) (X : ℕ) :
    ∑ m ∈ Icc 1 X, (if (q : ℝ) ^ m < x then Real.log q else 0) ≤ Real.log x := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  set S := (Icc 1 X).filter fun m => (q : ℝ) ^ m < x
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h, hlogx]
  set M := S.max' h
  have hMS : M ∈ S := S.max'_mem h
  have hM : (q : ℝ) ^ M < x := (mem_filter.1 hMS).2
  have hcard : S.card ≤ M := by
    calc S.card ≤ (Icc 1 M).card := card_le_card fun m hm =>
          mem_Icc.2 ⟨(mem_Icc.1 (mem_filter.1 hm).1).1, S.le_max' m hm⟩
      _ = M := by simp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  calc (S.card : ℝ) * Real.log q ≤ M * Real.log q := by gcongr
    _ = Real.log ((q : ℝ) ^ M) := by rw [Real.log_pow]
    _ ≤ Real.log x := Real.log_le_log (pow_pos hq0 _) hM.le

lemma psiTerm_nonneg (x : ℝ) (p : ℕ) : 0 ≤ psiTerm K x p := by
  unfold psiTerm
  refine sum_nonneg fun P _ => sum_nonneg fun m _ => ?_
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

/-- Every prime contributes at most `n log x`. -/
lemma psiTerm_le {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 ≤ x) :
    psiTerm K x p ≤ Module.finrank ℚ K * Real.log x := by
  unfold psiTerm
  calc _ ≤ ∑ P ∈ primesAbove K p, Real.log x := sum_le_sum fun P hP =>
        sum_log_le ((hp.two_le).trans (le_absNorm hp hP)) hx _
    _ = (primesAbove K p).card * Real.log x := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        · exact Real.log_nonneg hx
        · exact_mod_cast card_primesAbove_le hp

/-- The term `m = 1` of the primes of norm `p`. -/
lemma psiTerm_ge {p : ℕ} {x : ℝ} (hx : 1 ≤ x) :
    ((primesAbove K p).filter fun P => Ideal.absNorm P = p).card *
      (if (p : ℝ) < x then Real.log p else 0) ≤ psiTerm K x p := by
  unfold psiTerm
  have h1 : 1 ∈ Icc 1 ⌊x⌋₊ := mem_Icc.2 ⟨le_rfl, Nat.le_floor (by simpa using hx)⟩
  rw [← nsmul_eq_mul, ← sum_const]
  calc _ = ∑ P ∈ (primesAbove K p).filter (fun P => Ideal.absNorm P = p),
        (if ((Ideal.absNorm P : ℕ) : ℝ) ^ 1 < x then Real.log (Ideal.absNorm P) else 0) := by
        refine sum_congr rfl fun P hP => ?_
        rw [(mem_filter.1 hP).2, pow_one]
    _ ≤ ∑ P ∈ (primesAbove K p).filter (fun P => Ideal.absNorm P = p), ∑ m ∈ Icc 1 ⌊x⌋₊,
        (if ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x then Real.log (Ideal.absNorm P) else 0) := by
        refine sum_le_sum fun P _ => ?_
        refine single_le_sum (f := fun m => if ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x then
          Real.log (Ideal.absNorm P) else 0) (fun m _ => ?_) h1
        split_ifs
        · exact Real.log_natCast_nonneg _
        · exact le_rfl
    _ ≤ _ := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun P _ _ => ?_
        refine sum_nonneg fun m _ => ?_
        split_ifs
        · exact Real.log_natCast_nonneg _
        · exact le_rfl

/-- If `p² ≥ x`, only the primes of norm `p`, with `m = 1`, contribute. -/
lemma psiTerm_eq {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 ≤ x) (hpx : x ≤ (p : ℝ) ^ 2) :
    psiTerm K x p = ((primesAbove K p).filter fun P => Ideal.absNorm P = p).card *
      (if (p : ℝ) < x then Real.log p else 0) := by
  unfold psiTerm
  have h1 : 1 ∈ Icc 1 ⌊x⌋₊ := mem_Icc.2 ⟨le_rfl, Nat.le_floor (by simpa using hx)⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  rw [← nsmul_eq_mul, ← sum_const, ← sum_filter_add_sum_filter_not (primesAbove K p)
    (fun P => Ideal.absNorm P = p)]
  have hzero : ∑ P ∈ (primesAbove K p).filter (fun P => ¬ Ideal.absNorm P = p),
      ∑ m ∈ Icc 1 ⌊x⌋₊, (if ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x then
        Real.log (Ideal.absNorm P) else 0) = 0 := by
    refine sum_eq_zero fun P hP => sum_eq_zero fun m hm => ?_
    obtain ⟨hP, hne⟩ := mem_filter.1 hP
    have hf : 2 ≤ P.inertiaDeg ℤ := by
      have := one_le_inertiaDeg hp hP
      by_contra h
      have h1' : P.inertiaDeg ℤ = 1 := by omega
      apply hne; rw [← absNorm_eq_pow hp hP, h1', pow_one]
    have hN : (p : ℝ) ^ 2 ≤ ((Ideal.absNorm P : ℕ) : ℝ) := by
      rw [← absNorm_eq_pow hp hP]; push_cast
      exact pow_le_pow_right₀ hp1 hf
    have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm P : ℕ) : ℝ) := hp1.trans (by
      exact_mod_cast le_absNorm hp hP)
    have hm1 : 1 ≤ m := (mem_Icc.1 hm).1
    refine ite_eq_right_iff.2 fun hlt => absurd hlt (not_lt.2 ?_)
    calc x ≤ (p : ℝ) ^ 2 := hpx
      _ ≤ _ := hN
      _ ≤ _ := le_self_pow₀ hN1 (by omega)
  rw [hzero, add_zero]
  refine sum_congr rfl fun P hP => ?_
  rw [(mem_filter.1 hP).2]
  rw [sum_eq_single_of_mem 1 h1 fun m hm hm1 => ?_, pow_one]
  refine ite_eq_right_iff.2 fun hlt => absurd hlt (not_lt.2 ?_)
  have hm2 : 2 ≤ m := by have := (mem_Icc.1 hm).1; omega
  exact hpx.trans (pow_le_pow_right₀ hp1 hm2)

end PerPrime

/-! ### `ψ_K` against `θ_k` for the Kummer field -/

section KField

variable {a : ℤ} {k : ℕ}

local notation "𝓚" => KField a k

lemma finrank_eq_kummerDegree : Module.finrank ℚ 𝓚 = kummerDegree a k := rfl

/-- For `p ∤ k a`, the number of primes of norm `p` above `p` is `n` or `0`. -/
lemma card_filter_absNorm_eq (ha : a ≠ 0) (hk : k ≠ 0) {p : ℕ} (hp : p.Prime) (hpk : ¬ p ∣ k)
    (hpa : ¬ (p : ℤ) ∣ a) :
    ((primesAbove 𝓚 p).filter fun P => Ideal.absNorm P = p).card =
      if KummerCond a k p then kummerDegree a k else 0 := by
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := split_of_kummerCond ha hk hp hpk hpa hc
    rw [filter_true_of_mem h1, h2]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro P hP hN
    exact hc ((kummerCond_iff_exists_absNorm_eq ha hk hp hpk hpa).2 ⟨P, hP, hN⟩)

/-- The main term of `ψ_K(x)` above `p`: `n log p` if `p` is counted by `kummerCount`. -/
noncomputable def mainTerm (a : ℤ) (k x p : ℕ) : ℝ :=
  kummerDegree a k * (if KummerPred a k p ∧ p < x then Real.log p else 0)

lemma mainTerm_nonneg (x p : ℕ) : 0 ≤ mainTerm a k x p := by
  unfold mainTerm
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

lemma mainTerm_le_psiTerm (ha : a ≠ 0) (hk : k ≠ 0) {x : ℕ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p.Prime) : mainTerm a k x p ≤ psiTerm 𝓚 x p := by
  unfold mainTerm
  by_cases h : KummerPred a k p ∧ p < x
  · have hpk := not_dvd_of_kummerPred h.1
    have hpa := h.1.2.1
    have hc := (kummerPred_iff hp hpa).1 h.1
    have := psiTerm_ge (K := 𝓚) (p := p) (x := x) (by exact_mod_cast hx)
    have hlt : (p : ℝ) < x := by exact_mod_cast h.2
    rw [card_filter_absNorm_eq ha hk hp hpk hpa] at this
    simp only [hc, hlt, h, ↓reduceIte, and_self] at this ⊢
    exact this
  · simp only [h, ↓reduceIte, mul_zero]
    exact psiTerm_nonneg _ _

lemma psiTerm_le_mainTerm (ha : a ≠ 0) (hk : k ≠ 0) {x : ℕ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p.Prime) : psiTerm 𝓚 x p ≤ mainTerm a k x p +
      (if p ∣ k * a.natAbs ∨ p * p < x then kummerDegree a k * Real.log x else 0) := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  split_ifs with hbad
  · exact (psiTerm_le hp hx').trans (le_add_of_nonneg_left (mainTerm_nonneg _ _))
  · push Not at hbad
    obtain ⟨hdvd, hpx⟩ := hbad
    have hpk : ¬ p ∣ k := fun h => hdvd (dvd_mul_of_dvd_left h _)
    have hpa : ¬ (p : ℤ) ∣ a := fun h => hdvd (dvd_mul_of_dvd_right (Int.natCast_dvd.1 h) _)
    rw [add_zero, psiTerm_eq hp hx' (by rw [sq]; exact_mod_cast hpx),
      card_filter_absNorm_eq ha hk hp hpk hpa]
    unfold mainTerm
    have hiff := kummerPred_iff hp hpa (k := k)
    by_cases hc : KummerPred a k p
    · have hc' := hiff.1 hc
      by_cases hlt : p < x
      · simp [hc, hc', hlt, show (p : ℝ) < x by exact_mod_cast hlt]
      · simp [hc, hc', hlt, show ¬ (p : ℝ) < x by exact_mod_cast hlt]
    · have hc' : ¬ KummerCond a k p := fun h => hc (hiff.2 h)
      simp [hc, hc']

lemma sum_mainTerm (x : ℕ) :
    ∑ p ∈ (range (x + 1)).filter Nat.Prime, mainTerm a k x p = kummerDegree a k * kummerTheta a k x := by
  unfold mainTerm kummerTheta kummerSet
  rw [← mul_sum, sum_filter, sum_filter, sum_range_succ]
  congr 1
  rw [show (if x.Prime then (if KummerPred a k x ∧ x < x then Real.log x else 0) else 0) = 0 by
    simp, add_zero]
  refine sum_congr rfl fun p hp => ?_
  have hpx := mem_range.1 hp
  by_cases h : KummerPred a k p
  · simp [h, h.1, hpx]
  · by_cases h' : p.Prime <;> simp [h, h']

/-- `ω(m) ≤ 2 log m`. -/
lemma card_primeFactors_le_log {m : ℕ} (hm : m ≠ 0) :
    (m.primeFactors.card : ℝ) ≤ 2 * Real.log m := by
  have h2 : 2 ^ m.primeFactors.card ≤ m := by
    calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
          pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)
  have h2' : (2 : ℝ) ^ m.primeFactors.card ≤ m := by exact_mod_cast h2
  have := Real.log_le_log (by positivity) h2'
  rw [Real.log_pow] at this
  have hlog2 := Real.log_two_gt_d9
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  nlinarith

/-- The primes `p ≤ x` with `p ∣ m` or `p² < x` number at most `ω(m) + √x`. -/
lemma card_bad_le {m : ℕ} (hm : m ≠ 0) (x : ℕ) :
    ((((range (x + 1)).filter Nat.Prime).filter fun p => p ∣ m ∨ p * p < x).card : ℝ) ≤
      2 * Real.log m + Real.sqrt x := by
  have hsub : (((range (x + 1)).filter Nat.Prime).filter fun p => p ∣ m ∨ p * p < x) ⊆
      m.primeFactors ∪ Icc 1 (Nat.sqrt x) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨⟨-, hpp⟩, h⟩ := hp
    rcases h with h | h
    · exact mem_union_left _ (Nat.mem_primeFactors.2 ⟨hpp, h, hm⟩)
    · exact mem_union_right _ (mem_Icc.2 ⟨hpp.one_lt.le, Nat.le_sqrt.2 h.le⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  calc _ ≤ ((m.primeFactors.card + Nat.sqrt x : ℕ) : ℝ) := by exact_mod_cast this
    _ ≤ _ := by
      push_cast
      exact add_le_add (card_primeFactors_le_log hm) Real.nat_sqrt_le_real_sqrt

/-- **A5, counting.** `0 ≤ ψ_K(x) - n θ_k(x) ≤ n log x (2 log(k |a|) + √x)`. -/
theorem psiK_sub_theta (ha : a ≠ 0) (hk : k ≠ 0) {x : ℕ} (hx : 1 ≤ x) :
    0 ≤ psiK 𝓚 x - kummerDegree a k * kummerTheta a k x ∧
      psiK 𝓚 x - kummerDegree a k * kummerTheta a k x ≤
        kummerDegree a k * Real.log x * (2 * Real.log (k * a.natAbs) + Real.sqrt x) := by
  rw [psiK_eq, Nat.floor_natCast, ← sum_mainTerm, ← sum_sub_distrib]
  refine ⟨sum_nonneg fun p hp => sub_nonneg.2 (mainTerm_le_psiTerm ha hk hx (mem_filter.1 hp).2),
    ?_⟩
  have hm : k * a.natAbs ≠ 0 := Nat.mul_ne_zero hk (Int.natAbs_ne_zero.2 ha)
  calc _ ≤ ∑ p ∈ (range (x + 1)).filter Nat.Prime,
        (if p ∣ k * a.natAbs ∨ p * p < x then kummerDegree a k * Real.log x else 0) :=
        sum_le_sum fun p hp => by
          have := psiTerm_le_mainTerm ha hk hx (mem_filter.1 hp).2 (a := a) (k := k)
          linarith
    _ = (((range (x + 1)).filter Nat.Prime).filter fun p => p ∣ k * a.natAbs ∨ p * p < x).card *
          (kummerDegree a k * Real.log x) := by rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.log ((k * a.natAbs : ℕ) : ℝ) + Real.sqrt x) * (kummerDegree a k * Real.log x) := by
        gcongr
        exact card_bad_le hm x
    _ = _ := by push_cast; ring

/-- The constant of `theta_bound`. -/
noncomputable def thetaConst (C : ℝ) (a : ℤ) : ℝ :=
  max C 0 * (5 + 8 * Real.log |(a : ℝ)|) + 4 + 4 * Real.log |(a : ℝ)|

lemma one_le_abs_cast (ha : a ≠ 0) : (1 : ℝ) ≤ |(a : ℝ)| := by
  have : ((1 : ℤ) : ℝ) ≤ ((|a| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs ha
  simpa using this

lemma thetaConst_nonneg (C : ℝ) (ha : a ≠ 0) : 0 ≤ thetaConst C a := by
  have := Real.log_nonneg (one_le_abs_cast ha)
  unfold thetaConst
  have := le_max_right C 0
  positivity

/-- **θ from ψ.** `PsiKBound` for `K_k` gives `|θ_k(x) - x / n| ≤ C₁ √x log x log(k x)`. -/
theorem theta_bound (ha : a ≠ 0) (hk : k ≠ 0) {C : ℝ} (hψ : PsiKBound 𝓚 C) {x : ℕ}
    (hx : 2 ≤ x) :
    |kummerTheta a k x - x / kummerDegree a k| ≤
      thetaConst C a * Real.sqrt x * Real.log x * Real.log (k * x) := by
  set n : ℝ := ((kummerDegree a k : ℕ) : ℝ) with hn_def
  set X : ℝ := (x : ℝ)
  set C' : ℝ := max C 0
  set La := Real.log |(a : ℝ)|
  set L := Real.log (k * a.natAbs : ℝ)
  set ℓ := Real.log X
  set lam := Real.log (k * X)
  have hn : 1 ≤ n := by
    rw [hn_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := 𝓚)
  have hX : (2 : ℝ) ≤ X := by simp only [X]; exact_mod_cast hx
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hlog2 := Real.log_two_gt_d9
  have hnat : ((a.natAbs : ℕ) : ℝ) = |(a : ℝ)| := by simp
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hX
  have hℓlam : ℓ ≤ lam := Real.log_le_log (by linarith) (by nlinarith)
  have hLa : 0 ≤ La := Real.log_nonneg (one_le_abs_cast ha)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hlogk' : Real.log k ≤ lam := Real.log_le_log (by linarith) (by nlinarith)
  have hL : L = Real.log k + La := by
    simp only [L, La, hnat]
    rw [Real.log_mul (by positivity) (by simpa using ha)]
  have hsqrt : 1 ≤ Real.sqrt X := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  -- the analytic input
  have hψx := hψ X hX
  have hd := log_abs_discr_le ha hk
  rw [← hnat] at hd
  change Real.log |(discr 𝓚 : ℝ)| ≤ 4 * n * L at hd
  have hd0 : 0 ≤ Real.log |(discr 𝓚 : ℝ)| := by
    apply Real.log_nonneg
    have := discr_ne_zero 𝓚
    have : (1 : ℤ) ≤ |discr 𝓚| := Int.one_le_abs this
    exact_mod_cast this
  rw [finrank_eq_kummerDegree] at hψx
  have hT : |psiK 𝓚 X - X| ≤ C' * (n * (Real.sqrt X * (4 * L + ℓ) * ℓ)) := by
    refine hψx.trans ?_
    have h0 : 0 ≤ Real.sqrt X * (Real.log |(discr 𝓚 : ℝ)| + n * ℓ) * ℓ := by
      have : 0 ≤ ℓ := by linarith
      positivity
    calc C * Real.sqrt X * (Real.log |(discr 𝓚 : ℝ)| + n * ℓ) * ℓ
        = C * (Real.sqrt X * (Real.log |(discr 𝓚 : ℝ)| + n * ℓ) * ℓ) := by ring
      _ ≤ C' * (Real.sqrt X * (Real.log |(discr 𝓚 : ℝ)| + n * ℓ) * ℓ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ C' * (Real.sqrt X * (4 * n * L + n * ℓ) * ℓ) := by
          gcongr
      _ = _ := by ring
  obtain ⟨h1, h2⟩ := psiK_sub_theta ha hk (x := x) (by omega)
  -- combine
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hmain : |n * kummerTheta a k x - X| ≤
      n * (Real.sqrt X * ℓ * (C' * (4 * L + ℓ)) + ℓ * (2 * L + Real.sqrt X)) := by
    have : |n * kummerTheta a k x - X| ≤ |psiK 𝓚 X - X| + (psiK 𝓚 X - n * kummerTheta a k x) := by
      rw [abs_le]; constructor
      · have := neg_abs_le (psiK 𝓚 X - X); linarith
      · have := le_abs_self (psiK 𝓚 X - X); linarith
    refine this.trans ?_
    have h2' : psiK 𝓚 X - n * kummerTheta a k x ≤ n * (ℓ * (2 * L + Real.sqrt X)) := by
      refine h2.trans (le_of_eq ?_)
      ring
    have hT' : C' * (n * (Real.sqrt X * (4 * L + ℓ) * ℓ)) =
        n * (Real.sqrt X * ℓ * (C' * (4 * L + ℓ))) := by ring
    linarith
  have hdiv : |kummerTheta a k x - X / n| = |n * kummerTheta a k x - X| / n := by
    rw [← abs_of_pos (by linarith : (0 : ℝ) < n), ← abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < n)]
    congr 1
    field_simp
  rw [hdiv, div_le_iff₀ (by linarith)]
  refine hmain.trans ?_
  rw [mul_comm _ n]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  -- now the bracket
  have hlam0 : 0 ≤ lam := by linarith
  have hLlam : L ≤ (1 + 2 * La) * lam := by
    rw [hL]; nlinarith
  have hb1 : 4 * L + ℓ ≤ (5 + 8 * La) * lam := by nlinarith
  have hb2 : 2 * L + Real.sqrt X ≤ (4 + 4 * La) * lam * Real.sqrt X := by
    have : 2 * L ≤ 2 * (1 + 2 * La) * lam * Real.sqrt X := by
      have : 0 ≤ (1 + 2 * La) * lam := by positivity
      nlinarith
    nlinarith
  have hC' : 0 ≤ C' := le_max_right _ _
  have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  calc Real.sqrt X * ℓ * (C' * (4 * L + ℓ)) + ℓ * (2 * L + Real.sqrt X)
      ≤ Real.sqrt X * ℓ * (C' * ((5 + 8 * La) * lam)) +
          ℓ * ((4 + 4 * La) * lam * Real.sqrt X) := by
        gcongr
    _ = thetaConst C a * Real.sqrt X * ℓ * lam := by
        unfold thetaConst; ring

end KField

/-! ### Partial summation -/

section Abel

/-- `∑_{i ≤ N} 1 / √i ≤ 2 √N` (the `i = 0` term is `0`). -/
lemma sum_inv_sqrt_le (N : ℕ) : ∑ i ∈ range (N + 1), 1 / Real.sqrt i ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have ht : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hst : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ 2 = Real.sqrt N ^ 2 + 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : 1 / Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) := by
      rw [div_le_iff₀ ht]
      nlinarith [sq_nonneg (Real.sqrt N - Real.sqrt ((N + 1 : ℕ) : ℝ))]
    linarith

/-- The weight `1 / log(max i 2)`. -/
noncomputable def logWeight (i : ℕ) : ℝ := 1 / Real.log (max (i : ℝ) 2)

lemma logWeight_of_two_le {i : ℕ} (hi : 2 ≤ i) : logWeight i = 1 / Real.log i := by
  unfold logWeight
  rw [max_eq_left (by exact_mod_cast hi)]

lemma logWeight_diff_le {i : ℕ} (hi : 2 ≤ i) :
    0 ≤ logWeight i - logWeight (i + 1) ∧
      (logWeight i - logWeight (i + 1)) * (Real.sqrt (i + 1 : ℕ) * Real.log (i + 1 : ℕ)) ≤
        3 / Real.sqrt i := by
  rw [logWeight_of_two_le hi, logWeight_of_two_le (by omega)]
  have hi' : (2 : ℝ) ≤ i := by exact_mod_cast hi
  have hlog2 := Real.log_two_gt_d9
  have hli : Real.log 2 ≤ Real.log i := Real.log_le_log (by norm_num) hi'
  have hli1 : Real.log i ≤ Real.log (i + 1 : ℕ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  have hD : Real.log (i + 1 : ℕ) - Real.log i ≤ 1 / i := by
    rw [← Real.log_div (by positivity) (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    push_cast; field_simp; ring
  have hpos : 0 < Real.log i := by linarith
  have hpos1 : 0 < Real.log (i + 1 : ℕ) := by linarith
  have hsi : 0 < Real.sqrt i := Real.sqrt_pos.2 (by linarith)
  have hsqrt : Real.sqrt (i + 1 : ℕ) ≤ 2 * Real.sqrt i := by
    rw [show (2 : ℝ) * Real.sqrt i = Real.sqrt (4 * i) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  constructor
  · rw [sub_nonneg]; exact one_div_le_one_div_of_le hpos hli1
  · have heq : (1 / Real.log i - 1 / Real.log (i + 1 : ℕ)) *
        (Real.sqrt (i + 1 : ℕ) * Real.log (i + 1 : ℕ)) =
        (Real.log (i + 1 : ℕ) - Real.log i) * Real.sqrt (i + 1 : ℕ) / Real.log i := by
      field_simp
    rw [heq, div_le_div_iff₀ hpos hsi]
    have hD0 : 0 ≤ Real.log (i + 1 : ℕ) - Real.log i := by linarith
    have hii : Real.sqrt i * Real.sqrt i = i := Real.mul_self_sqrt (by linarith)
    calc (Real.log (i + 1 : ℕ) - Real.log i) * Real.sqrt (i + 1 : ℕ) * Real.sqrt i
        ≤ (1 / i) * (2 * Real.sqrt i) * Real.sqrt i := by gcongr
      _ = 2 := by rw [mul_assoc, mul_assoc, hii]; field_simp
      _ ≤ 3 * Real.log i := by linarith

/-- **Partial summation.** If `A(t) = ∑_{m < t} u_m log m` satisfies
`|A(t)| ≤ B √t log t Λ` for `2 ≤ t ≤ x`, then `|∑_{m < x} u_m| ≤ 8 B Λ √x`. -/
lemma abs_sum_le_of_abs_sum_log_le (u : ℕ → ℝ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) {x : ℕ}
    (hx : 2 ≤ x) {B Λ : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hA : ∀ t, 2 ≤ t → t ≤ x →
      |∑ m ∈ range t, u m * Real.log m| ≤ B * Real.sqrt t * Real.log t * Λ) :
    |∑ m ∈ range x, u m| ≤ 8 * B * Λ * Real.sqrt x := by
  set g : ℕ → ℝ := fun m => u m * Real.log m
  have hsum : ∑ m ∈ range x, u m = ∑ m ∈ range x, logWeight m • g m := by
    refine sum_congr rfl fun m _ => ?_
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> simp [g, hu0, hu1]
    · rw [logWeight_of_two_le h, smul_eq_mul]
      have : Real.log m ≠ 0 := (Real.log_pos (by exact_mod_cast h)).ne'
      simp only [g]; field_simp
  rw [hsum, sum_range_by_parts]
  have hlog2 := Real.log_two_gt_d9
  have hX : (2 : ℝ) ≤ x := by exact_mod_cast hx
  -- the boundary term
  have hfirst : |logWeight (x - 1) • ∑ i ∈ range x, g i| ≤ 2 * B * Λ * Real.sqrt x := by
    set m₀ : ℝ := max ((x - 1 : ℕ) : ℝ) 2
    have hm₀ : (2 : ℝ) ≤ m₀ := le_max_right _ _
    have hm₀' : ((x - 1 : ℕ) : ℝ) ≤ m₀ := le_max_left _ _
    have hcast : ((x - 1 : ℕ) : ℝ) = x - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hxm : (x : ℝ) ≤ m₀ ^ 2 := by nlinarith
    have hlogm : Real.log x ≤ 2 * Real.log m₀ := by
      have := Real.log_le_log (by linarith) hxm
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlm : 0 < Real.log m₀ := Real.log_pos (by linarith)
    rw [smul_eq_mul, abs_mul]
    have hw : |logWeight (x - 1)| = 1 / Real.log m₀ := by
      unfold logWeight; rw [abs_of_pos (by positivity)]
    rw [hw]
    have := hA x hx le_rfl
    calc 1 / Real.log m₀ * |∑ i ∈ range x, g i|
        ≤ 1 / Real.log m₀ * (B * Real.sqrt x * Real.log x * Λ) := by gcongr
      _ = B * Λ * Real.sqrt x * (Real.log x / Real.log m₀) := by ring
      _ ≤ B * Λ * Real.sqrt x * 2 := by
          gcongr
          rw [div_le_iff₀ hlm]; linarith
      _ = _ := by ring
  -- the other terms
  have hterm : ∀ i ∈ range (x - 1), |(logWeight (i + 1) - logWeight i) •
      ∑ j ∈ range (i + 1), g j| ≤ 3 * B * Λ * (1 / Real.sqrt i) := by
    intro i hi
    have hi' := mem_range.1 hi
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · simp [g, hu0]
      · have : logWeight 2 - logWeight 1 = 0 := by
          unfold logWeight; norm_num
        rw [this, zero_smul, abs_zero]; positivity
    · obtain ⟨hd0, hd⟩ := logWeight_diff_le h
      rw [smul_eq_mul, abs_mul, abs_sub_comm, abs_of_nonneg hd0]
      have hA' := hA (i + 1) (by omega) (by omega)
      calc (logWeight i - logWeight (i + 1)) * |∑ j ∈ range (i + 1), g j|
          ≤ (logWeight i - logWeight (i + 1)) *
              (B * Real.sqrt (i + 1 : ℕ) * Real.log (i + 1 : ℕ) * Λ) := by gcongr
        _ = B * Λ * ((logWeight i - logWeight (i + 1)) *
              (Real.sqrt (i + 1 : ℕ) * Real.log (i + 1 : ℕ))) := by ring
        _ ≤ B * Λ * (3 / Real.sqrt i) := by gcongr
        _ = _ := by ring
  have hrest : |∑ i ∈ range (x - 1), (logWeight (i + 1) - logWeight i) •
      ∑ j ∈ range (i + 1), g j| ≤ 6 * B * Λ * Real.sqrt x := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have h1 : ∑ i ∈ range (x - 1), 1 / Real.sqrt i ≤ ∑ i ∈ range (x - 1 + 1), 1 / Real.sqrt i :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun _ _ _ => by positivity
    have h2 := sum_inv_sqrt_le (x - 1)
    have h3 : Real.sqrt ((x - 1 : ℕ) : ℝ) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le x 1)
    have : 0 ≤ 3 * B * Λ := by positivity
    calc 3 * B * Λ * ∑ i ∈ range (x - 1), 1 / Real.sqrt i ≤ 3 * B * Λ * (2 * Real.sqrt x) := by
          gcongr; linarith
      _ = _ := by ring
  calc _ ≤ |logWeight (x - 1) • ∑ i ∈ range x, g i| + |∑ i ∈ range (x - 1),
        (logWeight (i + 1) - logWeight i) • ∑ j ∈ range (i + 1), g j| := abs_sub _ _
    _ ≤ _ := by linarith

end Abel

end Artin.Analytic
