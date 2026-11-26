import Mertens.Statement2
import Mertens.Uniform
import Mertens.Main

/-!
# The summatory Liouville function `L(x) = O(x^{1/2+ε})` under RH

`λ * 1 = 1_{squares}` (both sides are multiplicative, and at `p^i` both are `1` if `i` is even
and `0` otherwise), so `λ = 1_{squares} * μ` and
`L(N) = ∑_{d² ≤ N} M(⌊N/d²⌋)`. With `|M(n)| ≤ K (n+1)^β` (`β = 1/2 + ε`) this gives
`|L(N)| ≤ K 2^β N^β ∑_d d^{-2β}`, and `2β > 1`.
-/

namespace Mertens

open Filter Finset Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.Omega

/-- The indicator of the nonzero squares, as an arithmetic function. -/
noncomputable def sqInd : ArithmeticFunction ℤ where
  toFun n := by classical exact if n ≠ 0 ∧ IsSquare n then 1 else 0
  map_zero' := by simp

lemma sqInd_apply (n : ℕ) [Decidable (n ≠ 0 ∧ IsSquare n)] :
    sqInd n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := by
  simp only [sqInd, coe_mk]
  congr

lemma isSquare_mul_iff_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  simp only [Nat.isSquare_iff_even_factorization, Nat.factorization_mul hm hn,
    Finsupp.add_apply]
  constructor
  · intro H
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · by_cases hpn : p ∣ n
      · have : ¬ p ∣ m := fun hpm => hp.not_dvd_one (h.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn)
        rw [Nat.factorization_eq_zero_of_not_dvd this]; exact ⟨0, rfl⟩
      · have := H p hp
        rwa [Nat.factorization_eq_zero_of_not_dvd hpn, add_zero] at this
    · by_cases hpm : p ∣ m
      · have : ¬ p ∣ n := fun hpn => hp.not_dvd_one (h.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn)
        rw [Nat.factorization_eq_zero_of_not_dvd this]; exact ⟨0, rfl⟩
      · have := H p hp
        rwa [Nat.factorization_eq_zero_of_not_dvd hpm, zero_add] at this
  · rintro ⟨H1, H2⟩ p hp
    exact (H1 p hp).add (H2 p hp)

lemma isMultiplicative_sqInd : IsMultiplicative sqInd := by
  classical
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [sqInd_apply], fun {m n} hm hn h => ?_⟩
  simp only [sqInd_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    isSquare_mul_iff_of_coprime hm hn h]
  split_ifs <;> simp_all

lemma isSquare_prime_pow_iff {p i : ℕ} (hp : p.Prime) : IsSquare (p ^ i) ↔ Even i := by
  constructor
  · intro H
    have := Nat.isSquare_iff_even_factorization.1 H p hp
    rwa [hp.factorization_pow, Finsupp.single_eq_same] at this
  · rintro ⟨k, rfl⟩
    exact ⟨p ^ k, by rw [pow_add]⟩

lemma sum_neg_one_pow (i : ℕ) :
    ∑ j ∈ range (i + 1), (-1 : ℤ) ^ j = if Even i then 1 else 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd i with h | h
    · have h' : ¬ Even (i + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', pow_succ, h.neg_one_pow]; ring
    · have h' : Even (i + 1) := h.add_one
      have hn : ¬ Even i := Nat.not_even_iff_odd.2 h
      rw [if_neg hn, if_pos h', pow_succ, h.neg_one_pow]; ring

lemma liouville_mul_zeta : liouville * (ζ : ArithmeticFunction ℤ) = sqInd := by
  classical
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouville.mul isMultiplicative_zeta.natCast) _ isMultiplicative_sqInd).2
    fun p i hp => ?_
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sqInd_apply]
  have : ∀ j ∈ range (i + 1), liouville (p ^ j) = (-1) ^ j := fun j _ => by
    rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
  rw [sum_congr rfl this, sum_neg_one_pow]
  by_cases he : Even i <;> simp [he, isSquare_prime_pow_iff hp, hp.ne_zero]

lemma liouville_eq_sqInd_mul_moebius : liouville = sqInd * (μ : ArithmeticFunction ℤ) := by
  rw [← liouville_mul_zeta, mul_assoc, coe_zeta_mul_moebius, mul_one]

lemma Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext n; simp only [mem_Icc, mem_Ioc]; omega

lemma liouvilleSum_nat (N : ℕ) :
    (liouvilleSum N : ℝ) = ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ) := by
  have h := sum_Ioc_mul_eq_sum_sum sqInd (μ : ArithmeticFunction ℤ) N
  rw [← liouville_eq_sqInd_mul_moebius] at h
  rw [liouvilleSum, Nat.floor_natCast, Icc_one_eq_Ioc_zero, h]
  push_cast
  refine sum_congr rfl fun n _ => ?_
  rw [mertens, Nat.floor_natCast, Icc_one_eq_Ioc_zero]
  push_cast
  rfl

lemma sum_sqInd_rpow_le {β : ℝ} (hβ : 1 / 2 < β) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (n : ℝ) ^ (-β) ≤ ∑' d : ℕ, (d : ℝ) ^ (-(2 * β)) := by
  classical
  have hsum : Summable fun d : ℕ => (d : ℝ) ^ (-(2 * β)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have hfilt : ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (n : ℝ) ^ (-β) =
      ∑ n ∈ (Ioc 0 N).filter IsSquare, (n : ℝ) ^ (-β) := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by simp at hn; omega
    rw [sqInd_apply]
    by_cases hs : IsSquare n <;> simp [hs, hn0]
  rw [hfilt]
  have hsub : (Ioc 0 N).filter IsSquare ⊆ (Ioc 0 N).image fun d : ℕ => d * d := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨h0, hN⟩, r, rfl⟩ := hn
    refine mem_image.2 ⟨r, mem_Ioc.2 ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos r with rfl | h
      · simp at h0
      · exact h
    · exact le_trans (Nat.le_mul_self r) hN
  calc ∑ n ∈ (Ioc 0 N).filter IsSquare, (n : ℝ) ^ (-β)
      ≤ ∑ n ∈ (Ioc 0 N).image (fun d : ℕ => d * d), (n : ℝ) ^ (-β) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ d ∈ Ioc 0 N, ((d * d : ℕ) : ℝ) ^ (-β) :=
        sum_image_le_of_nonneg fun _ _ => by positivity
    _ = ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-(2 * β)) := by
        refine sum_congr rfl fun d _ => ?_
        push_cast
        rw [show -(2 * β) = -β + -β by ring, Real.rpow_add' (by positivity) (by linarith),
          Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ ∑' d : ℕ, (d : ℝ) ^ (-(2 * β)) :=
        hsum.sum_le_tsum _ fun _ _ => by positivity

/-- `|L(N)| ≤ K' N^β` for every `N`, from the Mertens bound. -/
theorem abs_liouvilleSum_nat_le (hMB : MertensBound) {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ N : ℕ, |(liouvilleSum N : ℝ)| ≤ K' * (N : ℝ) ^ β := by
  obtain ⟨K, hK0, hK⟩ := abs_mertens_le_of_mertensBound hMB hβ
  have hβ0 : 0 ≤ β := by linarith
  set Z : ℝ := ∑' d : ℕ, (d : ℝ) ^ (-(2 * β))
  refine ⟨K * 2 ^ β * Z, by positivity, fun N => ?_⟩
  rw [liouvilleSum_nat]
  have hterm : ∀ n ∈ Ioc 0 N, |(sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ)| ≤
      K * 2 ^ β * (N : ℝ) ^ β * ((sqInd n : ℝ) * (n : ℝ) ^ (-β)) := by
    classical
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn.1 hn.2)
    have hs : (sqInd n : ℝ) = 0 ∨ (sqInd n : ℝ) = 1 := by
      rw [sqInd_apply]; split_ifs <;> simp
    rcases hs with hs | hs
    · rw [hs]; simp
    rw [hs, one_mul, one_mul]
    have hq : ((N / n : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) / n) := by
      have h1 : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ (N : ℝ) / n := by
        rw [le_div_iff₀ hn0, one_mul]; exact_mod_cast hn.2
      linarith
    calc |(mertens (N / n : ℕ) : ℝ)| ≤ K * (((N / n : ℕ) : ℝ) + 1) ^ β := hK _
      _ ≤ K * (2 * ((N : ℝ) / n)) ^ β := by gcongr
      _ = K * 2 ^ β * (N : ℝ) ^ β * (n : ℝ) ^ (-β) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.div_rpow hN0.le hn0.le,
            Real.rpow_neg hn0.le]
          ring
  calc |∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ)|
      ≤ ∑ n ∈ Ioc 0 N, |(sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, K * 2 ^ β * (N : ℝ) ^ β * ((sqInd n : ℝ) * (n : ℝ) ^ (-β)) :=
        sum_le_sum hterm
    _ = K * 2 ^ β * (N : ℝ) ^ β * ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (n : ℝ) ^ (-β) := by
        rw [mul_sum]
    _ ≤ K * 2 ^ β * (N : ℝ) ^ β * Z := by
        gcongr
        exact sum_sqInd_rpow_le hβ N
    _ = K * 2 ^ β * Z * (N : ℝ) ^ β := by ring

/-- **The Liouville bound from the Mertens bound**: `M(x) = O(x^{1/2+ε})` for every `ε > 0`
implies `L(x) = O(x^{1/2+ε})` for every `ε > 0`. -/
theorem liouville_of_mertensBound (hMB : MertensBound) : LiouvilleBound := by
  intro ε hε
  obtain ⟨K', hK'0, hK'⟩ := abs_liouvilleSum_nat_le hMB (β := 1 / 2 + ε) (by linarith)
  refine IsBigO.of_bound K' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hL : liouvilleSum x = liouvilleSum (⌊x⌋₊ : ℝ) := by
    simp only [liouvilleSum, Nat.floor_natCast]
  rw [hL, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
  calc |(liouvilleSum (⌊x⌋₊ : ℝ) : ℝ)| ≤ K' * (⌊x⌋₊ : ℝ) ^ (1 / 2 + ε) := hK' _
    _ ≤ K' * x ^ (1 / 2 + ε) := by
        gcongr
        exact Nat.floor_le hx0

/-- **The Liouville bound under RH**: `∑_{n ≤ x} λ(n) = O(x^{1/2+ε})` for every `ε > 0`. -/
theorem liouville_of_RH (hRH : RiemannHypothesis) : LiouvilleBound :=
  liouville_of_mertensBound (mertens_of_RH hRH)

end Mertens
