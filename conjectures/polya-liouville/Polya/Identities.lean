import Polya.Statement
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Two identities for the Mertens function

* `sum_mertens_div`: `∑_{n=1}^{x} M(⌊x/n⌋) = 1` for `x ≥ 1`, from `ζ * μ = 1`.
* `liouvilleSum_eq_sum_mertens`: `L(x) = ∑_{d=1}^{⌊√x⌋} M(⌊x/d²⌋)`, from `λ = 𝟙_□ * μ`, where
  `𝟙_□` is the indicator of the nonzero squares (`liouville_mul_zeta : λ * ζ = 𝟙_□`).
-/

namespace Polya

open ArithmeticFunction Finset

theorem Icc_one_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext k; simp only [mem_Icc, mem_Ioc]; omega

theorem mertens_eq_Ioc (x : ℕ) : mertens x = ∑ k ∈ Ioc 0 x, μ k := by
  rw [mertens, Icc_one_eq_Ioc]

/-- `∑_{n=1}^{x} M(⌊x/n⌋) = 1` for `x ≥ 1`. -/
theorem sum_mertens_div {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 x, mertens (x / n) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum ((ζ : ArithmeticFunction ℤ)) μ x
  rw [coe_zeta_mul_moebius] at h
  have h1 : ∑ n ∈ Ioc 0 x, (1 : ArithmeticFunction ℤ) n = 1 := by
    simp only [ArithmeticFunction.one_apply]
    rw [sum_ite_eq']
    simp only [mem_Ioc]
    rw [if_pos ⟨Nat.one_pos, hx⟩]
  rw [h1] at h
  rw [h, Icc_one_eq_Ioc]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by simp only [mem_Ioc] at hn; omega
  rw [intCoe_apply, zeta_apply_ne hn0, Nat.cast_one, one_mul, mertens_eq_Ioc]

/-! ## The indicator of the squares -/

/-- The indicator of the nonzero squares. -/
def sqInd : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

theorem sqInd_apply (n : ℕ) : sqInd n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := rfl

theorem isSquare_mul_iff_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  simp only [Nat.isSquare_iff_even_factorization, Nat.factorization_mul hm hn,
    Finsupp.coe_add, Pi.add_apply]
  constructor
  · intro H
    have key : ∀ p : ℕ, p.Prime → m.factorization p = 0 ∨ n.factorization p = 0 := by
      intro p hp
      by_contra hc
      push_neg at hc
      have hpm : p ∣ m := Nat.dvd_of_factorization_pos hc.1
      have hpn : p ∣ n := Nat.dvd_of_factorization_pos hc.2
      have : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
      rw [h.gcd_eq_one] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rcases key p hp with h0 | h0
      · rw [h0]; exact even_zero
      · simpa [h0] using H p hp
    · rcases key p hp with h0 | h0
      · simpa [h0] using H p hp
      · rw [h0]; exact even_zero
  · rintro ⟨H1, H2⟩ p hp
    exact (H1 p hp).add (H2 p hp)

theorem isMultiplicative_sqInd : IsMultiplicative sqInd := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [sqInd_apply], fun {m n} hm hn hmn => ?_⟩
  simp only [sqInd_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    isSquare_mul_iff_of_coprime hm hn hmn]
  by_cases h1 : IsSquare m <;> by_cases h2 : IsSquare n <;> simp [h1, h2]

theorem isSquare_prime_pow_iff {p i : ℕ} (hp : p.Prime) : IsSquare (p ^ i) ↔ Even i := by
  rw [Nat.isSquare_iff_even_factorization]
  constructor
  · intro H
    simpa [hp.factorization_pow] using H p hp
  · intro H q hq
    rw [hp.factorization_pow, Finsupp.single_apply]
    split_ifs
    · exact H
    · exact even_zero

theorem sum_range_neg_one_pow (i : ℕ) :
    ∑ j ∈ range (i + 1), ((-1 : ℤ) ^ j) = if Even i then 1 else 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih]
    by_cases h : Even i
    · have h' : ¬ Even (i + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', h.neg_one_pow.symm ▸ rfl]
      rw [pow_succ, h.neg_one_pow]; norm_num
    · have h' : Even (i + 1) := by rw [Nat.even_add_one]; exact h
      rw [if_neg h, if_pos h']
      rw [Nat.not_even_iff_odd] at h
      rw [h'.neg_one_pow]; norm_num

/-- `∑_{d ∣ n} λ(d) = 1` if `n` is a nonzero square and `0` otherwise. -/
theorem liouville_mul_zeta : liouville * (ζ : ArithmeticFunction ℤ) = sqInd := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouville.mul isMultiplicative_zeta.intCast) _ isMultiplicative_sqInd).2 ?_
  intro p i hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sqInd_apply]
  have : ∀ j ∈ range (i + 1), liouville (p ^ j) = (-1 : ℤ) ^ j := by
    intro j _
    rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
  rw [sum_congr rfl this, sum_range_neg_one_pow, isSquare_prime_pow_iff hp]
  simp [hp.ne_zero]

theorem liouville_eq_sqInd_mul_moebius : liouville = sqInd * μ := by
  rw [← liouville_mul_zeta, mul_assoc, coe_zeta_mul_moebius, mul_one]

/-- `L(x) = ∑_{d=1}^{⌊√x⌋} M(⌊x/d²⌋)`. -/
theorem liouvilleSum_eq_sum_mertens (x : ℕ) :
    liouvilleSum x = ∑ d ∈ Icc 1 (Nat.sqrt x), mertens (x / (d * d)) := by
  rw [liouvilleSum, Icc_one_eq_Ioc, liouville_eq_sqInd_mul_moebius, sum_Ioc_mul_eq_sum_sum]
  simp_rw [← mertens_eq_Ioc, sqInd_apply, ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  have himg : (Ioc 0 x).filter (fun n => n ≠ 0 ∧ IsSquare n) =
      (Icc 1 (Nat.sqrt x)).image (fun d => d * d) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨h0, hx⟩, -, r, rfl⟩
      refine ⟨r, ⟨?_, Nat.le_sqrt.2 hx⟩, rfl⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp at h0
      · exact hr
    · rintro ⟨d, ⟨h1, hd⟩, rfl⟩
      have hdd : 0 < d * d := Nat.mul_pos h1 h1
      exact ⟨⟨hdd, Nat.le_sqrt.1 hd⟩, hdd.ne', d, rfl⟩
  rw [himg, sum_image]
  intro a _ b _ hab
  exact Nat.mul_self_inj.1 hab

end Polya
