import Robin.Defs

/-!
# An upper bound for `σ(n)/n` with a free exponent

For every `ε > 0`, `σ(n)/n ≤ n^ε ∏_p max_k (1 + p⁻¹ + ⋯ + p⁻ᵏ) p^{−kε}`
(multiplicativity; this is the bound attained by colossally abundant numbers).
With `ε = ε(x) = log(1+1/x)/log x` only primes `p ≤ x` contribute, and the local maximum is
at most `c_p − ε log p − min(1/p², ε log p)`.
-/

namespace Robin

open ArithmeticFunction Real
open scoped ArithmeticFunction.sigma

/-- The local factor `σ(p^k)/p^k = (1 + p + ⋯ + p^k)/p^k`. -/
noncomputable def locT (p k : ℕ) : ℝ := (∑ j ∈ Finset.range (k + 1), (p : ℝ) ^ j) / (p : ℝ) ^ k

lemma locT_pos {p : ℕ} (hp : 1 ≤ p) (k : ℕ) : 0 < locT p k := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold locT
  apply div_pos _ (by positivity)
  exact Finset.sum_pos (fun j _ => by positivity) ⟨0, by simp⟩

lemma epsR_pos {x : ℝ} (hx : 3 ≤ x) : 0 < epsR x := by
  unfold epsR
  apply div_pos
  · apply Real.log_pos
    have : 0 < 1 / x := div_pos one_pos (by linarith)
    linarith
  · exact Real.log_pos (by linarith)

/-- `log(1 + 1/t) ≤ ε(x) log t` for `t ≥ x ≥ 3`: `log(1+1/t)/log t` is decreasing. -/
lemma log_one_add_inv_le_epsR_mul {x t : ℝ} (hx : 3 ≤ x) (ht : x ≤ t) :
    Real.log (1 + 1 / t) ≤ epsR x * Real.log t := by
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlt : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) ht
  have h1 : Real.log (1 + 1 / t) ≤ Real.log (1 + 1 / x) := by
    have : 0 < 1 / t := div_pos one_pos (by linarith)
    apply Real.log_le_log (by linarith)
    have := one_div_le_one_div_of_le (by linarith) ht
    linarith
  have h0 : 0 ≤ Real.log (1 + 1 / t) :=
    Real.log_nonneg (by have : 0 ≤ 1 / t := div_nonneg zero_le_one (by linarith); linarith)
  unfold epsR
  rw [div_mul_eq_mul_div, le_div_iff₀ hlx]
  nlinarith [mul_le_mul_of_nonneg_left hlt h0,
    mul_le_mul_of_nonneg_right h1 (le_of_lt (lt_of_lt_of_le hlx hlt))]

lemma geom_sum_le_add_one_pow {p : ℝ} (hp : 0 ≤ p) :
    ∀ k : ℕ, ∑ j ∈ Finset.range (k + 1), p ^ j ≤ (p + 1) ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ]
    have ih := geom_sum_le_add_one_pow hp k
    have : p ^ (k + 1) ≤ p * (p + 1) ^ k := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp (by linarith) k) hp
    calc _ ≤ (p + 1) ^ k + p * (p + 1) ^ k := by linarith
      _ = (p + 1) ^ (k + 1) := by ring

lemma log_locT_le {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    Real.log (locT p k) ≤ k * Real.log (1 + 1 / (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hb : locT p k ≤ (1 + 1 / (p : ℝ)) ^ k := by
    unfold locT
    rw [div_le_iff₀ (by positivity), ← mul_pow]
    have : (1 + 1 / (p : ℝ)) * p = p + 1 := by field_simp
    rw [this]
    exact geom_sum_le_add_one_pow (by linarith) k
  rw [← Real.log_pow]
  exact Real.log_le_log (locT_pos hp k) hb

lemma locT_eq {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    locT p k = (1 - 1 / (p : ℝ) ^ (k + 1)) / (1 - 1 / (p : ℝ)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) ≠ 1 := by intro h; linarith
  have h1' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  unfold locT
  rw [geom_sum_eq h1]
  field_simp
  ring

lemma log_locT_eq {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    Real.log (locT p k) = cp p + Real.log (1 - 1 / (p : ℝ) ^ (k + 1)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have ha : 0 < 1 - 1 / (p : ℝ) ^ (k + 1) := by
    have : 1 / (p : ℝ) ^ (k + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      exact one_lt_pow₀ (by linarith) (by omega)
    linarith
  have hb : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  rw [locT_eq hp, Real.log_div ha.ne' hb.ne', cp]
  ring

/-- Primes beyond `x` contribute nothing. -/
lemma local_le_zero {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : 3 ≤ x) (hpx : x < p) (k : ℕ) :
    Real.log (locT p k) - k * (epsR x * Real.log p) ≤ 0 := by
  have h1 := log_locT_le hp k
  have h2 := log_one_add_inv_le_epsR_mul hx hpx.le
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hk]

/-- The local maximum for a prime `p ≤ x`. -/
lemma local_le_small {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 3 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (locT p k) - k * (epsR x * Real.log p) ≤
      cp p - epsR x * Real.log p - min (1 / (p : ℝ) ^ 2) (epsR x * Real.log p) := by
  have hp2 := hp.two_le
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hε := epsR_pos hx
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hεl : 0 ≤ epsR x * Real.log p := mul_nonneg hε.le hlp
  rw [log_locT_eq hp2]
  have hq : 0 < 1 / (p : ℝ) ^ (k + 1) := by positivity
  have hq1 : 1 / (p : ℝ) ^ (k + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ (by linarith) (by omega)
  have hlog : Real.log (1 - 1 / (p : ℝ) ^ (k + 1)) ≤ -(1 / (p : ℝ) ^ (k + 1)) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - 1 / (p : ℝ) ^ (k + 1) by linarith)
    linarith
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    norm_num at hlog ⊢
    have := min_le_left ((p : ℝ) ^ 2)⁻¹ (epsR x * Real.log p)
    linarith
  · have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have := min_le_right (1 / (p : ℝ) ^ 2) (epsR x * Real.log p)
    nlinarith [mul_le_mul_of_nonneg_right hk2' hεl]

/-- The local maximum for a prime `p ≤ x` is nonnegative. -/
lemma local_bound_nonneg {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 3 ≤ x) (hpx : (p : ℝ) ≤ x) :
    0 ≤ cp p - epsR x * Real.log p - min (1 / (p : ℝ) ^ 2) (epsR x * Real.log p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hε := epsR_pos hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hm := min_le_left (1 / (p : ℝ) ^ 2) (epsR x * Real.log p)
  -- `cp p - 1/p² ≥ log(1 + 1/p)`
  have ha : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have hb : 0 < 1 + 1 / (p : ℝ) := by positivity
  have hsq : 1 - 1 / (p : ℝ) ^ 2 = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ)) := by ring
  have hlog : Real.log (1 - 1 / (p : ℝ) ^ 2) ≤ -(1 / (p : ℝ) ^ 2) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - 1 / (p : ℝ) ^ 2 by rw [hsq]; positivity)
    linarith
  rw [hsq, Real.log_mul ha.ne' hb.ne'] at hlog
  -- `log(1 + 1/p) ≥ log(1 + 1/x) = ε log x ≥ ε log p`
  have h1 : Real.log (1 + 1 / x) ≤ Real.log (1 + 1 / (p : ℝ)) := by
    apply Real.log_le_log (by positivity)
    have := one_div_le_one_div_of_le (by linarith) hpx
    linarith
  have h2 : epsR x * Real.log x = Real.log (1 + 1 / x) := by
    unfold epsR; field_simp
  have h3 : epsR x * Real.log p ≤ epsR x * Real.log x :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hpx) hε.le
  unfold cp
  linarith

theorem log_sigma_div_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 3 ≤ x) :
    Real.log ((σ 1 n : ℝ) / n) ≤
      epsR x * Real.log n + primeSum (fun p => cp p - epsR x * Real.log p) x - gainSum x := by
  have hn0 : n ≠ 0 := by omega
  have hσ : (σ 1 n : ℝ) = ∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1), (p : ℝ) ^ j := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0, Finsupp.prod,
      Nat.support_factorization]
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]
    push_cast
    rfl
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  have hpos : ∀ p ∈ n.primeFactors, 1 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hlogq : Real.log ((σ 1 n : ℝ) / n) =
      ∑ p ∈ n.primeFactors, Real.log (locT p (n.factorization p)) := by
    rw [hσ, hnR, ← Finset.prod_div_distrib, Real.log_prod]
    · rfl
    · intro p hp
      exact (locT_pos (hpos p hp) _).ne'
  have hlogn : Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
    rw [hnR, Real.log_prod]
    · simp [Real.log_pow]
    · intro p hp
      have : (1 : ℝ) ≤ p := by exact_mod_cast hpos p hp
      positivity
  set P := (Finset.Iic ⌊x⌋₊).filter Nat.Prime with hP
  set b : ℕ → ℝ := fun p =>
    cp p - epsR x * Real.log p - min (1 / (p : ℝ) ^ 2) (epsR x * Real.log p) with hb
  have hmemP : ∀ p : ℕ, p ∈ P ↔ p.Prime ∧ (p : ℝ) ≤ x := by
    intro p
    rw [hP, Finset.mem_filter, Finset.mem_Iic, Nat.le_floor_iff (by linarith)]
    tauto
  have key : ∑ p ∈ n.primeFactors,
      (Real.log (locT p (n.factorization p)) - n.factorization p * (epsR x * Real.log p)) ≤
      ∑ p ∈ P, b p := by
    calc _ ≤ ∑ p ∈ n.primeFactors, (if p ∈ P then b p else 0) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpp := Nat.prime_of_mem_primeFactors hp
          split_ifs with h
          · exact local_le_small hpp hx
              ((Nat.Prime.factorization_pos_of_dvd hpp hn0 (Nat.dvd_of_mem_primeFactors hp)))
          · have : x < p := by
              by_contra hc
              exact h ((hmemP p).2 ⟨hpp, not_lt.mp hc⟩)
            exact local_le_zero (hpos p hp) hx this _
      _ = ∑ p ∈ n.primeFactors ∩ P, b p := by rw [Finset.sum_ite_mem]
      _ ≤ ∑ p ∈ P, b p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right ?_
          intro p hp _
          obtain ⟨hpp, hpx⟩ := (hmemP p).1 hp
          exact local_bound_nonneg hpp hx hpx
  have hsplit : primeSum (fun p => cp p - epsR x * Real.log p) x - gainSum x = ∑ p ∈ P, b p := by
    unfold gainSum primeSum
    rw [← Finset.sum_sub_distrib]
  rw [hlogq, hlogn, Finset.mul_sum]
  rw [Finset.sum_sub_distrib] at key
  have : ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * (epsR x * Real.log p) =
      ∑ p ∈ n.primeFactors, epsR x * ((n.factorization p : ℝ) * Real.log p) :=
    Finset.sum_congr rfl fun p _ => by ring
  linarith

end Robin
