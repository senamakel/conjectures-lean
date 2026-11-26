import Robin.Elementary.SigmaBound

/-!
# The colossally-abundant envelope and the line test

For every `ε > 0` and `n ≥ 1`,
`log(σ(n)/n) = Σ_{p^k ∥ n} log(σ(p^k)/p^k) ≤ ε log n + Σ_p max_k (log(σ(p^k)/p^k) − kε log p)`.
`log_sigma_div_le_env` states this with an arbitrary finite set `S` that contains every prime
whose local maximum may be positive, and arbitrary upper bounds `b p` for those maxima.

`robin_of_line_ends`: if `ε x + C < γ + log log x` at both ends of `[lo, hi]` then, since
`log log` is concave, it holds on all of `[lo, hi]`, and then every `n` with `log n ∈ [lo, hi]`
and `log(σ(n)/n) ≤ ε log n + C` satisfies Robin's inequality.
-/

namespace Robin.Compute

open ArithmeticFunction Real Finset
open scoped ArithmeticFunction.sigma

theorem log_sigma_div_le_env {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (S : Finset ℕ) (b : ℕ → ℝ)
    (hout : ∀ p, p.Prime → p ∉ S → ∀ k, Real.log (locT p k) - k * (ε * Real.log p) ≤ 0)
    (hin : ∀ p ∈ S, p.Prime → ∀ k, 1 ≤ k → Real.log (locT p k) - k * (ε * Real.log p) ≤ b p)
    (hnn : ∀ p ∈ S, 0 ≤ b p) :
    Real.log ((σ 1 n : ℝ) / n) ≤ ε * Real.log n + ∑ p ∈ S, b p := by
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
  have key : ∑ p ∈ n.primeFactors,
      (Real.log (locT p (n.factorization p)) - n.factorization p * (ε * Real.log p)) ≤
      ∑ p ∈ S, b p := by
    calc _ ≤ ∑ p ∈ n.primeFactors, (if p ∈ S then b p else 0) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpp := Nat.prime_of_mem_primeFactors hp
          split_ifs with h
          · exact hin p h hpp _
              (Nat.Prime.factorization_pos_of_dvd hpp hn0 (Nat.dvd_of_mem_primeFactors hp))
          · exact hout p hpp h _
      _ = ∑ p ∈ n.primeFactors ∩ S, b p := by rw [Finset.sum_ite_mem]
      _ ≤ ∑ p ∈ S, b p :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            (fun p hp _ => hnn p hp)
  rw [hlogq, hlogn, Finset.mul_sum]
  rw [Finset.sum_sub_distrib] at key
  have : ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * (ε * Real.log p) =
      ∑ p ∈ n.primeFactors, ε * ((n.factorization p : ℝ) * Real.log p) :=
    Finset.sum_congr rfl fun p _ => by ring
  linarith

/-! ### Local factors as products of `1 + 1/a_j` -/

/-- `a_j = p + p² + ⋯ + p^{j+1}`. -/
def aSeq (p j : ℕ) : ℕ := ∑ i ∈ range (j + 1), p ^ (i + 1)

lemma aSeq_succ (p j : ℕ) : aSeq p (j + 1) = aSeq p j + p ^ (j + 2) := by
  unfold aSeq; rw [Finset.sum_range_succ]

lemma aSeq_zero (p : ℕ) : aSeq p 0 = p := by simp [aSeq]

lemma aSeq_pos {p : ℕ} (hp : 1 ≤ p) (j : ℕ) : 0 < aSeq p j := by
  unfold aSeq
  exact Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩

lemma aSeq_mono (p : ℕ) {i j : ℕ} (h : i ≤ j) : aSeq p i ≤ aSeq p j := by
  unfold aSeq
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun _ _ _ => Nat.zero_le _)

lemma sq_le_aSeq_one {p : ℕ} : p ^ 2 ≤ aSeq p 1 := by
  simp [aSeq, Finset.sum_range_succ]

lemma locT_succ {p : ℕ} (hp : 1 ≤ p) (j : ℕ) :
    locT p (j + 1) = locT p j * (1 + 1 / (aSeq p j : ℝ)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hS : ∀ j : ℕ, (aSeq p j : ℝ) = p * ∑ i ∈ range (j + 1), (p : ℝ) ^ i := by
    intro j; unfold aSeq; push_cast; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : (0 : ℝ) < ∑ i ∈ range (j + 1), (p : ℝ) ^ i :=
    Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩
  unfold locT
  rw [hS j, Finset.sum_range_succ _ (j + 1)]
  have : ∑ i ∈ range (j + 1 + 1), (p : ℝ) ^ i = 1 + p * ∑ i ∈ range (j + 1), (p : ℝ) ^ i := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ]; ring
  rw [← Finset.sum_range_succ, this]
  field_simp
  ring

lemma log_locT_eq_sum {p : ℕ} (hp : 1 ≤ p) :
    ∀ k, Real.log (locT p k) = ∑ j ∈ range k, Real.log (1 + 1 / (aSeq p j : ℝ))
  | 0 => by simp [locT]
  | k + 1 => by
    rw [locT_succ hp, Real.log_mul (locT_pos hp k).ne' (by
        have := aSeq_pos hp k; positivity), log_locT_eq_sum hp k, Finset.sum_range_succ]

/-! ### Monotonicity of `log(1 + 1/t)/log t` -/

lemma log_one_add_inv_le_mul {x t : ℝ} (hx : 1 < x) (ht : x ≤ t) :
    Real.log (1 + 1 / t) * Real.log x ≤ Real.log (1 + 1 / x) * Real.log t := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlt : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) ht
  have h1 : Real.log (1 + 1 / t) ≤ Real.log (1 + 1 / x) := by
    have : 0 < 1 / t := div_pos one_pos (by linarith)
    apply Real.log_le_log (by linarith)
    have := one_div_le_one_div_of_le (by linarith) ht
    linarith
  have h0 : 0 ≤ Real.log (1 + 1 / t) :=
    Real.log_nonneg (by have : 0 ≤ 1 / t := div_nonneg zero_le_one (by linarith); linarith)
  nlinarith [mul_le_mul_of_nonneg_left hlt h0,
    mul_le_mul_of_nonneg_right h1 (le_of_lt (lt_of_lt_of_le hlx hlt))]

/-- From `log(1 + 1/B) ≤ ε log B`: `log(1 + 1/t) ≤ ε log t` for `t ≥ B > 1`. -/
lemma log_one_add_inv_le_of_le {ε B t : ℝ} (hB : 1 < B) (ht : B ≤ t)
    (h : Real.log (1 + 1 / B) ≤ ε * Real.log B) : Real.log (1 + 1 / t) ≤ ε * Real.log t := by
  have hlB : 0 < Real.log B := Real.log_pos hB
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hm := log_one_add_inv_le_mul hB ht
  have : Real.log (1 + 1 / t) * Real.log B ≤ ε * Real.log t * Real.log B := by nlinarith
  exact le_of_mul_le_mul_right this hlB

/-- From `ε log P ≤ log(1 + 1/P)`: `ε log m ≤ log(1 + 1/m)` for `1 < m ≤ P`. -/
lemma le_log_one_add_inv_of_le {ε m P : ℝ} (hm : 1 < m) (hmP : m ≤ P)
    (h : ε * Real.log P ≤ Real.log (1 + 1 / P)) : ε * Real.log m ≤ Real.log (1 + 1 / m) := by
  have hlm : 0 < Real.log m := Real.log_pos hm
  have hlP : 0 < Real.log P := Real.log_pos (by linarith)
  have hmono := log_one_add_inv_le_mul hm hmP
  have : ε * Real.log m * Real.log P ≤ Real.log (1 + 1 / m) * Real.log P := by nlinarith
  exact le_of_mul_le_mul_right this hlP

/-- Primes beyond the cut-off contribute nothing. -/
lemma local_le_zero_of {ε : ℝ} {p : ℕ} (hp : 1 ≤ p)
    (h : Real.log (1 + 1 / (p : ℝ)) ≤ ε * Real.log p) (k : ℕ) :
    Real.log (locT p k) - k * (ε * Real.log p) ≤ 0 := by
  have h1 := log_locT_le hp k
  have hk : (0 : ℝ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hk]

/-! ### The line test -/

lemma robin_of_env {n : ℕ} (hn : 1 ≤ n) {ε C : ℝ}
    (henv : Real.log ((σ 1 n : ℝ) / n) ≤ ε * Real.log n + C)
    (hline : ε * Real.log n + C < Real.eulerMascheroniConstant + Real.log (Real.log (Real.log n)))
    (hl : 1 < Real.log n) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hσpos : (0 : ℝ) < σ 1 n := by
    have : 0 < σ 1 n := by rw [sigma_pos_iff]; omega
    exact_mod_cast this
  have hlt : Real.log ((σ 1 n : ℝ) / n) <
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log n)) := by linarith
  have h := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_log (div_pos hσpos hn0), Real.exp_add,
    Real.exp_log (Real.log_pos hl)] at h
  rw [div_lt_iff₀ hn0] at h
  linarith [h]

lemma concave_loglog {lo hi x : ℝ} (hlo0 : 0 < lo) (hlo : 1 < Real.log lo) (h1 : lo ≤ x)
    (h2 : x ≤ hi) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = t * lo + (1 - t) * hi ∧
      t * Real.log (Real.log lo) + (1 - t) * Real.log (Real.log hi) ≤
        Real.log (Real.log x) := by
  have hhi : 1 < Real.log hi := lt_of_lt_of_le hlo (Real.log_le_log hlo0 (h1.trans h2))
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · refine ⟨1, by norm_num, le_refl _, by rw [heq] at h1; linarith, ?_⟩
    have : x = lo := by rw [← heq] at h2; linarith
    rw [this]; simp
  set t := (hi - x) / (hi - lo)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
  have ht1 : t ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hx : x = t * lo + (1 - t) * hi := by
    have hne : hi - lo ≠ 0 := by linarith
    simp only [t]; field_simp; ring
  refine ⟨t, ht0, ht1, hx, ?_⟩
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have hsum : t + (1 - t) = 1 := by ring
  have hl1 : t * Real.log lo + (1 - t) * Real.log hi ≤ Real.log x := by
    have := hc.2 (Set.mem_Ioi.mpr hlo0) (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < hi)) ht0 h1t hsum
    simpa [smul_eq_mul, ← hx] using this
  have hl2 : t * Real.log (Real.log lo) + (1 - t) * Real.log (Real.log hi) ≤
      Real.log (t * Real.log lo + (1 - t) * Real.log hi) := by
    have := hc.2 (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < Real.log lo))
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < Real.log hi)) ht0 h1t hsum
    simpa [smul_eq_mul] using this
  have hpos : 0 < t * Real.log lo + (1 - t) * Real.log hi := by nlinarith
  exact hl2.trans (Real.log_le_log hpos hl1)

lemma line_of_ends {lo hi x ε C : ℝ} (hlo0 : 0 < lo) (hlo1 : 1 < Real.log lo) (h1 : lo ≤ x) (h2 : x ≤ hi)
    (hl : ε * lo + C < Real.eulerMascheroniConstant + Real.log (Real.log lo))
    (hh : ε * hi + C < Real.eulerMascheroniConstant + Real.log (Real.log hi)) :
    ε * x + C < Real.eulerMascheroniConstant + Real.log (Real.log x) := by
  obtain ⟨t, ht0, ht1, hx, hc⟩ := concave_loglog hlo0 hlo1 h1 h2
  set a := Real.eulerMascheroniConstant + Real.log (Real.log lo) - (ε * lo + C)
  set b := Real.eulerMascheroniConstant + Real.log (Real.log hi) - (ε * hi + C)
  have ha : 0 < a := by simp only [a]; linarith
  have hb : 0 < b := by simp only [b]; linarith
  have hab : 0 < t * a + (1 - t) * b := by
    rcases le_total a b with h | h
    · nlinarith
    · nlinarith
  have e : ε * x + C = t * (ε * lo + C) + (1 - t) * (ε * hi + C) := by rw [hx]; ring
  rw [e]
  simp only [a, b] at hab
  nlinarith

end Robin.Compute
