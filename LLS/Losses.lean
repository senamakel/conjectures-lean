import Mathlib

/-!
# Losses from integers not prime to `q`

If a character `φ` mod `f ∣ q` takes the value `1` on every `n ≤ x` prime to `q`, then a
`Λ`-weighted sum `Σ_{n ≤ x} Λ(n) w(n) Re φ(n)` falls short of `Σ_{n ≤ x} Λ(n) w(n)` only through
prime powers `p^k ≤ x` with `p ∣ q`: once if `p ∣ f` (there `φ = 0`) and at most twice if
`p ∤ f` (there `Re φ ≥ −1`).
-/

namespace LLS

open ArithmeticFunction Finset

/-- The prime powers of `p` up to `x`. -/
def ppF (x p : ℕ) : Finset ℕ := (range (x + 1)).filter fun n => IsPrimePow n ∧ n.minFac = p

/-- A weighted `Λ`-sum over `n ≤ x` with `P n` is bounded by the prime-power fibres over `S`,
provided every prime power `n ≤ x` with `P n` has its prime in `S`. -/
lemma sum_le_sum_ppF (x : ℕ) (P : ℕ → Prop) [DecidablePred P] (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ≤ x, 0 ≤ w n) (hS : ∀ n ≤ x, P n → IsPrimePow n → n.minFac ∈ S) :
    ∑ n ∈ (range (x + 1)).filter P, (Λ n : ℝ) * w n
      ≤ ∑ p ∈ S, ∑ n ∈ ppF x p, (Λ n : ℝ) * w n := by
  classical
  set T := ((range (x + 1)).filter P).filter IsPrimePow
  have h1 : ∑ n ∈ (range (x + 1)).filter P, (Λ n : ℝ) * w n = ∑ n ∈ T, (Λ n : ℝ) * w n := by
    simp only [T]
    rw [sum_filter (s := (range (x + 1)).filter P)]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · rw [vonMangoldt_apply, ite_eq_right h]; simp
  rw [h1, ← sum_fiberwise_of_maps_to (g := Nat.minFac) (t := S)]
  · refine sum_le_sum fun p _ => ?_
    refine sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
    · intro n hn
      simp only [T, mem_filter, mem_range] at hn
      simp only [ppF, mem_filter, mem_range]
      exact ⟨hn.1.1.1, hn.1.2, hn.2⟩
    · simp only [ppF, mem_filter, mem_range] at hn
      exact mul_nonneg vonMangoldt_nonneg (hw n (Nat.lt_succ_iff.1 hn.1))
  · intro n hn
    simp only [T, mem_filter, mem_range] at hn
    exact hS n (Nat.lt_succ_iff.1 hn.1.1) hn.1.2 hn.2

/-- The loss lemma. -/
theorem sum_re_ge {f q : ℕ} (φ : DirichletCharacter ℂ f) (_hfq : f ∣ q) (hq : q ≠ 0) (x : ℕ)
    (w : ℕ → ℝ) (hw : ∀ n ≤ x, 0 ≤ w n) (h1 : ∀ n ≤ x, n.Coprime q → φ n = 1) :
    ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n
        - ∑ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * w n
        - ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f), ∑ n ∈ ppF x p, (Λ n : ℝ) * w n
      ≤ ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n * (φ n).re := by
  classical
  have hcopf : ∀ n : ℕ, φ n ≠ 0 → n.Coprime f := fun n hn => by
    have hu : IsUnit (n : ZMod f) := by
      by_contra h
      exact hn (MulChar.map_nonunit φ h)
    exact (ZMod.isUnit_iff_coprime n f).1 hu
  set E₁ := ∑ n ∈ (range (x + 1)).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) * w n
  set E₂ := ∑ n ∈ (range (x + 1)).filter (fun n : ℕ => ¬ n.Coprime q ∧ φ (n : ZMod f) ≠ 0),
    (Λ n : ℝ) * w n
  have hterm : ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n - E₁ - E₂
      ≤ ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n * (φ n).re := by
    simp only [E₁, E₂]
    rw [sum_filter, sum_filter, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hnx : n ≤ x := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hlw : 0 ≤ (Λ n : ℝ) * w n := mul_nonneg vonMangoldt_nonneg (hw n hnx)
    by_cases hc : n.Coprime q
    · rw [h1 n hnx hc]; simp [hc]
    · have hnorm : ‖φ n‖ ≤ 1 := DirichletCharacter.norm_le_one φ _
      have hre1 : -1 ≤ (φ n).re := by
        have := Complex.abs_re_le_norm (φ n)
        rw [abs_le] at this; linarith
      by_cases h0 : φ n = 0
      · simp only [hc, h0, not_false_eq_true, true_and, ne_eq, not_true_eq_false, ite_true,
          ite_false, Complex.zero_re, mul_zero, sub_zero]
        linarith
      · simp only [hc, h0, not_false_eq_true, true_and, ne_eq, ite_true]
        nlinarith [mul_le_mul_of_nonneg_left hre1 hlw]
  have hE₁ : E₁ ≤ ∑ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * w n := by
    refine sum_le_sum_ppF x _ _ w hw fun n _ hc hpp => ?_
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    rw [Nat.Prime.pow_minFac hr hk.ne', Nat.mem_primeFactors]
    refine ⟨hr, ?_, hq⟩
    by_contra hd
    exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
  have hE₂ : E₂ ≤ ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f),
      ∑ n ∈ ppF x p, (Λ n : ℝ) * w n := by
    refine sum_le_sum_ppF x _ _ w hw fun n _ hc hpp => ?_
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    rw [Nat.Prime.pow_minFac hr hk.ne']
    simp only [mem_filter, Nat.mem_primeFactors]
    refine ⟨⟨hr, ?_, hq⟩, ?_⟩
    · by_contra hd
      exact hc.1 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
    · intro hd
      have hcop := hcopf _ hc.2
      have : r.Coprime f := Nat.Coprime.coprime_dvd_left (dvd_pow_self r hk.ne') hcop
      exact (Nat.Prime.coprime_iff_not_dvd hr).1 this hd
  linarith

/-- `log f + Σ_{p ∣ q, p ∤ f} log p ≤ log q` for `f ∣ q`. -/
theorem log_add_sum_log_le {f q : ℕ} (hfq : f ∣ q) (hq : q ≠ 0) :
    Real.log f + ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f), Real.log p ≤ Real.log q := by
  classical
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f)
  have hf0 : f ≠ 0 := fun h => hq (Nat.eq_zero_of_zero_dvd (h ▸ hfq))
  have hRpos : ∀ p ∈ R, (p : ℝ) ≠ 0 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).pos
    positivity
  have hcop : f.Coprime (∏ p ∈ R, p) := Nat.Coprime.prod_right fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1
    exact ((Nat.Prime.coprime_iff_not_dvd hpp).2 (mem_filter.1 hp).2).symm
  have hdvd : f * ∏ p ∈ R, p ∣ q :=
    hcop.mul_dvd_of_dvd_of_dvd hfq
      ((prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q))
  have hle : ((f * ∏ p ∈ R, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd
  have hf0' : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero hf0
  have hP0 : (0 : ℝ) < ∏ p ∈ R, (p : ℝ) := prod_pos fun p hp => by
    have := (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).pos
    positivity
  rw [← Real.log_prod hRpos, ← Real.log_mul hf0'.ne' hP0.ne']
  refine Real.log_le_log (by positivity) ?_
  simpa using hle

end LLS
