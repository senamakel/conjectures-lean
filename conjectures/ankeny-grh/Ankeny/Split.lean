import Ankeny.Analytic
import Ankeny.PrimePowers

/-!
# The key inequality

Let `χ ≠ 1` be a Dirichlet character mod `q` with `χ(n) = 1` for every `n < x` coprime to `q`.
Let `ψ` be the primitive character inducing `χ` (conductor `f ∣ q`). Then
`Re bachSum ψ x ≥ S₀ − Σ_{n<x, (n,q)>1} Λ(n) − Σ_{n<x, (n,q)>1, ψ(n) ≠ 0} Λ(n)`.
The first error sum is at most `ω(q) log x`. In the second, `n = p^k` with `p ∣ q`, `p ∤ f`, so it
is at most `(2/3)√x Σ_{p ∈ R} log p` with `f ∏_{p∈R} p ∣ q`; it is absorbed by the zero sum,
whose size is governed by `log f ≤ log q − Σ_{p∈R} log p`. Under GRH this gives

`x/2 − √x/20 − 3 − ω(q) log x ≤ (√x + 2 + 3/x)(2/3)(log q + 5/3) + log x + 1.6`.
-/

namespace Ankeny

open Complex ArithmeticFunction Finset Erdos985
open scoped Classical

/-- The real weight `1 - n/x` lies in `[0, 1]` for `n < x`. -/
lemma weight_mem {x n : ℕ} (hn : n < x) :
    0 ≤ 1 - (n : ℝ) / x ∧ 1 - (n : ℝ) / x ≤ 1 := by
  have hx : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have h1 : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx]; exact_mod_cast hn.le
  have h0 : 0 ≤ (n : ℝ) / x := by positivity
  constructor <;> linarith

lemma re_bachSum {N : ℕ} (ψ : DirichletCharacter ℂ N) (x : ℕ) :
    (bachSum ψ x).re = ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) * (ψ n).re := by
  rw [bachSum, Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  have : (Λ n : ℂ) * ψ n * (1 - (n : ℂ) / x) = (((Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ) : ℂ) * ψ n := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]

theorem key_inequality (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 144 ≤ x)
    (hval : ∀ n < x, n.Coprime q → χ n = 1) :
    (x : ℝ) / 2 - √(x : ℝ) / 20 - 3 - q.primeFactors.card * Real.log x
      ≤ (√(x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log q + 5 / 3)) + (Real.log x + 1) + 0.6 := by
  set f := χ.conductor with hf
  have hfq : f ∣ q := χ.conductor_dvd_level
  have hq0 : q ≠ 0 := NeZero.ne q
  have : NeZero f := ⟨fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hfq))⟩
  set ψ := χ.primitiveCharacter
  have hψprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hψ1 : ψ ≠ 1 := fun h => hχ (by
    rw [← χ.changeLevel_primitiveCharacter]
    change DirichletCharacter.changeLevel _ ψ = 1
    rw [h, map_one])
  have hψval : ∀ n : ℕ, n.Coprime q → ψ n = χ n := fun n hn => by
    have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.2 hn)
    simpa using this
  have hψcop : ∀ n : ℕ, ψ n ≠ 0 → n.Coprime f := fun n hn => by
    have hu : IsUnit (n : ZMod f) := by
      by_contra h
      exact hn (MulChar.map_nonunit ψ h)
    exact (ZMod.isUnit_iff_coprime n f).1 hu
  have hxR : (144 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : 1 ≤ x := by omega
  /- termwise lower bound for the real part -/
  set S₀ : ℝ := ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) with hS₀
  set E₁ : ℝ := ∑ n ∈ (range x).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) with hE₁d
  set E₂ : ℝ := ∑ n ∈ (range x).filter (fun n : ℕ => ¬ n.Coprime q ∧ ψ (n : ZMod f) ≠ 0),
    (Λ n : ℝ) with hE₂d
  have hre : S₀ - E₁ - E₂ ≤ (bachSum ψ x).re := by
    rw [re_bachSum, hS₀, hE₁d, hE₂d, sum_filter, sum_filter, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hnx := mem_range.1 hn
    obtain ⟨hw0, hw1⟩ := weight_mem hnx
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    by_cases hc : n.Coprime q
    · rw [hψval n hc, hval n hnx hc]
      simp [hc]
    · have hnorm : ‖ψ n‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
      have hre1 : -1 ≤ (ψ n).re := by
        have := Complex.abs_re_le_norm (ψ n)
        rw [abs_le] at this; linarith
      by_cases h0 : ψ n = 0
      · simp only [hc, h0, not_false_eq_true, true_and, ne_eq, not_true_eq_false, ite_true,
          ite_false, Complex.zero_re, mul_zero, sub_zero]
        nlinarith
      · simp only [hc, h0, not_false_eq_true, true_and, ne_eq, ite_true]
        have hlw : 0 ≤ (Λ n : ℝ) * (1 - (n : ℝ) / x) := mul_nonneg hΛ hw0
        nlinarith [mul_le_mul_of_nonneg_left hre1 hlw]
  /- the first error sum -/
  have hE₁ : E₁ ≤ q.primeFactors.card * Real.log x := by
    refine (sum_vonMangoldt_le_sum_fiber x _ q.primeFactors ?_).trans ?_
    · intro n _ hc hpp
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rw [Nat.Prime.pow_minFac hr hk.ne', Nat.mem_primeFactors]
      refine ⟨hr, ?_, hq0⟩
      by_contra hd
      exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
    · calc ∑ p ∈ q.primeFactors, ∑ n ∈ ppFiber x p, (Λ n : ℝ)
          ≤ ∑ p ∈ q.primeFactors, Real.log x := sum_le_sum fun p hp =>
            (sum_ppFiber_le x p (Nat.prime_of_mem_primeFactors hp)).trans
              (log_mul_natLog_le x p (Nat.prime_of_mem_primeFactors hp) hx1)
        _ = q.primeFactors.card * Real.log x := by rw [sum_const, nsmul_eq_mul]
  /- the second error sum -/
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f)
  have hE₂ : E₂ ≤ (2 / 3) * √(x : ℝ) * ∑ p ∈ R, Real.log p := by
    refine (sum_vonMangoldt_le_sum_fiber x _ R ?_).trans ?_
    · intro n _ hc hpp
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rw [Nat.Prime.pow_minFac hr hk.ne']
      simp only [R, mem_filter, Nat.mem_primeFactors]
      refine ⟨⟨hr, ?_, hq0⟩, ?_⟩
      · by_contra hd
        exact hc.1 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
      · intro hd
        have hcop := hψcop _ hc.2
        have : r.Coprime f := Nat.Coprime.coprime_dvd_left (dvd_pow_self r hk.ne') hcop
        exact (Nat.Prime.coprime_iff_not_dvd hr).1 this hd
    · rw [mul_sum]
      refine sum_le_sum fun p hp => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1
      refine (sum_ppFiber_le x p hpp).trans ?_
      have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have := natLog_le_sqrt x p hpp hx
      nlinarith
  /- `log f + Σ_{p ∈ R} log p ≤ log q` -/
  have hlogR : Real.log f + ∑ p ∈ R, Real.log p ≤ Real.log q := by
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
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdvd
    have hf0 : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne f)
    have hP0 : (0 : ℝ) < ∏ p ∈ R, (p : ℝ) := prod_pos fun p hp => by
      have := (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).pos
      positivity
    rw [← Real.log_prod hRpos, ← Real.log_mul hf0.ne' hP0.ne']
    refine Real.log_le_log (by positivity) ?_
    simpa using hle
  /- assemble -/
  have hB := norm_bachSum_le hGRH hψprim hψ1 x hx1
  have hprin := (abs_le.1 (Analytic.bach_principal_of_GRH hGRH x hx1)).1
  have hRe := Complex.re_le_norm (bachSum ψ x)
  have hs0 : 0 ≤ √(x : ℝ) := Real.sqrt_nonneg _
  have hA : √(x : ℝ) ≤ √(x : ℝ) + 2 + 3 / x := by
    have : (0 : ℝ) ≤ 3 / x := by positivity
    linarith
  have hRnn : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).one_lt.le)
  have hkey : (√(x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log f + 5 / 3))
      + (2 / 3) * √(x : ℝ) * ∑ p ∈ R, Real.log p
      ≤ (√(x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log q + 5 / 3)) := by
    nlinarith
  linarith

end Ankeny
