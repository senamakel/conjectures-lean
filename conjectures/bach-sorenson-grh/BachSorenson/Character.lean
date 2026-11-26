import Ankeny.Split

/-!
# Step 2: the weighted sum of a non-principal character of any modulus, under GRH

For a non-trivial Dirichlet character `χ` mod `q` (not necessarily primitive) and `x ≥ 144`,

`‖Σ_{n<x} Λ(n) χ(n) (1 - n/x)‖ ≤ (√x + 2 + 3/x) (2/3) (log q + 5/3) + log x + 1.6`.

Let `ψ` be the primitive character inducing `χ`, of conductor `f ∣ q`. `bachSum χ` and
`bachSum ψ` differ only at `n` sharing a prime `p ∣ q` with `p ∤ f`, which contributes at most
`(2/3)√x · Σ_{p∈R} log p`; that is absorbed by the `log f` in `Ankeny.norm_bachSum_le`, since
`log f + Σ_{p∈R} log p ≤ log q`. This is the argument of `Ankeny.key_inequality`, kept as a norm
bound instead of a lower bound on the real part.
-/

namespace BachSorenson

open Complex ArithmeticFunction Finset Erdos985 Ankeny
open scoped Classical

/-- The per-character error term `B(q, x)`. -/
noncomputable def charBound (q x : ℕ) : ℝ :=
  (√(x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log q + 5 / 3)) + (Real.log x + 1) + 0.6

theorem norm_bachSum_le_charBound (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 144 ≤ x) :
    ‖bachSum χ x‖ ≤ charBound q x := by
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
  have hχ0 : ∀ n : ℕ, ¬ n.Coprime q → χ n = 0 := fun n hn =>
    MulChar.map_nonunit χ (fun h => hn ((ZMod.isUnit_iff_coprime n q).1 h))
  have hψcop : ∀ n : ℕ, ψ n ≠ 0 → n.Coprime f := fun n hn => by
    have hu : IsUnit (n : ZMod f) := by
      by_contra h
      exact hn (MulChar.map_nonunit ψ h)
    exact (ZMod.isUnit_iff_coprime n f).1 hu
  have hx1 : 1 ≤ x := by omega
  /- the difference `bachSum χ - bachSum ψ` -/
  set E₂ : ℝ := ∑ n ∈ (range x).filter (fun n : ℕ => ¬ n.Coprime q ∧ ψ (n : ZMod f) ≠ 0),
    (Λ n : ℝ) with hE₂d
  have hdiff : ‖bachSum χ x - bachSum ψ x‖ ≤ E₂ := by
    rw [bachSum, bachSum, ← sum_sub_distrib, hE₂d, sum_filter]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    have hnx := mem_range.1 hn
    obtain ⟨hw0, hw1⟩ := weight_mem hnx
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    have hwc : (1 - (n : ℂ) / x) = ((1 - (n : ℝ) / x : ℝ) : ℂ) := by push_cast; ring
    by_cases hc : n.Coprime q
    · rw [hψval n hc]; simp [hc]
    · rw [hχ0 n hc]
      by_cases h0 : ψ n = 0
      · simp [hc, h0]
      · simp only [hc, h0, not_false_eq_true, true_and, ne_eq, ite_true]
        rw [show (Λ n : ℂ) * 0 * (1 - (n : ℂ) / x) - (Λ n : ℂ) * ψ n * (1 - (n : ℂ) / x)
            = -((Λ n : ℝ) : ℂ) * ψ n * ((1 - (n : ℝ) / x : ℝ) : ℂ) by rw [← hwc]; ring,
          norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hΛ, abs_of_nonneg hw0]
        have hnorm : ‖ψ n‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
        calc (Λ n : ℝ) * ‖ψ n‖ * (1 - (n : ℝ) / x) ≤ (Λ n : ℝ) * 1 * 1 := by
              gcongr
          _ = Λ n := by ring
  /- the error sum `E₂` -/
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
  have htri : ‖bachSum χ x‖ ≤ ‖bachSum ψ x‖ + ‖bachSum χ x - bachSum ψ x‖ := by
    have := norm_add_le (bachSum ψ x) (bachSum χ x - bachSum ψ x)
    rwa [add_sub_cancel] at this
  unfold charBound
  linarith

lemma charBound_nonneg (q x : ℕ) (hq : 1 ≤ q) (hx : 1 ≤ x) : 0 ≤ charBound q x := by
  unfold charBound
  have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  positivity

end BachSorenson
