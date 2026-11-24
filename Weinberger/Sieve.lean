import Mathlib

/-!
# The prime-sum upper bound

If a character `ψ` takes the value `−1` at every prime `p < x` outside a set `P`, and only
primes of `P` can have a proper power below `x`, then
`Σ_{m<x} Λ(m)(1 − m/x)(1 + Re ψ(m)) ≤ 2 · #P · log x`:
a prime outside `P` contributes `0`, and the powers of one prime of `P` below `x` contribute at
most `log x` to `Σ Λ(m)`.
-/

namespace Weinberger

open ArithmeticFunction Finset

/-- The weighted sum `Σ_{m<x} Λ(m)(1 − m/x)(1 + Re ψ(m))`. -/
noncomputable def splitSum {N : ℕ} (ψ : DirichletCharacter ℂ N) (x : ℕ) : ℝ :=
  ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re)

/-- The powers of a prime `p` below `x` carry total von Mangoldt weight at most `log x`. -/
theorem sum_vonMangoldt_dvd_le {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 1 ≤ x) :
    ∑ m ∈ range x, (if p ∣ m then (Λ m : ℝ) else 0) ≤ Real.log x := by
  set K := Nat.log p x
  rw [← Finset.sum_filter]
  have hsub : ((range x).filter (fun m => p ∣ m)).filter (fun m => (Λ m : ℝ) ≠ 0)
      ⊆ (p ^ K).divisors := by
    intro m hm
    simp only [mem_filter, mem_range] at hm
    obtain ⟨⟨hmx, hpm⟩, hΛ⟩ := hm
    have hpp : IsPrimePow m := by
      by_contra h
      exact hΛ (by simp [vonMangoldt_apply, h])
    obtain ⟨q, k, hq, hk, rfl⟩ := hpp
    have hq' := hq.nat_prime
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').1 (hp.dvd_of_dvd_pow hpm)
    subst hpq
    rw [Nat.mem_divisors]
    refine ⟨pow_dvd_pow p (Nat.le_log_of_pow_le hp.one_lt hmx.le), pow_ne_zero _ hp.ne_zero⟩
  calc ∑ m ∈ (range x).filter (fun m => p ∣ m), (Λ m : ℝ)
      = ∑ m ∈ ((range x).filter (fun m => p ∣ m)).filter (fun m => (Λ m : ℝ) ≠ 0), (Λ m : ℝ) :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ m ∈ (p ^ K).divisors, (Λ m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = Real.log (p ^ K : ℕ) := by
        rw [vonMangoldt_sum]
    _ ≤ Real.log x := by
        apply Real.log_le_log (by exact_mod_cast pow_pos hp.pos K)
        exact_mod_cast Nat.pow_log_le_self p (by omega)

/-- The main sieve bound. `P` must contain every prime `p < x` with `p * p < x`, and `ψ` must
be `−1` at every prime `p < x` not in `P`. -/
theorem splitSum_le {N : ℕ} (ψ : DirichletCharacter ℂ N) {x : ℕ} (hx : 1 ≤ x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime)
    (hsq : ∀ p, p.Prime → p < x → p * p < x → p ∈ P)
    (hval : ∀ p, p.Prime → p < x → p ∉ P → ψ p = -1) :
    splitSum ψ x ≤ 2 * P.card * Real.log x := by
  have hpt : ∀ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re)
      ≤ 2 * ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) := by
    intro m hm
    rw [mem_range] at hm
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hw0 : 0 ≤ 1 - (m : ℝ) / x := by
      rw [sub_nonneg, div_le_one hxR]; exact_mod_cast hm.le
    have hw1 : 1 - (m : ℝ) / x ≤ 1 := by
      have : 0 ≤ (m : ℝ) / x := by positivity
      linarith
    have hre : (ψ m).re ≤ 1 := by
      have h1 := Complex.re_le_norm (ψ m)
      have h2 : ‖ψ m‖ ≤ 1 := DirichletCharacter.norm_le_one ψ m
      linarith
    have hre' : -1 ≤ (ψ m).re := by
      have h1 := Complex.abs_re_le_norm (ψ m)
      have h2 : ‖ψ m‖ ≤ 1 := DirichletCharacter.norm_le_one ψ m
      have := neg_abs_le (ψ m).re
      linarith
    have hΛ0 : (0 : ℝ) ≤ Λ m := vonMangoldt_nonneg
    have hRHS0 : 0 ≤ ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) :=
      Finset.sum_nonneg fun p _ => by split_ifs <;> simp [hΛ0]
    by_cases hpp : IsPrimePow m
    · set p := m.minFac
      have hm1 : m ≠ 1 := hpp.ne_one
      have hpr : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      by_cases hP : p ∈ P
      · have : (Λ m : ℝ) ≤ ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) := by
          have := Finset.single_le_sum (f := fun q => if q ∣ m then (Λ m : ℝ) else 0)
            (fun q _ => by split_ifs <;> simp [hΛ0]) hP
          simpa [hpm] using this
        have h2 : (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re) ≤ (Λ m : ℝ) * 1 * 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hw1 hΛ0) (by linarith) (by linarith)
          positivity
        linarith
      · -- `m` is a prime outside `P`
        have hmpos : 0 < m := hpp.pos
        have hpx : p < x := lt_of_le_of_lt (Nat.minFac_le hmpos) hm
        have hmp : m = p := by
          have he := hpp.minFac_pow_factorization_eq
          set e := m.factorization p
          have he0 : e ≠ 0 := by
            intro h0; rw [h0, pow_zero] at he; exact hm1 he.symm
          by_contra hne
          have he2 : 2 ≤ e := by
            rcases Nat.lt_or_ge e 2 with h | h
            · exfalso; have : e = 1 := by omega
              rw [this, pow_one] at he; exact hne he.symm
            · exact h
          have : p * p ∣ m := by
            rw [← he, ← pow_two]; exact pow_dvd_pow p he2
          have hle := Nat.le_of_dvd hmpos this
          exact hP (hsq p hpr hpx (by omega))
        have hψ := hval p hpr hpx hP
        have h0 : (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re) = 0 := by
          rw [hmp, hψ]
          simp only [Complex.neg_re, Complex.one_re, add_neg_cancel, mul_zero]
        rw [h0]; linarith
    · have : (Λ m : ℝ) = 0 := by simp [vonMangoldt_apply, hpp]
      have h0 : (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re) = 0 := by
        rw [this]; simp only [zero_mul]
      rw [h0]; linarith
  calc splitSum ψ x ≤ ∑ m ∈ range x, 2 * ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = 2 * ∑ p ∈ P, ∑ m ∈ range x, (if p ∣ m then (Λ m : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * ∑ p ∈ P, Real.log x := by
        gcongr with p hp
        exact sum_vonMangoldt_dvd_le (hPp p hp) hx
    _ = 2 * P.card * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `2 ^ ω(m) ≤ m`. -/
theorem two_pow_card_primeFactors_le {m : ℕ} (hm : m ≠ 0) : 2 ^ m.primeFactors.card ≤ m := by
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

end Weinberger
