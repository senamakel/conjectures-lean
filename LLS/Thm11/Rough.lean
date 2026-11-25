import LLS.Thm11.Common
import LLS.Thm11.IntervalsR
import LLS.Numerics.IntervalsP
import LLS.Numerics.TailP
import LLS.Statement

/-!
# LLS Theorem 1.1 (2) under GRH

If `q ≥ 3000` has no prime factor below `(log q)²`, every proper subgroup `H` of `(ℤ/qℤ)ˣ`
misses a prime `ℓ ≤ (log q)²`.

For such `q`, every prime `p ∣ q` is at least `x` for any `x ≤ (log q)²`, so all prime-power
losses vanish and the loss-free budget `Φ₁` of the prime case applies (`Phi1_nonpos_rough`,
the argument of `LLS.Phi1_nonpos` with the primality of `q` replaced by this). `GoodP 1 q`
(some `64 ≤ x ≤ (log q)²` with `Φ₁(x, log q) > 0`) is certified for `3000 ≤ q < 4096` here
(`LLS.IvR.goodP_rough`), for `2^12 ≤ q < 2^700` by `LLS.IvP.goodP_range` and beyond by
`LLS.goodP_tail`.
-/

namespace LLS.Thm11

open Real Finset

/-- `LLS.Phi1_nonpos` for any modulus whose prime factors are all `≥ x`. -/
theorem Phi1_nonpos_rough (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hbig : ∀ p ∈ q.primeFactors, x ≤ p) (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) :
    Phi1 x (Real.log q) ≤ 0 := by
  classical
  obtain ⟨lf, Z, hlf, hZ0, R, hRq, hlog, h1, h2⟩ := key hGRH χ hχ x hx hval
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hzero : ∀ p ∈ q.primeFactors, llp x p = 0 ∧ lcp x p = 0 := fun p hp =>
    ⟨llp_eq_zero_of_le (Nat.prime_of_mem_primeFactors hp) (hbig p hp),
      lcp_eq_zero_of_le (Nat.prime_of_mem_primeFactors hp) (hbig p hp)⟩
  have hS0 : ∀ S ⊆ q.primeFactors, ∑ p ∈ S, llp x p = 0 ∧ ∑ p ∈ S, lcp x p = 0 :=
    fun S hS => ⟨sum_eq_zero fun p hp => (hzero p (hS hp)).1,
      sum_eq_zero fun p hp => (hzero p (hS hp)).2⟩
  obtain ⟨a1, a2⟩ := hS0 _ subset_rfl
  obtain ⟨b1, b2⟩ := hS0 R hRq
  rw [a1, b1] at h2
  rw [a2, b2] at h1
  have hRlog : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg fun p hp => by
    have := Nat.prime_of_mem_primeFactors (hRq hp)
    exact Real.log_nonneg (by exact_mod_cast this.one_lt.le)
  have hlfL : lf ≤ Real.log q := by linarith
  set s := √(x : ℝ)
  set l := Real.log x
  set den := 1 + 1 / (x : ℝ) - 2 / s
  have hden : 3 / 4 ≤ den := den_pos hxR
  set K := Kc x
  have hKdef : K * den = s + 1 + l / 2 := by
    show Kc x * den = _
    unfold Kc
    exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hK0 : 0 < K := Kc_pos hxR
  have hN : (s + 1 + l / 2) * Z ≤ K * (lf * (1 - 1 / x) - 2 * (l - 2 - 0 - 0) + 2 * Eshift x) := by
    rw [← hKdef]
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    nlinarith
  have hS : (x : ℝ) - 3 / 20 * s - 3 * l - 3 - 0 - 0
      ≤ K * (lf * (1 - 1 / x) - 2 * (l - 2 - 0 - 0) + 2 * Eshift x) + lf / 2 * l
        - 1 / 2 * Real.log Real.pi * l + Etil x := by
    have : (√(x : ℝ) + 1) * Z + (lf + Z) / 2 * l = (s + 1 + l / 2) * Z + lf / 2 * l := by ring
    linarith
  have hkap0 : 0 ≤ kap x := by
    have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    unfold kap; positivity
  have hlf' : K * (lf * (1 - 1 / x)) + lf / 2 * l ≤ kap x * Real.log q := by
    have : K * (lf * (1 - 1 / x)) + lf / 2 * l = kap x * lf := by simp only [kap, K, l]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hlfL hkap0
  unfold Phi1
  change (x : ℝ) - 3 / 20 * s - 3 * l - 3 + 2 * K * (l - 2) - kap x * Real.log q
    - 2 * K * Eshift x + 1 / 2 * Real.log Real.pi * l - Etil x ≤ 0
  have hexp : K * (lf * (1 - 1 / x) - 2 * (l - 2 - 0 - 0) + 2 * Eshift x)
      = K * (lf * (1 - 1 / x)) - 2 * K * (l - 2) + 2 * K * Eshift x := by ring
  linarith

/-- `GoodP 1 q` for every `q ≥ 3000`. -/
theorem goodP_ge_3000 (q : ℕ) (hq : 3000 ≤ q) : GoodP 1 q := by
  rcases lt_or_ge q 4096 with h | h
  · exact IvR.goodP_rough q hq h
  rcases lt_or_ge q (2 ^ 700) with h' | h'
  · exact IvP.goodP_range q (by simpa using h) h'
  · exact goodP_tail q h'

/-- **LLS Theorem 1.1 (2) under GRH.** -/
theorem leastPrimeOutsideSubgroupRough_of_GRH
    (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) : LeastPrimeOutsideSubgroupRough := by
  intro q hq hbig H hH
  have : NeZero q := ⟨by omega⟩
  obtain ⟨x, hx64, hxc, hPhi⟩ := goodP_ge_3000 q hq
  rw [one_mul] at hxc
  by_contra hcon
  push Not at hcon
  have hprime : ∀ ℓ ≤ x, ℓ.Prime → ∀ hc : ℓ.Coprime q, ZMod.unitOfCoprime ℓ hc ∈ H := by
    intro ℓ hℓx hℓ hc
    by_contra hmem
    have := hcon ℓ hℓ hc hmem
    have : (ℓ : ℝ) ≤ x := by exact_mod_cast hℓx
    linarith
  obtain ⟨χ, hχ, hval⟩ := exists_char_of_primes_mem H hH x hprime
  have hbig' : ∀ p ∈ q.primeFactors, x ≤ p := by
    intro p hp
    have := hbig p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    exact_mod_cast hxc.trans this
  have := Phi1_nonpos_rough hGRH χ hχ x hx64 hbig' hval
  linarith

end LLS.Thm11
