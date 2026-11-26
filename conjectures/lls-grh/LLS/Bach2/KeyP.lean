import LLS.Key

/-!
# The key inequality with a general Cesàro lower bound

`LLS.keyP` is `LLS.key` with the unconditional bound `Σ_{n<x} Λ(n)/n (1 − n/x) ≥ log x − 2`
replaced by any lower bound `Pc` (used with `Pc = log x − 1.6`, verified by computation for
`x ≤ 1000` in `LLS.Bach2.Mertens`).
-/

namespace LLS

open Complex ArithmeticFunction Finset Erdos985

/-- **The key inequality**, with any lower bound `Pc` for the Cesàro sum of `Λ(n)/n`. -/
theorem keyP (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ)
    (hPc' : Pc ≤ ∑ n ∈ range (x + 1), (Λ n : ℝ) * (1 / (n : ℝ) * (1 - (n : ℝ) / x))) :
    ∃ lf Z : ℝ, 0 ≤ lf ∧ 0 ≤ Z ∧ ∃ R ⊆ q.primeFactors,
      lf + ∑ p ∈ R, Real.log p ≤ Real.log q ∧
      Z * (1 + 1 / x - 2 / √(x : ℝ)) ≤ lf * (1 - 1 / x)
        - 2 * (Pc - ∑ p ∈ q.primeFactors, lcp x p - ∑ p ∈ R, lcp x p)
        + 2 * Eshift x ∧
      (x : ℝ) - 3 / 20 * √(x : ℝ) - 3 * Real.log x - 3
          - ∑ p ∈ q.primeFactors, llp x p - ∑ p ∈ R, llp x p
        ≤ (√(x : ℝ) + 1) * Z + (lf + Z) / 2 * Real.log x
          - 1 / 2 * Real.log Real.pi * Real.log x + Etil x := by
  classical
  set f := χ.conductor with hf
  have hfq : f ∣ q := χ.conductor_dvd_level
  have hq0 : q ≠ 0 := NeZero.ne q
  have hf0 : f ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hfq))
  have : NeZero f := ⟨hf0⟩
  set ψ := χ.primitiveCharacter
  have hψprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hψ1 : ψ ≠ 1 := fun h => hχ (by
    rw [← χ.changeLevel_primitiveCharacter]
    change DirichletCharacter.changeLevel _ ψ = 1
    rw [h, map_one])
  have hψi1 : ψ⁻¹ ≠ 1 := by simpa using hψ1
  have hψiprim : ψ⁻¹.IsPrimitive := hψprim.inv
  have hψval : ∀ n : ℕ, n.Coprime q → ψ n = χ n := fun n hn => by
    have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.2 hn)
    simpa using this
  have h1 : ∀ n ≤ x, n.Coprime q → ψ n = 1 := fun n hn hc => by
    rw [hψval n hc, hval n hn hc]
  have h1i : ∀ n ≤ x, n.Coprime q → ψ⁻¹ n = 1 := fun n hn hc => by
    rw [MulChar.inv_apply_eq_inv', h1 n hn hc, inv_one]
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f) with hR
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : 1 ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  /- lower bounds -/
  have hPL := psiLog_ge hGRH x hx1
  have lowS : ∀ φ : DirichletCharacter ℂ f, (∀ n ≤ x, n.Coprime q → φ n = 1) →
      (x : ℝ) - 3 / 20 * √(x : ℝ) - 3 * Real.log x - 3
          - ∑ p ∈ q.primeFactors, llp x p - ∑ p ∈ R, llp x p ≤ (logSum φ x).re := by
    intro φ hφ
    have := sum_re_ge φ hfq hq0 x (fun n => Real.log ((x : ℝ) / n))
      (fun n hn => log_div_nonneg hn) hφ
    rw [re_logSum_eq]
    simp only [llp, hR] at *
    linarith
  have lowC : ∀ φ : DirichletCharacter ℂ f, (∀ n ≤ x, n.Coprime q → φ n = 1) →
      Pc - ∑ p ∈ q.primeFactors, lcp x p - ∑ p ∈ R, lcp x p
        ≤ (cesShift φ x).re := by
    intro φ hφ
    have := sum_re_ge φ hfq hq0 x (fun n => 1 / (n : ℝ) * (1 - (n : ℝ) / x))
      (fun n hn => ces_weight_nonneg hn) hφ
    rw [re_cesShift_eq]
    simp only [lcp, hR] at *
    linarith
  /- upper bounds -/
  have uS := re_logSum_le hGRH hψprim hψ1 x hx1
  have uSi := re_logSum_le hGRH hψiprim hψi1 x hx1
  have uC := re_cesShift_le hGRH hψprim hψ1 x hx2
  have uCi := re_cesShift_le hGRH hψiprim hψi1 x hx2
  rw [inv_inv] at uSi uCi
  obtain ⟨-, hZ⟩ := Z2_eq hGRH hψprim hψ1
  obtain ⟨-, hZi⟩ := Z2_eq hGRH hψiprim hψi1
  rw [inv_inv] at hZi
  set U := (D ψ 1).re
  set V := (D ψ⁻¹ 1).re
  set Z := Z2 ψ
  have hZZ : Z2 ψ⁻¹ = Z := by rw [hZi, hZ]; ring
  rw [hZZ] at uSi uCi
  set lf := Real.log f
  have hlf : 0 ≤ lf := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hf0)
  refine ⟨lf, Z, hlf, Z2_nonneg ψ, R, filter_subset _ _, log_add_sum_log_le hfq hq0, ?_, ?_⟩
  · have l1 := lowC ψ h1
    have l2 := lowC ψ⁻¹ h1i
    set a := 1 / (x : ℝ)
    set b := 1 / √(x : ℝ)
    have e1 : (lf + V) / (x : ℝ) = (lf + V) * a := by simp [a, div_eq_mul_inv]
    have e2 : (lf + U) / (x : ℝ) = (lf + U) * a := by simp [a, div_eq_mul_inv]
    have e3 : Z / √(x : ℝ) = Z * b := by simp [b, div_eq_mul_inv]
    have e4 : 2 / √(x : ℝ) = 2 * b := by simp [b, div_eq_mul_inv]
    rw [e1, e3] at uC
    rw [e2, e3] at uCi
    rw [e4]
    have hUV : U + V = Z - lf := by rw [hZ]; ring
    have hUVa : U * a + V * a = Z * a - lf * a := by rw [← add_mul, hUV, sub_mul]
    linarith
  · have l1 := lowS ψ h1
    have l2 := lowS ψ⁻¹ h1i
    have hUV : U + V = Z - lf := by rw [hZ]; ring
    have hUVl : U * Real.log x + V * Real.log x = Z * Real.log x - lf * Real.log x := by
      rw [← add_mul, hUV, sub_mul]
    linarith

end LLS
