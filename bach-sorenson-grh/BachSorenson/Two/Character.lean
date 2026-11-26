import BachSorenson.Two.LogDeriv
import LLS.Losses
import Ankeny.PrimePowers

/-!
# The log-weighted sum of a non-principal character, under GRH

For `χ ≠ 1` mod `q` with inducing primitive character `ψ` mod `f`, and
`S(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) log(x/n)` (`LLS.logSum`):

`‖S(x, χ)‖ ≤ (√x + 1 + log x) Z₂(ψ) + (log q + 2.52) log x + (log² x/2 + 5 log x + 2)
  + ω(q) log² x` (`norm_logSum_le`),

from LLS's log-weighted explicit formula `S(x, ψ) = −Σ_ρ (x^ρ − 1)/ρ² − D(0) log x + Γ̃(x)`
(`LLS.LogAux.log_explicit_formula`), and

`Z₂(ψ) ≤ (11/10)(log q + log 2 − 1.4 + Re L'/L(21/20, χ) + Re L'/L(21/20, χ⁻¹))`
(`Z2_prim_le`), from `Z2_le` with `a = 1/20`, the gamma bound and the imprimitive correction.
-/

namespace BachSorenson.Two

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic Erdos985.Analytic.BoundsAux LLS Finset

/-- `log f + 2 Σ_{p ∣ q, p ∤ f} log p/(p − 1) ≤ log q + log 2`. -/
lemma log_add_two_sum_le {f q : ℕ} (hfq : f ∣ q) (hq : q ≠ 0) :
    Real.log f + 2 * ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f), Real.log p / (p - 1)
      ≤ Real.log q + Real.log 2 := by
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f)
  have h := log_add_sum_log_le hfq hq
  have hterm : ∀ p ∈ R, 2 * (Real.log p / (p - 1)) ≤ Real.log p + (if p = 2 then Real.log 2 else 0) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    by_cases h2 : p = 2
    · subst h2; norm_num; linarith
    · simp only [h2, ↓reduceIte, add_zero]
      have h3 : (3 : ℝ) ≤ p := by
        have := hpp.two_le; have : p ≠ 2 := h2; exact_mod_cast (by omega : 3 ≤ p)
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
  have hs : 2 * ∑ p ∈ R, Real.log p / (p - 1)
      ≤ ∑ p ∈ R, Real.log p + ∑ p ∈ R, (if p = 2 then Real.log 2 else 0) := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_le_sum hterm
  have h2 : ∑ p ∈ R, (if p = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact Real.log_nonneg (by norm_num)
  linarith

/-- The zero sum of the inducing primitive character, bounded through `L'/L(21/20)` of `χ` and
`χ⁻¹`. -/
theorem Z2_prim_le (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    haveI : NeZero χ.conductor := ⟨fun h => NeZero.ne q
      (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))⟩
    Z2 χ.primitiveCharacter ≤ 11 / 10 * (Real.log q + Real.log 2 - 7 / 5
      + (ld χ ((1 + 1 / 20 : ℝ) : ℂ)).re + (ld χ⁻¹ ((1 + 1 / 20 : ℝ) : ℂ)).re) := by
  have : NeZero χ.conductor := ⟨fun h => NeZero.ne q
      (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))⟩
  set ψ := χ.primitiveCharacter
  have hfq : χ.conductor ∣ q := χ.conductor_dvd_level
  have hq0 : q ≠ 0 := NeZero.ne q
  have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hψ1 : ψ ≠ 1 := fun h => hχ (by
    rw [← χ.changeLevel_primitiveCharacter]
    change DirichletCharacter.changeLevel _ ψ = 1
    rw [h, map_one])
  have hψi : ψ⁻¹ ≠ 1 := by simpa using hψ1
  have hlift : DirichletCharacter.changeLevel hfq ψ = χ := χ.changeLevel_primitiveCharacter
  have hlift' : DirichletCharacter.changeLevel hfq ψ⁻¹ = χ⁻¹ := by rw [map_inv, hlift]
  have hs : 1 < (((1 + 1 / 20 : ℝ)) : ℂ).re := by norm_num
  have hZ := Z2_le hGRH hprim hψ1 (a := 1 / 20) (by norm_num)
  have hD : ∀ φ : DirichletCharacter ℂ χ.conductor, φ ≠ 1 →
      (D φ ((1 + 1 / 20 : ℝ) : ℂ)).re = (ld φ ((1 + 1 / 20 : ℝ) : ℂ)).re
        + (gammaLogDeriv φ ((1 + 1 / 20 : ℝ) : ℂ)).re :=
    fun φ hφ => by
      have := logDeriv_LFunction_eq hφ hs
      unfold ld D; rw [this]; simp
  have hc1 := re_ld_le_changeLevel hfq hq0 ψ (a := 1 / 20) (by norm_num)
  have hc2 := re_ld_le_changeLevel hfq hq0 ψ⁻¹ (a := 1 / 20) (by norm_num)
  rw [hlift] at hc1
  rw [hlift'] at hc2
  have hg1 := re_gammaLogDeriv_le ψ
  have hg2 := re_gammaLogDeriv_le ψ⁻¹
  have hlog := log_add_two_sum_le hfq hq0
  rw [hD ψ hψ1, hD ψ⁻¹ hψi] at hZ
  change Z2 ψ ≤ _
  linarith

/-- `Σ_{n ∈ ppF x p} Λ(n) ≤ log x`. -/
lemma sum_ppF_le (x p : ℕ) (hp : p.Prime) (hx : 1 ≤ x) :
    ∑ n ∈ ppF x p, (Λ n : ℝ) ≤ Real.log x := by
  have hsub : ppF x p ⊆ (Icc 1 (Nat.log p x)).image (p ^ ·) := by
    intro n hn
    simp only [ppF, mem_filter, mem_range] at hn
    obtain ⟨hnx, hpp, hmin⟩ := hn
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    have hrp : r = p := by rw [← hmin, Nat.Prime.pow_minFac hr hk.ne']
    subst hrp
    exact mem_image.2 ⟨k, mem_Icc.2 ⟨hk, Nat.le_log_of_pow_le hr.one_lt (by omega)⟩, rfl⟩
  have hcard : (ppF x p).card ≤ Nat.log p x :=
    (card_le_card hsub).trans (card_image_le.trans (by simp))
  have h : ∀ n ∈ ppF x p, (Λ n : ℝ) = Real.log p := by
    intro n hn
    simp only [ppF, mem_filter] at hn
    rw [vonMangoldt_apply, ite_eq_left hn.2.1, hn.2.2]
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul, mul_comm]
  refine (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard : ((ppF x p).card : ℝ) ≤ Nat.log p x)
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))).trans ?_
  exact Ankeny.log_mul_natLog_le x p hp hx

/-- The gamma term of the log-weighted formula: `|Γ̃(x)| ≤ log² x/2 + 5 log x + 2`. -/
lemma norm_lgamma_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ)‖
      ≤ Real.log x ^ 2 / 2 + 5 * Real.log x + 2 := by
  obtain ⟨hs, he⟩ := LogAux.lgammaPart_eq χ x hx
  obtain ⟨g, hg, hg1⟩ := gammaLogDeriv_two χ
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  set T := ∑' k : ℕ, LogAux.ltau x (2 * k + parity χ)
  rw [he, hg, show ((T : ℂ) + (g : ℂ) * (Real.log x : ℂ)) = ((T + g * Real.log x : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hz : Real.pi ^ 2 / 6 ≤ 1.66 := by nlinarith
  have hκ := parity_le_one χ
  -- upper bound
  have hup : T ≤ Real.pi ^ 2 / 6 := by
    refine hasSum_le (fun k => ?_) hs.hasSum LogAux.hasSum_inv_succ_sq
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hκ with h0 | h1
    · rw [h0, add_zero]
      have := LogAux.ltau_le_even (x : ℝ) hx1 k
      split_ifs at this <;> linarith
    · rw [h1]
      have := LogAux.ltau_le_odd (x : ℝ) hx1 k
      split_ifs at this <;> nlinarith
  -- lower bound
  have hlow_term : ∀ k : ℕ, -(if k = 0 then Real.log x ^ 2 / 2 else 0)
      - 2 * Real.log x * (1 / ((k : ℝ) + 1) ^ 2) ≤ LogAux.ltau x (2 * k + parity χ) := by
    intro k
    set m := 2 * k + parity χ with hm
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hq : 0 ≤ 2 * Real.log x * (1 / ((k : ℝ) + 1) ^ 2) := by positivity
    by_cases hm0 : m = 0
    · have hk : k = 0 := by omega
      simp only [LogAux.ltau, hm0, ↓reduceIte, hk]
      nlinarith
    · simp only [LogAux.ltau, hm0, ↓reduceIte]
      have hmk : (k : ℝ) + 1 ≤ m := by
        have : k + 1 ≤ m := by omega
        exact_mod_cast this
      have hm1 : (0 : ℝ) < m := by linarith
      have hxm : 1 / (x : ℝ) ^ m ≤ 1 := by
        rw [div_le_one (by positivity)]; exact one_le_pow₀ hx1
      have h1 : 0 ≤ (1 - 1 / (x : ℝ) ^ m) / (m : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 : Real.log x / (2 + m) - Real.log x / m = -(2 * Real.log x / (m * (m + 2))) := by
        field_simp; ring
      have h3 : 2 * Real.log x / (m * (m + 2)) ≤ 2 * Real.log x * (1 / ((k : ℝ) + 1) ^ 2) := by
        rw [mul_one_div]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      have h4 : 0 ≤ (if k = 0 then Real.log x ^ 2 / 2 else 0) := by split_ifs <;> positivity
      linarith
  have hlowS : HasSum (fun k : ℕ => -(if k = 0 then Real.log x ^ 2 / 2 else 0)
      - 2 * Real.log x * (1 / ((k : ℝ) + 1) ^ 2))
      (-(Real.log x ^ 2 / 2) - 2 * Real.log x * (Real.pi ^ 2 / 6)) :=
    ((hasSum_ite_eq 0 (Real.log x ^ 2 / 2)).neg).sub (LogAux.hasSum_inv_succ_sq.mul_left _)
  have hlow := hasSum_le hlow_term hlowS hs.hasSum
  rw [abs_le] at hg1 ⊢
  have hgl : |g * Real.log x| ≤ Real.log x := by
    rw [abs_mul, abs_of_nonneg hl]; nlinarith [abs_le.2 hg1]
  rw [abs_le] at hgl
  constructor <;> nlinarith

/-- A primitive non-trivial character, under GRH:
`‖S(x, ψ)‖ ≤ (√x + 1 + log x) Z₂ + (log f + 2.52) log x + log² x/2 + 5 log x + 2`. -/
theorem norm_logSum_prim_le (hGRH : DirichletLNonvanishingRightOfHalf) {f : ℕ} [NeZero f]
    {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖logSum ψ x‖ ≤ (√(x : ℝ) + 1 + Real.log x) * Z2 ψ + (Real.log f + 2.52) * Real.log x
      + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2) := by
  set Λf := DirichletCharacter.completedLFunction ψ with hΛf
  obtain ⟨hS1, he⟩ := LogAux.log_explicit_formula hprim hψ x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hterm : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ‖(analyticOrderNatAt Λf ρ : ℂ)
      * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)‖
        ≤ (√(x : ℝ) + 1) * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ
    have hre := completedLFunction_zero_re hGRH hprim hψ ρ.2
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
    have h1 : ‖(x : ℂ) ^ (ρ : ℂ) - 1‖ ≤ √(x : ℝ) + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, show (x : ℂ) = ((x : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hx0, hre,
        Real.sqrt_eq_rpow]
    rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow]
    have hρp : 0 < ‖(ρ : ℂ)‖ ^ 2 := by have := norm_pos_iff.2 hρ0; positivity
    rw [mul_div_assoc', div_le_iff₀ hρp]
    calc (analyticOrderNatAt Λf ρ : ℝ) * ‖(x : ℂ) ^ (ρ : ℂ) - 1‖
        ≤ (analyticOrderNatAt Λf ρ : ℝ) * (√(x : ℝ) + 1) := by gcongr
      _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hρp.ne']; ring
  have hSz := tsum_of_norm_bounded ((hasSum_Z2 hGRH hprim hψ).mul_left (√(x : ℝ) + 1)) hterm
  have hD0 := norm_D_zero_le hGRH hprim hψ
  have hG := norm_lgamma_le ψ x hx
  have hZ0 := Z2_nonneg ψ
  rw [he]
  have hDl : ‖D ψ 0 * (Real.log x : ℂ)‖ ≤ (Real.log f + Z2 ψ + 2.52) * Real.log x := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl]
    exact mul_le_mul_of_nonneg_right hD0 hl
  calc ‖-(∑' ρ : {ρ : ℂ // Λf ρ = 0}, (analyticOrderNatAt Λf ρ : ℂ)
          * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)) - D ψ 0 * (Real.log x : ℂ)
          + (LogAux.lgammaPart ψ x + gammaLogDeriv ψ 2 * (Real.log x : ℂ))‖
        ≤ ‖∑' ρ : {ρ : ℂ // Λf ρ = 0}, (analyticOrderNatAt Λf ρ : ℂ)
          * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)‖ + ‖D ψ 0 * (Real.log x : ℂ)‖
          + ‖LogAux.lgammaPart ψ x + gammaLogDeriv ψ 2 * (Real.log x : ℂ)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ (√(x : ℝ) + 1) * Z2 ψ + (Real.log f + Z2 ψ + 2.52) * Real.log x
          + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2) := by gcongr
    _ = _ := by ring

/-- Lifting to modulus `q` changes the log-weighted sum by at most `ω(q) log² x`. -/
theorem norm_logSum_changeLevel_sub_le {f q : ℕ} (hfq : f ∣ q) (hq : q ≠ 0)
    (ψ : DirichletCharacter ℂ f) (x : ℕ) (hx : 1 ≤ x) :
    ‖logSum (DirichletCharacter.changeLevel hfq ψ) x - logSum ψ x‖
      ≤ q.primeFactors.card * Real.log x ^ 2 := by
  classical
  set χ := DirichletCharacter.changeLevel hfq ψ with hχdef
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hw : ∀ n ≤ x, 0 ≤ Real.log ((x : ℝ) / n) := fun n hn => by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by exact_mod_cast hn0)]
      simpa using (show (n : ℝ) ≤ x by exact_mod_cast hn)
  have h1 : ‖logSum χ x - logSum ψ x‖
      ≤ ∑ n ∈ (range (x + 1)).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) * Real.log ((x : ℝ) / n) := by
    rw [logSum, logSum, ← sum_sub_distrib, sum_filter]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    have hnx : n ≤ x := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    have hwn := hw n hnx
    by_cases hc : n.Coprime q
    · have hval : χ n = ψ n := by
        have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hfq (a := (n : ℤ))
          (Nat.isCoprime_iff_coprime.2 hc)
        simpa [hχdef] using this
      simp [hc, hval]
    · have hχ0 : χ n = 0 :=
        MulChar.map_nonunit χ (fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h))
      simp only [hc, not_false_eq_true, ↓reduceIte, hχ0, mul_zero, zero_mul, zero_sub, norm_neg]
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hΛ,
        Real.norm_of_nonneg hwn]
      have := DirichletCharacter.norm_le_one ψ n
      nlinarith [mul_nonneg (mul_nonneg hΛ (sub_nonneg.2 this)) hwn]
  have h2 := sum_le_sum_ppF x (fun n => ¬ n.Coprime q) q.primeFactors
    (fun n => Real.log ((x : ℝ) / n)) hw (fun n _ hc hpp => by
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rw [Nat.Prime.pow_minFac hr hk.ne', Nat.mem_primeFactors]
      refine ⟨hr, ?_, hq⟩
      by_contra hd
      exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd)))
  have h3 : ∀ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      ≤ Real.log x * Real.log x := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    calc ∑ n ∈ ppF x p, (Λ n : ℝ) * Real.log ((x : ℝ) / n)
        ≤ ∑ n ∈ ppF x p, (Λ n : ℝ) * Real.log x := by
          refine sum_le_sum fun n hn => ?_
          simp only [ppF, mem_filter, mem_range] at hn
          have hn0 : 0 < n := hn.2.1.pos
          apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ (by exact_mod_cast hn0)]
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
          nlinarith
      _ = (∑ n ∈ ppF x p, (Λ n : ℝ)) * Real.log x := by rw [sum_mul]
      _ ≤ Real.log x * Real.log x :=
          mul_le_mul_of_nonneg_right (sum_ppF_le x p hpp hx) hl
  calc ‖logSum χ x - logSum ψ x‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x * Real.log x := sum_le_sum h3
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end BachSorenson.Two
