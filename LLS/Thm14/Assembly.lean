import LLS.Thm14.PerChar
import LLS.Thm14.Orth
import LLS.Thm14.PsiUp
import LLS.Thm14.Squares
import LLS.Key

/-!
# The main inequality for LLS Theorem 1.4

Let `m = |H̃|`, `s ≥ 31622`, `X = s²`, `s² ≤ 2N²`, and suppose no prime `p ≤ X` lies in the
coset `aH`. Then (`LLS.Thm14.main_ineq`)

  `X − (3/20)s − 3 log X − 3 − Σ_{p ∣ q} llp(X, p)
     ≤ m (2ψ⁺(s) + 2ψ⁺(N)) + (m − 1) Pc + 2A P₂(X)`,

with `ψ⁺(y) = y + (3/20)√y + 4 log y + 2`. The left side bounds `Re S(X, χ₀)` from below; by
orthogonality `m Σ_{n ≤ X, n ∈ aH} Λ(n) log(X/n) = Σ_{χ ∈ H̃} χ(a⁻¹) S(X, χ)`, whose left side
only sees prime powers `p^k`, `k ≥ 2` (LLS (4.10)), and the non-principal characters are bounded
by `LLS.Thm14.norm_logSum_char`; their Cesàro sums add up to at least `−P₂(X)`.
-/

namespace LLS.Thm14

open Complex ArithmeticFunction Finset Erdos985

/-- `ψ⁺(y) = y + (3/20)√y + 4 log y + 2`. -/
noncomputable def psiU (y : ℝ) : ℝ := y + 3 / 20 * √y + 4 * Real.log y + 2

lemma P2sum_eq_succ (x : ℕ) :
    LLS.P2sum x = ∑ n ∈ range (x + 1), (Λ n : ℝ) * (1 / (n : ℝ) * (1 - (n : ℝ) / x)) := by
  rw [LLS.P2sum, sum_range_succ]
  have hlast : (Λ x : ℝ) * (1 / (x : ℝ) * (1 - (x : ℝ) / x)) = 0 := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
      simp [div_self this]
  rw [hlast, add_zero]
  refine sum_congr rfl fun n _ => ?_
  ring

theorem main_ineq (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) (s N : ℕ) (hs : 31622 ≤ s) (hN : s ^ 2 ≤ 2 * N ^ 2)
    (hno : ∀ p ≤ s ^ 2, p.Prime → ∀ hp : p.Coprime q, a⁻¹ * ZMod.unitOfCoprime p hp ∉ H) :
    ((s ^ 2 : ℕ) : ℝ) - 3 / 20 * s - 3 * Real.log ((s ^ 2 : ℕ) : ℝ) - 3
        - ∑ p ∈ q.primeFactors, llp (s ^ 2) p
      ≤ ((Htil H).card : ℝ) * (2 * psiU s + 2 * psiU N)
        + (((Htil H).card : ℝ) - 1) * Pc (Real.log q) s (Real.log ((s ^ 2 : ℕ) : ℝ))
        + 2 * Acoef s * LLS.P2sum (s ^ 2) := by
  classical
  set X := s ^ 2 with hXdef
  set m := (Htil H).card with hm
  have hq0 : q ≠ 0 := NeZero.ne q
  have hsR : (31622 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hXR : ((X : ℕ) : ℝ) = (s : ℝ) ^ 2 := by rw [hXdef]; push_cast; ring
  have hsqX : √((X : ℕ) : ℝ) = s := by rw [hXR, Real.sqrt_sq hs0.le]
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; nlinarith
    · exact h
  have hA0 : 0 ≤ Acoef s := by unfold Acoef; positivity
  set w : ℕ → ℝ := fun n => Real.log ((X : ℝ) / n)
  -- the coset sum
  set T := ∑ n ∈ range (X + 1), (Λ n : ℝ) * w n
      * (if h : n.Coprime q then (if a⁻¹ * ZMod.unitOfCoprime n h ∈ H then (1 : ℝ) else 0)
          else 0) with hT
  have horth : ∑ χ ∈ Htil H, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * LLS.logSum χ X
      = ((m * T : ℝ) : ℂ) := by
    simp only [LLS.logSum, mul_sum]
    rw [sum_comm]
    rw [hT, mul_sum, Complex.ofReal_sum]
    refine sum_congr rfl fun n _ => ?_
    have e : ∑ χ ∈ Htil H, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * ((Λ n : ℂ) * χ n * (w n : ℂ))
        = (Λ n : ℂ) * (w n : ℂ) * ∑ χ ∈ Htil H, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * χ n := by
      rw [mul_sum]; refine sum_congr rfl fun χ _ => by ring
    simp only [w] at e ⊢
    rw [e, sum_Htil_coset]
    split_ifs <;> push_cast <;> ring
  -- upper bound for `T`
  have hT2 : T ≤ 2 * psiU s + 2 * psiU N := by
    have h1 : T ≤ ∑ n ∈ (range (X + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        (Λ n : ℝ) * Real.log (((X : ℕ) : ℝ) / n) := by
      rw [hT, sum_filter]
      refine sum_le_sum fun n hn => ?_
      have hnx : n ≤ X := Nat.lt_succ_iff.1 (mem_range.1 hn)
      have hlw : 0 ≤ (Λ n : ℝ) * w n := mul_nonneg vonMangoldt_nonneg (log_div_nonneg hnx)
      by_cases hpp : IsPrimePow n ∧ ¬ n.Prime
      · rw [if_pos hpp]
        split_ifs <;> simp [w] <;> nlinarith
      · rw [if_neg hpp]
        by_cases hΛ : (Λ n : ℝ) = 0
        · simp [hΛ]
        · have hp : IsPrimePow n := by
            by_contra h; exact hΛ (by rw [vonMangoldt_apply, if_neg h])
          have hpr : n.Prime := by by_contra h; exact hpp ⟨hp, h⟩
          split_ifs with hc hmem
          · exact absurd hmem (hno n hnx hpr hc)
          · simp
          · simp
    have h2 := sum_sq_pp_le s N (by omega) hN
    have h3 := psiLog_le hGRH s (by omega)
    have h4 := psiLog_le hGRH N hN1
    unfold psiU
    rw [← hXdef] at h2
    linarith
  -- the principal character
  have hprin : ((X : ℕ) : ℝ) - 3 / 20 * s - 3 * Real.log ((X : ℕ) : ℝ) - 3
      - ∑ p ∈ q.primeFactors, llp X p ≤ (LLS.logSum (1 : DirichletCharacter ℂ q) X).re := by
    have hPL := LLS.psiLog_ge hGRH X hX1
    rw [hsqX] at hPL
    have := LLS.sum_re_ge (1 : DirichletCharacter ℂ q) dvd_rfl hq0 X
      (fun n => Real.log ((X : ℝ) / n)) (fun n hn => log_div_nonneg hn)
      (fun n _ hc => by
        have : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).2 hc
        exact MulChar.one_apply this)
    have hempty : q.primeFactors.filter (fun p => ¬ p ∣ q) = ∅ :=
      filter_eq_empty_iff.2 fun p hp => not_not.2 (Nat.dvd_of_mem_primeFactors hp)
    rw [hempty, sum_empty] at this
    rw [LLS.re_logSum_eq]
    simp only [llp] at *
    linarith
  -- the non-principal characters
  have h1mem := one_mem_Htil H
  set E := (Htil H).erase 1
  have hcardE : (E.card : ℝ) = (m : ℝ) - 1 := by
    have : 1 ≤ m := card_pos.2 ⟨1, h1mem⟩
    rw [card_erase_of_mem h1mem, ← hm, Nat.cast_sub this, Nat.cast_one]
  have hnp : ∑ χ ∈ E, ‖LLS.logSum χ X‖
      ≤ ∑ χ ∈ E, (Pc (Real.log q) s (Real.log ((X : ℕ) : ℝ))
          - 2 * Acoef s * (LLS.cesShift χ X).re) :=
    sum_le_sum fun χ hχ => norm_logSum_char hGRH χ (ne_of_mem_erase hχ) s hs
  have hces : -(LLS.P2sum X) ≤ ∑ χ ∈ E, (LLS.cesShift χ X).re := by
    simp only [cesShift_eq_succ]
    rw [← Complex.re_sum, sum_comm, Complex.re_sum, P2sum_eq_succ, ← sum_neg_distrib]
    refine sum_le_sum fun n hn => ?_
    have hnx : n ≤ X := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hw : 0 ≤ (Λ n : ℝ) * (1 / (n : ℝ) * (1 - (n : ℝ) / X)) :=
      mul_nonneg vonMangoldt_nonneg (ces_weight_nonneg hnx)
    have e : ∑ χ ∈ E, (Λ n : ℂ) * χ n * ((1 / (n : ℝ) * (1 - (n : ℝ) / X) : ℝ) : ℂ)
        = (((Λ n : ℝ) * (1 / (n : ℝ) * (1 - (n : ℝ) / X)) : ℝ) : ℂ) * ∑ χ ∈ E, χ n := by
      rw [mul_sum]; refine sum_congr rfl fun χ _ => ?_; push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    have := re_sum_Htil_ne_one_ge H n
    nlinarith
  -- combine
  have hsplit := add_sum_erase (Htil H)
    (fun χ => χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * LLS.logSum χ X) h1mem
  rw [horth] at hsplit
  have hre := congrArg Complex.re hsplit
  rw [Complex.add_re, Complex.ofReal_re] at hre
  simp only [MulChar.one_apply_coe, one_mul] at hre
  have hbound : -(∑ χ ∈ E, ‖LLS.logSum χ X‖)
      ≤ (∑ χ ∈ E, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * LLS.logSum χ X).re := by
    have h := (Complex.abs_re_le_norm (∑ χ ∈ E, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * LLS.logSum χ X))
    have h2 : ‖∑ χ ∈ E, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * LLS.logSum χ X‖
        ≤ ∑ χ ∈ E, ‖LLS.logSum χ X‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ => ?_)
      rw [norm_mul]
      have := DirichletCharacter.norm_le_one χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q)
      have := norm_nonneg (LLS.logSum χ X)
      nlinarith
    have := neg_abs_le (∑ χ ∈ E, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * LLS.logSum χ X).re
    linarith
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcardE, ← mul_sum] at hnp
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmT := mul_le_mul_of_nonneg_left hT2 hm0
  have hAc := mul_le_mul_of_nonneg_left hces (show 0 ≤ 2 * Acoef s by linarith)
  linarith

end LLS.Thm14
