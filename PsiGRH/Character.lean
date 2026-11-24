import PsiGRH.Imprimitive

/-!
# The bound for every character (Montgomery–Vaughan (13.19))

`psiChar_general_bound`: reduce `χ` mod `q` to its primitive character `χ*` mod the conductor
`d ∣ q` (`norm_psiChar_sub_primitive_le`, a loss of `ω(q) log x ≤ 2 log x log qx`) and apply
`psiChar_primitive_bound` at level `d ≤ q`:

`|ψ(x, χ) − E₀(χ) x| ≤ A √x (log x)(log qx) + B log²(qx) + 2 (log x)(log qx)`.

`psiCharBound_of_GRH`: when `log qx ≤ √x log x` this is `≤ (A + B + 2) √x (log x)(log qx)`.
Otherwise `√x < 2 log qx`, and the trivial bound `x log x + x ≤ 3 x log x ≤ 6 √x (log x)(log qx)`
suffices. So `PsiCharBound (A + B + 8)`.
-/

namespace PsiGRH

open DirichletCharacter

theorem psiChar_general_bound (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
      2 ≤ x → ‖psiChar χ x - mainTerm χ x‖ ≤
        A * Real.sqrt x * Real.log x * Real.log (q * x) + B * Real.log (q * x) ^ 2 +
          2 * Real.log x * Real.log (q * x) := by
  obtain ⟨A, B, hA, hB, h⟩ := psiChar_primitive_bound hGRH hEF hZ
  refine ⟨A, B, hA, hB, fun q _ χ x hx => ?_⟩
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hx0 : 0 < x := by linarith
  have hl2 := Real.log_two_gt_d9
  have hℓ : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hd : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hd1 : (1 : ℝ) ≤ χ.conductor := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hLd : Real.log (χ.conductor * x) ≤ Real.log (q * x) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hLd0 : 0 ≤ Real.log (χ.conductor * x) := Real.log_nonneg (by nlinarith)
  have hP := h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive x hx
  rw [mainTerm_primitiveCharacter] at hP
  have hI := norm_psiChar_sub_primitive_le χ (by linarith : (1 : ℝ) ≤ x)
  have hω := card_primeFactors_mul_log_two_le (NeZero.ne q)
  have hLsplit : Real.log (q * x) = Real.log q + Real.log x := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hωb : (q.primeFactors.card : ℝ) * Real.log x ≤ 2 * Real.log x * Real.log (q * x) := by
    have : (q.primeFactors.card : ℝ) ≤ 2 * Real.log (q * x) := by
      have hc : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
      nlinarith
    have hlx : 0 ≤ Real.log x := by linarith
    nlinarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlx : 0 ≤ Real.log x := by linarith
  have hmain : A * Real.sqrt x * Real.log x * Real.log (χ.conductor * x) +
      B * Real.log (χ.conductor * x) ^ 2 ≤
        A * Real.sqrt x * Real.log x * Real.log (q * x) + B * Real.log (q * x) ^ 2 := by
    gcongr
  calc ‖psiChar χ x - mainTerm χ x‖
      ≤ ‖psiChar χ x - psiChar χ.primitiveCharacter x‖ +
          ‖psiChar χ.primitiveCharacter x - mainTerm χ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- Montgomery–Vaughan (13.19), uniform in `q`, from GRH and the two cited inputs. -/
theorem psiCharBound_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) :
    ∃ C : ℝ, 0 < C ∧ PsiCharBound C := by
  obtain ⟨A, B, hA, hB, h⟩ := psiChar_general_bound hGRH hEF hZ
  refine ⟨A + B + 8, by positivity, fun q _ χ x hx => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hl2 := Real.log_two_gt_d9
  set ℓ := Real.log x with hℓdef
  set L := Real.log (q * x) with hLdef
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hx
  have hℓL : ℓ ≤ L := Real.log_le_log (by linarith) (by nlinarith)
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hℓ0 : 0 < ℓ := by linarith
  have hL0 : 0 < L := by linarith
  rcases le_or_gt L (Real.sqrt x * ℓ) with hcase | hcase
  · -- the analytic bound
    have h1 := h q χ x hx
    have hBL : B * L ^ 2 ≤ B * (Real.sqrt x * ℓ * L) := by
      have : L ^ 2 ≤ Real.sqrt x * ℓ * L := by nlinarith
      gcongr
    have h2L : 2 * ℓ * L ≤ 2 * (Real.sqrt x * ℓ * L) := by
      have : ℓ * L ≤ Real.sqrt x * ℓ * L := by
        have : 0 ≤ ℓ * L := by positivity
        nlinarith
      linarith
    calc _ ≤ A * Real.sqrt x * ℓ * L + B * L ^ 2 + 2 * ℓ * L := h1
      _ ≤ A * Real.sqrt x * ℓ * L + B * (Real.sqrt x * ℓ * L) + 2 * (Real.sqrt x * ℓ * L) := by
          linarith
      _ ≤ (A + B + 8) * Real.sqrt x * ℓ * L := by
          have : 0 ≤ Real.sqrt x * ℓ * L := by positivity
          nlinarith
  · -- the trivial bound
    have h1 := norm_psiChar_sub_le_trivial χ (by linarith : (1 : ℝ) ≤ x)
    have hsL : Real.sqrt x ≤ 2 * L := by nlinarith
    have hxℓ : x ≤ 2 * (x * ℓ) := by nlinarith
    have hxl : x * ℓ ≤ 2 * (Real.sqrt x * ℓ * L) := by
      calc x * ℓ = Real.sqrt x * Real.sqrt x * ℓ := by rw [hsq]
        _ ≤ Real.sqrt x * (2 * L) * ℓ := by gcongr
        _ = 2 * (Real.sqrt x * ℓ * L) := by ring
    calc _ ≤ x * ℓ + x := h1
      _ ≤ 6 * (Real.sqrt x * ℓ * L) := by linarith
      _ ≤ (A + B + 8) * Real.sqrt x * ℓ * L := by
          have : 0 ≤ Real.sqrt x * ℓ * L := by positivity
          nlinarith

/-- The `log²(qx)` shape, from `PsiCharBound` and `log x ≤ log qx`. -/
theorem psiCharLogSqBound_of_psiCharBound {C : ℝ} (hC : 0 < C) (h : PsiCharBound C) :
    PsiCharLogSqBound C := by
  intro q _ χ x hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hℓL : Real.log x ≤ Real.log (q * x) := Real.log_le_log (by linarith) (by nlinarith)
  have hℓ0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  refine (h q χ x hx).trans ?_
  have hL0 : 0 ≤ Real.log (q * x) := hℓ0.trans hℓL
  calc C * Real.sqrt x * Real.log x * Real.log (q * x)
      ≤ C * Real.sqrt x * Real.log (q * x) * Real.log (q * x) := by gcongr
    _ = C * Real.sqrt x * Real.log (q * x) ^ 2 := by ring

end PsiGRH
