import LLS.Thm14.Gamma
import LLS.Analytic.LogFormula
import LLS.Sharp.AssemblyAux.Shift
import LLS.L1.Assembly

/-!
# Absolute-value bounds for a primitive character under GRH

For `ψ` primitive and non-trivial mod `f`, with `V = ½ log f + D(1, ψ)` and
`V' = ½ log f + D(1, ψ⁻¹)` (LLS's `ξ'/ξ(1, ψ)` and `−ξ'/ξ(0, ψ)`):

* `LLS.Thm14.shift_complex`: `V + V'/x = ½ log f (1 − 1/x) − S'(x, ψ) − Z + Γₛ(x)`, `|Z| ≤ Z₂/√x`;
* `LLS.Thm14.maxV_le`: `max(|V|, |V'|)(1 − 1/x − 2/√x) ≤ ½ log f (1 − 1/x) + P₂(x) + |Γₛ|`;
* `LLS.Thm14.norm_logSum_le`: `|S(x, ψ)| ≤ (√x + 1) Z₂ + |V'| log x + ½ log x max(log f − 3,
  log x + 2) + 5/4`, from `S = −Σ_ρ m_ρ(x^ρ − 1)/ρ² + V' log x + (½ log f log x + Γ̃)`.
-/

namespace LLS.Thm14

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic LLS.ShiftAux

variable {N : ℕ} [NeZero N]

lemma norm_cesShift_le {M : ℕ} (φ : DirichletCharacter ℂ M) (x : ℕ) :
    ‖LLS.cesShift φ x‖ ≤ LLS.P2sum x := by
  rw [LLS.cesShift]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hnx : n < x := Finset.mem_range.1 hn
  have hw : 0 ≤ (Λ n : ℝ) / n * (1 - (n : ℝ) / x) := by
    have : (n : ℝ) / x ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (show 0 < x by omega))]; exact_mod_cast hnx.le
    have : 0 ≤ (Λ n : ℝ) / n := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    nlinarith
  have e : (Λ n : ℂ) * φ n / n * (1 - (n : ℂ) / x)
      = (((Λ n : ℝ) / n * (1 - (n : ℝ) / x) : ℝ) : ℂ) * φ n := by push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  have := DirichletCharacter.norm_le_one φ n
  nlinarith

/-- The shift identity in complex form. -/
theorem shift_complex (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ∃ Z : ℂ, ‖Z‖ ≤ LLS.Z2 χ / √(x : ℝ) ∧
      ((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ 1
          + (((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ⁻¹ 1) / x
        = ((1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) : ℝ) : ℂ) - LLS.cesShift χ x - Z
          + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3) := by
  obtain ⟨Z, hZ, hZeq⟩ := zeroPart_eq hGRH hprim hχ x hx
  have hid := shift_identity hGRH hprim hχ x hx
  have hc3 := logDeriv_LFunction_eq hχ (s := 3) (by norm_num)
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := 1)
    (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) (by norm_num))
  rw [sub_self] at hFE
  have hD0 : LLS.D χ 0 = -((Real.log N : ℂ) + LLS.D χ⁻¹ 1) := by
    unfold LLS.D; rw [← hFE]; ring
  have hmain : LLS.cesShift χ x = -LLS.D χ 1 + LLS.D χ 0 / x - Z
      + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3) := by
    rw [hid, hZeq, hc3]
    unfold LLS.D
    ring
  refine ⟨Z, hZ, ?_⟩
  rw [hmain, hD0]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  push_cast
  field_simp
  ring

lemma Z2_eq_twoV (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LLS.Z2 χ = 2 * (((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ 1).re := by
  rw [LLS.Sharp.AssemblyAux.Z2_eq_two hGRH hprim hχ, add_re, ofReal_re]; ring

lemma Z2_inv (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) : LLS.Z2 χ⁻¹ = LLS.Z2 χ := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  obtain ⟨-, hZ⟩ := LLS.Z2_eq hGRH hprim hχ
  obtain ⟨-, hZi⟩ := LLS.Z2_eq hGRH hprim.inv hχi
  rw [inv_inv] at hZi
  rw [hZi, hZ]; ring

/-- `max(|V|, |V'|) (1 − 1/x − 2/√x) ≤ ½ log f (1 − 1/x) + P₂(x) + G₀`. -/
theorem maxV_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) (G0 : ℝ)
    (hG : max |LLS.Sharp.ELpar (parity χ) x| |LLS.Sharp.EUpar (parity χ) x| ≤ G0) :
    max ‖((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ 1‖ ‖((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ⁻¹ 1‖
        * (1 - 1 / (x : ℝ) - 2 / √(x : ℝ))
      ≤ 1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) + LLS.P2sum x + G0 := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  set V := ((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ 1
  set V' := ((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ⁻¹ 1
  set M := max ‖V‖ ‖V'‖
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
  have hG' : max |LLS.Sharp.ELpar (parity χ⁻¹) x| |LLS.Sharp.EUpar (parity χ⁻¹) x| ≤ G0 := by
    rwa [LLS.Sharp.AssemblyAux.parity_inv]
  -- one direction for a primitive character and its inverse
  have key : ∀ (φ : DirichletCharacter ℂ N), φ.IsPrimitive → φ ≠ 1 →
      max |LLS.Sharp.ELpar (parity φ) x| |LLS.Sharp.EUpar (parity φ) x| ≤ G0 →
      LLS.Z2 φ = LLS.Z2 χ →
      ‖((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ 1‖
        ≤ ‖((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ⁻¹ 1‖ / x
          + 1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) + LLS.P2sum x + LLS.Z2 χ / √(x : ℝ) + G0 := by
    intro φ hp h1 hGφ hZ
    obtain ⟨Z, hZb, he⟩ := shift_complex hGRH hp h1 x hx
    have hV : ((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ 1
        = ((1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) : ℝ) : ℂ) - LLS.cesShift φ x - Z
          + (gammaPartS φ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv φ 3)
          - (((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ⁻¹ 1) / x := by rw [← he]; ring
    rw [hV]
    have hlN : 0 ≤ 1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) := by
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one hx0]; exact_mod_cast hx
      have := Real.log_natCast_nonneg N
      positivity
    have n1 := norm_cesShift_le φ x
    have n2 := norm_shiftGamma_le φ x hx
    have n3 : ‖(((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ⁻¹ 1) / (x : ℂ)‖
        = ‖((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ⁻¹ 1‖ / x := by
      rw [norm_div, Complex.norm_natCast]
    rw [hZ] at hZb
    calc _ ≤ ‖((1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) : ℝ) : ℂ)‖ + ‖LLS.cesShift φ x‖ + ‖Z‖
          + ‖gammaPartS φ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv φ 3‖
          + ‖(((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D φ⁻¹ 1) / (x : ℂ)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_sub_le _ _
      _ ≤ _ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlN, n3]
          linarith
  have k1 := key χ hprim hχ hG rfl
  have k2 := key χ⁻¹ hprim.inv hχi hG' (Z2_inv hGRH hprim hχ)
  rw [inv_inv] at k2
  have hZ2 : LLS.Z2 χ ≤ 2 * M := by
    rw [Z2_eq_twoV hGRH hprim hχ]
    have := Complex.re_le_norm V
    have := le_max_left ‖V‖ ‖V'‖
    linarith
  have hZx : LLS.Z2 χ / √(x : ℝ) ≤ 2 * M / √(x : ℝ) := div_le_div_of_nonneg_right hZ2 hsx.le
  have hMx : ∀ y : ℝ, y ≤ M → y / x ≤ M / x := fun y hy => div_le_div_of_nonneg_right hy hx0.le
  have h1 := hMx ‖V'‖ (le_max_right _ _)
  have h2 := hMx ‖V‖ (le_max_left _ _)
  have hM : M ≤ M / x + 1 / 2 * Real.log N * (1 - 1 / (x : ℝ)) + LLS.P2sum x
      + 2 * M / √(x : ℝ) + G0 := by
    rcases le_total ‖V‖ ‖V'‖ with h | h
    · rw [show M = ‖V'‖ from max_eq_right h]; rw [show M = ‖V'‖ from max_eq_right h] at h2 hZx
      linarith
    · rw [show M = ‖V‖ from max_eq_left h]; rw [show M = ‖V‖ from max_eq_left h] at h1 hZx
      linarith
  have e : M * (1 - 1 / (x : ℝ) - 2 / √(x : ℝ)) = M - M / x - 2 * M / √(x : ℝ) := by ring
  rw [e]; linarith

/-- `|S(x, ψ)| ≤ (√x + 1) Z₂ + |V'| log x + ½ log x max(log f − 3, log x + 2) + 5/4`. -/
theorem norm_logSum_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) (hl4 : 4 ≤ Real.log x) :
    ‖LLS.logSum χ x‖ ≤ (√(x : ℝ) + 1) * LLS.Z2 χ
      + ‖((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ⁻¹ 1‖ * Real.log x
      + (1 / 2 * Real.log x * max (Real.log N - 3) (Real.log x + 2) + 5 / 4) := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  obtain ⟨hS1, he⟩ := LogAux.log_explicit_formula hprim hχ x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  obtain ⟨hsum_ε, -⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  have hsq : Summable fun ρ : {ρ : ℂ // Λf ρ = 0} =>
      (analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
    refine (hsum_ε 1 one_pos).congr fun ρ => ?_
    norm_num <;> rfl
  set Sz := ∑' ρ : {ρ : ℂ // Λf ρ = 0}, (analyticOrderNatAt Λf ρ : ℂ)
      * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2) with hSz
  have hterm : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, ‖(analyticOrderNatAt Λf ρ : ℂ)
      * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)‖
        ≤ (√(x : ℝ) + 1) * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
    intro ρ
    have hre := completedLFunction_zero_re hGRH hprim hχ ρ.2
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
  have hSzb : ‖Sz‖ ≤ (√(x : ℝ) + 1) * LLS.Z2 χ := by
    have hs : Summable fun ρ : {ρ : ℂ // Λf ρ = 0} => ‖(analyticOrderNatAt Λf ρ : ℂ)
        * (((x : ℂ) ^ (ρ : ℂ) - 1) / (ρ : ℂ) ^ 2)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsq.mul_left _)
    calc ‖Sz‖ ≤ _ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ : {ρ : ℂ // Λf ρ = 0}, (√(x : ℝ) + 1)
            * ((analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) :=
          hs.tsum_le_tsum hterm (hsq.mul_left _)
      _ = (√(x : ℝ) + 1) * LLS.Z2 χ := by rw [tsum_mul_left]; rfl
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hs1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) (by simp)
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ hs1
  rw [sub_self] at hFE
  have hD0 : -(LLS.D χ 0) = (Real.log N : ℂ) + LLS.D χ⁻¹ 1 := hFE
  have hG := norm_logGamma_le χ x hx (Real.log N) (Real.log_natCast_nonneg N) hl4
  have hsplit : LLS.logSum χ x = -Sz
      + (((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ⁻¹ 1) * (Real.log x : ℂ)
      + (((1 / 2 * Real.log N * Real.log x : ℝ) : ℂ)
        + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ))) := by
    rw [he]
    have : -(LLS.D χ 0) * (Real.log x : ℂ) = ((Real.log N : ℂ) + LLS.D χ⁻¹ 1) * (Real.log x : ℂ) := by
      rw [hD0]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    linear_combination this
  rw [hsplit]
  have hl0 : 0 ≤ Real.log x := by linarith
  calc _ ≤ ‖-Sz‖ + ‖(((1 / 2 * Real.log N : ℝ) : ℂ) + LLS.D χ⁻¹ 1) * (Real.log x : ℂ)‖
        + ‖((1 / 2 * Real.log N * Real.log x : ℝ) : ℂ)
          + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
        have : ((1 / 2 * Real.log N * Real.log x : ℝ) : ℂ)
            = ((1 / 2 * Real.log N * Real.log x : ℝ) : ℂ) := rfl
        linarith

end LLS.Thm14
