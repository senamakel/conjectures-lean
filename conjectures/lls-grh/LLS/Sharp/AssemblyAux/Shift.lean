import LLS.Sharp.AssemblyAux.Conj

/-!
# LLS Lemma 2.3 in the paper's form, and `Re l1Sum + Re S'/log x = Re W`

With `Γ = Re(Γₛ(x) + (1 − 1/x) G(3))` and `y = 1/√x`, the exact identity
`Re S' = −U − (log N + V)/x − Re Zρ + Γ`, `|Re Zρ| ≤ Z y`, and `U = V = (Z − log N)/2` give
`Z (1 − y)² ≤ (1 − 1/x) log N − 2 Re S' + 2Γ ≤ Z (1 + y)²`.
-/

namespace LLS.Sharp.AssemblyAux

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic LLS.ShiftAux

variable {N : ℕ} [NeZero N]

/-- `Z = log N + 2 Re D(1, χ)`. -/
lemma Z2_eq_two (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LLS.Z2 χ = Real.log N + 2 * (LLS.D χ 1).re := by
  obtain ⟨-, hZ⟩ := LLS.Z2_eq hGRH hprim hχ
  rw [hZ, re_D_inv_one hχ]; ring

/-- LLS Lemma 2.3, both directions, with `U = V`. -/
theorem cesShift_two_sided (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) :
    LLS.Z2 χ * (1 - 1 / √(x : ℝ)) ^ 2
        ≤ (1 - 1 / (x : ℝ)) * Real.log N - 2 * (LLS.cesShift χ x).re
          + 2 * (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re ∧
      (1 - 1 / (x : ℝ)) * Real.log N - 2 * (LLS.cesShift χ x).re
          + 2 * (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re
        ≤ LLS.Z2 χ * (1 + 1 / √(x : ℝ)) ^ 2 := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  obtain ⟨Z, hZ, hZeq⟩ := zeroPart_eq hGRH hprim hχ x hx1
  have hid := shift_identity hGRH hprim hχ x hx1
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
  have hre0 : (LLS.D χ 0 / (x : ℂ)).re = -(Real.log N + (LLS.D χ⁻¹ 1).re) / x := by
    rw [Complex.div_natCast_re, hD0, neg_re, add_re, ofReal_re]
  have hre : (LLS.cesShift χ x).re = -(LLS.D χ 1).re + (LLS.D χ 0 / (x : ℂ)).re - Z.re
      + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re := by
    rw [hmain, add_re, sub_re, add_re, neg_re]
  rw [hre0, re_D_inv_one hχ] at hre
  have hZ2 := Z2_eq_two hGRH hprim hχ
  set Γ := (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re
  set U := (LLS.D χ 1).re
  set b := 1 / √(x : ℝ) with hb
  have hb2 : b ^ 2 = 1 / (x : ℝ) := by
    rw [hb, div_pow, Real.sq_sqrt hx0.le, one_pow]
  have hZb : Z2 χ / √(x : ℝ) = Z2 χ * b := by rw [hb]; ring
  have hZre : |Z.re| ≤ Z2 χ * b := (Complex.abs_re_le_norm Z).trans (hZb ▸ hZ)
  rw [abs_le] at hZre
  have hdiv : -(Real.log N + U) / (x : ℝ) = -(Real.log N + U) * b ^ 2 := by
    rw [hb2]; ring
  rw [hdiv] at hre
  have hkey : (1 - b ^ 2) * Real.log N - 2 * (LLS.cesShift χ x).re + 2 * Γ
      = Z2 χ * (1 + b ^ 2) + 2 * Z.re := by
    rw [hre, hZ2]; ring
  rw [← hb2]
  have e1 : Z2 χ * (1 - b) ^ 2 = Z2 χ * (1 + b ^ 2) - 2 * (Z2 χ * b) := by ring
  have e2 : Z2 χ * (1 + b) ^ 2 = Z2 χ * (1 + b ^ 2) + 2 * (Z2 χ * b) := by ring
  rw [e1, e2, hkey]
  constructor <;> linarith

/-- `l1Sum χ x + cesShift χ x / log x = Wsum χ x`. -/
lemma l1Sum_add_cesShift {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) (hx : 2 ≤ x) :
    LLS.l1Sum χ x + LLS.cesShift χ x / (Real.log x : ℂ) = LLS.Sharp.Wsum χ x := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  unfold LLS.l1Sum LLS.cesShift LLS.Sharp.Wsum
  rw [Finset.sum_range_succ, Finset.sum_range_succ (n := x), Finset.sum_div, add_right_comm,
    ← Finset.sum_add_distrib]
  have hlast1 : (Λ x : ℂ) * χ x / ((x : ℂ) * (Real.log x : ℂ))
      * ((Real.log ((x : ℝ) / x) / Real.log x : ℝ) : ℂ) = 0 := by
    rw [div_self hx0.ne', Real.log_one, zero_div]; simp
  have hlast2 : (Λ x : ℂ) * χ x
      * ((1 / ((x : ℝ) * Real.log x) - 1 / ((x : ℝ) * Real.log x) : ℝ) : ℂ) = 0 := by
    rw [sub_self]; simp
  rw [hlast1, hlast2, add_zero, add_zero]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : n < x := Finset.mem_range.1 hn
  by_cases hΛ : Λ n = 0
  · simp [hΛ]
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hΛ
    · exact h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hA : (1 / ((n : ℝ) * Real.log n)) * (Real.log ((x : ℝ) / n) / Real.log x)
      + 1 / (n : ℝ) * (1 - (n : ℝ) / x) / Real.log x
      = 1 / ((n : ℝ) * Real.log n) - 1 / ((x : ℝ) * Real.log x) := by
    rw [Real.log_div hx0.ne' hn0.ne']
    field_simp
    ring
  rw [← hA]
  have hn0c : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hlnc : (Real.log n : ℂ) ≠ 0 := by exact_mod_cast hln.ne'
  have hlxc : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast hlx.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  push_cast
  field_simp

end LLS.Sharp.AssemblyAux
