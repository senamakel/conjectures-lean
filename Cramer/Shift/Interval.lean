import Cramer.Shift.PerZero
import Cramer.Shift.MajSum
import Cramer.Interval

/-!
# A prime in `[a, a + 2h)` under RH with a shifted-Lorentzian majorant

With `m = a + h`, every zero satisfies `‖D_ρ‖ ≤ h² m^{−1/2} M(γh/(2m))`
(`Cramer.Shift.norm_D_le_majF`), and the zero sum of `M` is at most `majZ`
(`Cramer.Shift.majF_zeroSum`). The second difference of `Ψ₁` then gives
`Σ_{a ≤ k < a+2h} Λ(k) ≥ h − h m^{−1/2} majZ − 3/h`.
-/

namespace Cramer.Shift

open ArithmeticFunction Finset Erdos985.Analytic

/-- The numerical condition on `(a, h)`. -/
def IntervalConditionShift (maj : List (ℕ × ℕ × ℕ)) (a h : ℕ) : Prop :=
  800 * h ≤ a + h ∧
  Real.log ((a : ℝ) + 2 * h) * ((√((a : ℝ) + 2 * h) - √(a : ℝ) + 1) + (((a : ℝ) + 2 * h) ^ ((1 : ℝ) / 3) + 1))
    < h - h * ((a : ℝ) + h) ^ (-(1 / 2 : ℝ)) * majZ maj ((a : ℝ) + h) h - 3 / h

/-- **Under RH**, if the majorant is good, `1 ≤ h` and `IntervalConditionShift maj a h`, then
`[a, a + 2h)` contains a prime. -/
theorem exists_prime_Ico_shift (hRH : RiemannHypothesis) {maj : List (ℕ × ℕ × ℕ)}
    (hgood : ∀ y : ℝ, 0 ≤ y → CellGood maj y) (hσ : ∀ c ∈ maj, 1000 ≤ c.2.1) {a h : ℕ}
    (hh : 1 ≤ h) (hC : IntervalConditionShift maj a h) : ∃ p, p.Prime ∧ a ≤ p ∧ p < a + 2 * h := by
  obtain ⟨h800, hC⟩ := hC
  have ha : 1 ≤ a := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  set m : ℝ := (a : ℝ) + h with hmdef
  have hm : 0 < m := by positivity
  have hε : (h : ℝ) / m ≤ 1 / 800 := by
    rw [div_le_iff₀ hm]
    have : (800 : ℝ) * h ≤ a + h := by exact_mod_cast h800
    linarith
  set A : ℝ := (h : ℝ) ^ 2 * m ^ (-(1 / 2 : ℝ))
  have hA0 : 0 ≤ A := by positivity
  have hcrit : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => xiZeta_zero_re_RH hRH ρ.2
  have hpt : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖
        ≤ A * majF maj ((ρ : ℂ).im * h / (2 * m)) := by
    intro ρ
    have := norm_D_le_majF hgood (hcrit ρ) hm hhR hε
    rw [show m + h = (a : ℝ) + 2 * h by rw [hmdef]; ring, show m - h = (a : ℝ) by rw [hmdef]; ring]
      at this
    exact this
  obtain ⟨hS, hle⟩ := majF_zeroSum hRH maj hσ hm hhR hε
  have hcmp : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖
        ≤ A * ((analyticOrderNatAt xiZeta ρ : ℝ) * majF maj ((ρ : ℂ).im * h / (2 * m))) := by
    intro ρ
    have := mul_le_mul_of_nonneg_left (hpt ρ) (Nat.cast_nonneg (analyticOrderNatAt xiZeta ρ))
    linarith
  have hnn : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, 0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖ := fun ρ => by positivity
  have hS' := hS.mul_left A
  have hsumD := Summable.of_nonneg_of_le hnn hcmp hS'
  have hD : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖ ≤ A * majZ maj m h := by
    calc _ ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, A * ((analyticOrderNatAt xiZeta ρ : ℝ) *
          majF maj ((ρ : ℂ).im * h / (2 * m))) := hsumD.tsum_le_tsum hcmp hS'
      _ = A * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
          majF maj ((ρ : ℂ).im * h / (2 * m)) := tsum_mul_left
      _ ≤ A * majZ maj m h := mul_le_mul_of_nonneg_left hle hA0
  have hlow := psi1N_second_diff_ge_of_zeroSum hRH ha hh hsumD hD
  have hup := psi1N_second_diff_le a h
  have hS2 : (h : ℝ) - h * m ^ (-(1 / 2 : ℝ)) * majZ maj m h - 3 / h
      ≤ ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
    have : (h : ℝ) * ((h : ℝ) - h * m ^ (-(1 / 2 : ℝ)) * majZ maj m h - 3 / h)
        ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
      have e : (h : ℝ) * ((h : ℝ) - h * m ^ (-(1 / 2 : ℝ)) * majZ maj m h - 3 / h)
          = (h : ℝ) ^ 2 - A * majZ maj m h - 3 := by simp only [A]; field_simp
      rw [e]; linarith
    exact le_of_mul_le_mul_left this hhR
  have hP := sum_vonMangoldt_not_prime_le a (a + 2 * h) ha (by omega) (by omega)
  push_cast at hP
  rw [← sum_filter_add_sum_filter_not _ (fun k => k.Prime)] at hS2
  have hpos : 0 < ∑ k ∈ (Ico a (a + 2 * h)).filter (fun k => k.Prime), (Λ k : ℝ) := by linarith
  obtain ⟨p, hp, _⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  simp only [mem_filter, mem_Ico] at hp
  exact ⟨p, hp.2, hp.1.1, hp.1.2⟩

end Cramer.Shift
