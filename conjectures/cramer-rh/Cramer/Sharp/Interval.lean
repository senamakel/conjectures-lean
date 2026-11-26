import Cramer.Interval
import Cramer.Sharp.Majorant

/-!
# A prime in `[a, a + 2h)` under RH with the Lorentzian majorant

With `σ = 7a/(3h)` and the majorant of `Cramer.Sharp.Majorant`, the zero sum is at most
`(9/7)(h² a^{−1/2}) σ (L(1/2+σ) + 1/40) = 3h√a (L(1/2+σ) + 1/40)`, so the second difference of
`Ψ₁` gives `Σ_{a ≤ k < a+2h} Λ(k) ≥ h − 3√a (L(1/2 + 7a/(3h)) + 1/40) − 3/h`. Compared with
`Cramer.Interval` the zero term is `3h√a·L` instead of `h·(4b/√a)·L` (`2Aσ` with `σ = 2b/h`),
which is what moves the constant from `2` to `3/2`.
-/

namespace Cramer

open ArithmeticFunction Finset Erdos985.Analytic

/-- The numerical condition on `(a, h)` for the sharper argument. -/
def IntervalCondition32 (a h : ℕ) : Prop :=
  400 * h ≤ a ∧
  Real.log ((a : ℝ) + 2 * h) * ((√((a : ℝ) + 2 * h) - √(a : ℝ) + 1) + (((a : ℝ) + 2 * h) ^ ((1 : ℝ) / 3) + 1))
    < h - 3 * √(a : ℝ) * (Lup (1 / 2 + 7 * (a : ℝ) / (3 * h)) + 1 / 40) - 3 / h

/-- **Under RH**, if `1 ≤ h` and `IntervalCondition32 a h`, then `[a, a + 2h)` contains a prime. -/
theorem exists_prime_Ico_of_RH_32 (hRH : RiemannHypothesis) {a h : ℕ} (hh : 1 ≤ h)
    (hC : IntervalCondition32 a h) : ∃ p, p.Prime ∧ a ≤ p ∧ p < a + 2 * h := by
  obtain ⟨h400, hC⟩ := hC
  have ha : 1 ≤ a := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have h400R : 400 * (h : ℝ) ≤ a := by exact_mod_cast h400
  set σ : ℝ := 7 * (a : ℝ) / (3 * h) with hσdef
  have hσ : 3 / 2 < σ := by
    rw [hσdef, lt_div_iff₀ (by positivity)]; linarith
  set A : ℝ := (h : ℝ) ^ 2 * (a : ℝ) ^ (-(1 / 2 : ℝ))
  have hcrit : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => xiZeta_zero_re_RH hRH ρ.2
  obtain ⟨hsumD, hD⟩ := lorentz_zeroSum_le hRH (σ := σ) (K := (9 / 7) * A) hσ (by positivity)
    (fun ρ => ‖gρ ρ ((a : ℝ) + 2 * h) - 2 * gρ ρ ((a : ℝ) + h) + gρ ρ a‖) (fun _ => norm_nonneg _)
    (fun ρ => by
      have := norm_second_diff_gρ_le_lorentz (hcrit ρ) haR hhR h400R
      rw [hσdef]; linarith)
  have hlow := psi1N_second_diff_ge_of_zeroSum hRH ha hh hsumD hD
  have hup := psi1N_second_diff_le a h
  have hsa : 0 < √(a : ℝ) := Real.sqrt_pos.mpr haR
  have hneg : (a : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(a : ℝ) := by
    rw [Real.rpow_neg haR.le, Real.sqrt_eq_rpow, one_div]; norm_num
  have hcoef : 9 / 7 * A * σ = h * (3 * √(a : ℝ)) := by
    simp only [A, hσdef, hneg]
    have hsq : √(a : ℝ) * √(a : ℝ) = a := Real.mul_self_sqrt haR.le
    field_simp
    nlinarith [hsq]
  rw [hcoef] at hlow
  set L := Lup (1 / 2 + σ) + 1 / 40
  have hS : (h : ℝ) - 3 * √(a : ℝ) * L - 3 / h ≤ ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
    have : (h : ℝ) * ((h : ℝ) - 3 * √(a : ℝ) * L - 3 / h)
        ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
      have e : (h : ℝ) * ((h : ℝ) - 3 * √(a : ℝ) * L - 3 / h)
          = (h : ℝ) ^ 2 - h * (3 * √(a : ℝ)) * L - 3 := by field_simp
      rw [e]; linarith
    exact le_of_mul_le_mul_left this hhR
  have hP := sum_vonMangoldt_not_prime_le a (a + 2 * h) ha (by omega) (by omega)
  push_cast at hP
  rw [← sum_filter_add_sum_filter_not _ (fun k => k.Prime)] at hS
  have hpos : 0 < ∑ k ∈ (Ico a (a + 2 * h)).filter (fun k => k.Prime), (Λ k : ℝ) := by linarith
  obtain ⟨p, hp, hp0⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  simp only [mem_filter, mem_Ico] at hp
  exact ⟨p, hp.2, hp.1.1, hp.1.2⟩

end Cramer
