import Cramer.Identity
import Cramer.PrimePowers

/-!
# A prime in `[a, a + 2h)` under RH, given one numerical inequality

With `σ = 2b/h` (`b = a + 2h`) in `Cramer.psi1N_second_diff_ge`, the second difference of `Ψ₁`
gives `Σ_{a ≤ k < b} Λ(k) ≥ h − (4b/√a)(L(1/2 + 2b/h) + 1/40) − 3/h`. If this exceeds the
prime-power bound of `Cramer.sum_vonMangoldt_not_prime_le`, some `k ∈ [a, b)` is prime.
-/

namespace Cramer

open ArithmeticFunction Finset

/-- The numerical condition on `(a, h)` under which the analytic argument finds a prime. -/
def IntervalCondition (a h : ℕ) : Prop :=
  Real.log ((a : ℝ) + 2 * h) * ((√((a : ℝ) + 2 * h) - √(a : ℝ) + 1) + (((a : ℝ) + 2 * h) ^ ((1 : ℝ) / 3) + 1))
    < h - 4 * ((a : ℝ) + 2 * h) / √(a : ℝ) * (Lup (1 / 2 + 2 * ((a : ℝ) + 2 * h) / h) + 1 / 40) - 3 / h

/-- **Under RH**, if `1 ≤ h`, `2h ≤ a` and `IntervalCondition a h`, then `[a, a + 2h)` contains a
prime. -/
theorem exists_prime_Ico_of_RH (hRH : RiemannHypothesis) {a h : ℕ} (hh : 1 ≤ h) (h2 : 2 * h ≤ a)
    (hC : IntervalCondition a h) : ∃ p, p.Prime ∧ a ≤ p ∧ p < a + 2 * h := by
  have ha : 1 ≤ a := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have h2R : 2 * (h : ℝ) ≤ a := by exact_mod_cast h2
  set bR : ℝ := (a : ℝ) + 2 * h with hbR
  have hbR0 : 0 < bR := by positivity
  set σ : ℝ := 2 * bR / h with hσdef
  have hσ : 3 / 2 < σ := by
    rw [hσdef, lt_div_iff₀ hhR]; linarith
  have hsa : 0 < √(a : ℝ) := Real.sqrt_pos.mpr haR
  have hsab : √(a : ℝ) ≤ √bR := Real.sqrt_le_sqrt (by linarith)
  have hsb2 : √bR * √bR = bR := Real.mul_self_sqrt hbR0.le
  have hneg : (a : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(a : ℝ) := by
    rw [Real.rpow_neg haR.le, Real.sqrt_eq_rpow, one_div]; norm_num
  have h32 : bR ^ (3 / 2 : ℝ) = bR * √bR := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hbR0,
      Real.rpow_one]
  have hB : 4 * bR ^ (3 / 2 : ℝ) ≤ (h : ℝ) ^ 2 * (a : ℝ) ^ (-(1 / 2 : ℝ)) * σ ^ 2 := by
    rw [h32, hneg, hσdef]
    have e : (h : ℝ) ^ 2 * (1 / √(a : ℝ)) * (2 * bR / h) ^ 2 = 4 * bR * (bR / √(a : ℝ)) := by
      field_simp; norm_num
    rw [e]
    have : √bR ≤ bR / √(a : ℝ) := by
      rw [le_div_iff₀ hsa]
      nlinarith
    nlinarith
  have hlow := psi1N_second_diff_ge hRH ha hh hσ hB
  have hup := psi1N_second_diff_le a h
  have hcoef : 2 * ((h : ℝ) ^ 2 * (a : ℝ) ^ (-(1 / 2 : ℝ))) * σ = h * (4 * bR / √(a : ℝ)) := by
    rw [hneg, hσdef]; field_simp; norm_num
  rw [hcoef] at hlow
  -- divide by `h`
  set L := Lup (1 / 2 + σ) + 1 / 40
  have hS : (h : ℝ) - 4 * bR / √(a : ℝ) * L - 3 / h ≤ ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
    have : (h : ℝ) * ((h : ℝ) - 4 * bR / √(a : ℝ) * L - 3 / h)
        ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
      have e : (h : ℝ) * ((h : ℝ) - 4 * bR / √(a : ℝ) * L - 3 / h)
          = (h : ℝ) ^ 2 - h * (4 * bR / √(a : ℝ)) * L - 3 := by field_simp
      rw [e]; linarith
    exact le_of_mul_le_mul_left this hhR
  -- prime powers
  have hP := sum_vonMangoldt_not_prime_le a (a + 2 * h) ha (by omega) (by omega)
  push_cast at hP
  rw [← sum_filter_add_sum_filter_not _ (fun k => k.Prime)] at hS
  have hC' : Real.log bR * ((√bR - √(a : ℝ) + 1) + (bR ^ ((1 : ℝ) / 3) + 1))
      < (h : ℝ) - 4 * bR / √(a : ℝ) * L - 3 / h := hC
  have hpos : 0 < ∑ k ∈ (Ico a (a + 2 * h)).filter (fun k => k.Prime), (Λ k : ℝ) := by linarith
  obtain ⟨p, hp, hp0⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  simp only [mem_filter, mem_Ico] at hp
  exact ⟨p, hp.2, hp.1.1, hp.1.2⟩

end Cramer
