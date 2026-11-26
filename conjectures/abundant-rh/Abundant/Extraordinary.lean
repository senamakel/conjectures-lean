import Abundant.Extremely
import Abundant.Check

/-!
# 4 is the only extraordinary number

Caveney–Nicolas–Sondow, proof of Theorem 5 (the RH direction). Let `N` be extraordinary.
* Condition (ii) and Gronwall's lower bound along multiples (`exists_mul_robinRatio_gt`, from
  Nicolas' inequality) give `G(N) ≥ e^γ` (`exp_gamma_le_of_forall_mul_le`; CNS use their
  Lemma 1).
* Robin's inequality then gives `N ≤ 5040` (`le_5040_of_forall_mul_le`).
* For composite `4 < N ≤ 5040` the finite check gives `G(N) < e^γ` or `G(N) < G(N/p)`, against
  condition (ii) or (i) (`Abundant.Check.finite_check`; CNS Lemma 2).

Conversely `4` is extraordinary: `G(2) < 0 < G(4)`, and `G(4a) < G(4)` for `a ≥ 2`, by the
finite check when `4a ≤ 5040` and by Robin's inequality (`G(4a) < e^γ < G(4)`) otherwise. CNS
use Robin's unconditional bound `G(n) < e^γ + 0.6483/(log log n)²` here instead.
-/

namespace Abundant

open Real ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- If `G(N) ≥ G(aN)` for every `a ≥ 1`, then `G(N) ≥ e^γ` (from Nicolas' inequality). -/
lemma exp_gamma_le_of_forall_mul_le (hNic : Nicolas.NicolasStatement) {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ a : ℕ, 1 ≤ a → robinRatio (a * N) ≤ robinRatio N) :
    Real.exp Real.eulerMascheroniConstant ≤ robinRatio N := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, _, hgt⟩ := exists_mul_robinRatio_gt hNic hN hlt 0
  linarith [h a ha]

/-- No `N > 5040` has `G(N) ≥ G(aN)` for every `a ≥ 1` (the GA2-type half of CNS's argument). -/
theorem le_5040_of_forall_mul_le (hR : Robin.RobinStatement) (hNic : Nicolas.NicolasStatement)
    {N : ℕ} (hN : 1 ≤ N) (h : ∀ a : ℕ, 1 ≤ a → robinRatio (a * N) ≤ robinRatio N) :
    N ≤ 5040 := by
  by_contra hgt
  push Not at hgt
  have h1 := exp_gamma_le_of_forall_mul_le hNic hN h
  have h2 := robinRatio_lt_of_robin hR hgt
  linarith

lemma robinRatio_two_neg : robinRatio 2 < 0 := by
  have hl : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log 2) < 0 := Real.log_neg hl0 hl
  rw [robinRatio]
  push_cast
  apply div_neg_of_pos_of_neg (by positivity)
  nlinarith

lemma exp_gamma_lt_robinRatio_four : Real.exp Real.eulerMascheroniConstant < robinRatio 4 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hEU : Real.exp Real.eulerMascheroniConstant < 2 := by
    have h2 : (2 : ℝ) / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    calc Real.exp Real.eulerMascheroniConstant < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log 4) ≤ Real.log 4 - 1 := Real.log_le_sub_one_of_pos hlog4
  have hll0 : 0 < Real.log (Real.log 4) := by
    simpa using Abundant.Check.loglog_pos (show 3 ≤ 4 by norm_num)
  rw [robinRatio, Abundant.Check.sigma_four]
  push_cast
  rw [lt_div_iff₀ (mul_pos (by norm_num) hll0)]
  have hb : Real.log (Real.log 4) < 1 / 2 := by linarith
  have := mul_lt_mul hEU hb.le hll0 (by norm_num)
  linarith

/-- `4` is extraordinary (given Robin's inequality for the multiples `4a > 5040`). -/
theorem isExtraordinary_four (hR : Robin.RobinStatement) : IsExtraordinary 4 := by
  refine ⟨⟨by norm_num, by decide⟩, ?_, ?_⟩
  · intro p hp hdvd
    have hp2 : p = 2 := by
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hdvd))
      exact this
    subst hp2
    have h4 := exp_gamma_lt_robinRatio_four
    have := robinRatio_two_neg
    have := Real.exp_pos Real.eulerMascheroniConstant
    show robinRatio 2 ≤ robinRatio 4
    linarith
  · intro a ha
    rcases Nat.lt_or_ge (a * 4) 5041 with h | h
    · rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · have : a = 1 := by omega
        subst this; simp
      · exact (Abundant.Check.four_check (by omega) (by omega) (dvd_mul_left 4 a)).le
    · have h1 := robinRatio_lt_of_robin hR (show 5040 < a * 4 by omega)
      have h2 := exp_gamma_lt_robinRatio_four
      linarith

/-- **Caveney–Nicolas–Sondow** (2011, Theorem 5): Robin's inequality and Nicolas' inequality
imply that `4` is the only extraordinary number. -/
theorem fourOnlyExtraordinary_of_robin_of_nicolas (hR : Robin.RobinStatement)
    (hNic : Nicolas.NicolasStatement) : FourOnlyExtraordinary := by
  intro N
  refine ⟨fun hN ↦ ?_, fun h ↦ h ▸ isExtraordinary_four hR⟩
  obtain ⟨⟨h1, hnp⟩, hi, hii⟩ := hN
  have hge := exp_gamma_le_of_forall_mul_le hNic (by omega) hii
  have hle := le_5040_of_forall_mul_le hR hNic (by omega) hii
  by_contra hne
  have h4 : 4 < N := by
    have : N ≠ 2 := fun h ↦ hnp (h ▸ Nat.prime_two)
    have : N ≠ 3 := fun h ↦ hnp (h ▸ Nat.prime_three)
    omega
  rcases Abundant.Check.finite_check h4 hle hnp with hA | ⟨p, hp, hdvd, hB⟩
  · linarith
  · linarith [hi p hp hdvd]

end Abundant
