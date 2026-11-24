import Schoenfeld.Check.Step
import Schoenfeld.SmallRange

/-!
# `PsiSmallRange` and `ThetaSmallRange`

`checkA isPP (366/5) 1500` and `checkA isPrime 599 30000` are run by `native_decide` (one
each; together under a second of compiled code) and `checkA_sound` turns them into the two
finite ranges of Schoenfeld's proof.
-/

namespace Schoenfeld.Check

open Real Chebyshev Finset ArithmeticFunction

lemma psi_succ (n : ℕ) :
    ψ ((n + 1 : ℕ) : ℝ) = ψ (n : ℝ) +
      if isPP (n + 1) then Real.log ((n + 1).minFac : ℝ) else 0 := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), vonMangoldt_apply]
  congr 1
  by_cases h : IsPrimePow (n + 1)
  · rw [if_pos h, if_pos ((isPP_iff _).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((isPP_iff _).mp h'))]

lemma theta_succ (n : ℕ) :
    θ ((n + 1 : ℕ) : ℝ) = θ (n : ℝ) +
      if isPrime (n + 1) then Real.log ((n + 1).minFac : ℝ) else 0 := by
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log, Nat.primesLE_succ]
  by_cases h : (n + 1).Prime
  · rw [if_pos h, if_pos ((isPrime_iff _).mpr h), Finset.sum_insert (Nat.notMem_primesLE n),
      h.minFac_eq, add_comm]
  · rw [if_neg h, if_neg (fun h' => h ((isPrime_iff _).mp h')), add_zero]

/-- The ψ check on `[73.2, 1500]`. -/
theorem checkA_psi : checkA isPP (366 / 5) 1500 = true := by native_decide

/-- The θ check on `[599, 3·10⁴]`. -/
theorem checkA_theta : checkA isPrime 599 30000 = true := by native_decide

/-- **`PsiSmallRange`**: `|ψ(x) − x| < √x log² x/(8π)` on `[73.2, 1500]`. -/
theorem psiSmallRange : PsiSmallRange := by
  intro x hx1 hx2
  have h := checkA_sound isPP (fun n => ψ (n : ℝ)) psi_succ (by simp [Chebyshev.psi])
    checkA_psi x (by push_cast; linarith) (by push_cast; exact hx2)
  rw [psi_eq_psi_coe_floor x]
  exact h

/-- **`ThetaSmallRange`**: `|θ(x) − x| < √x log² x/(8π)` on `[599, 3·10⁴]`. -/
theorem thetaSmallRange : ThetaSmallRange := by
  intro x hx1 hx2
  have h := checkA_sound isPrime (fun n => θ (n : ℝ)) theta_succ (by simp [Chebyshev.theta])
    checkA_theta x (by push_cast; linarith) (by push_cast; exact hx2)
  rw [theta_eq_theta_coe_floor x]
  exact h

end Schoenfeld.Check
