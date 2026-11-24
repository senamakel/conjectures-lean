import Schoenfeld.Check.PsiTheta

/-!
# PsiCert on `[1500, 10⁶]`

`checkA F0lo isPP 1500 1000000` (one `native_decide`) and `checkA_sound`, with the right-hand
side `F0(x) = (4/5)√x`: `|ψ(x) − x| < (4/5)√x` for `1500 ≤ x ≤ 10⁶`.
-/

namespace Schoenfeld.Check

open Real Chebyshev

/-- `(4/5)√x`. -/
noncomputable def F0 (x : ℝ) : ℝ := 4 / 5 * √x

/-- Lower bound for `F0 a`. -/
def F0lo (a : ℚ) : ℚ := rdDown (4 / 5 * sqrtLo a)

lemma F0lo_le {a : ℚ} (ha : 1 ≤ a) : (F0lo a : ℝ) ≤ F0 a := by
  unfold F0lo F0
  apply rdDown_le_real
  push_cast
  have := sqrtLo_le (by linarith : (0 : ℚ) ≤ a)
  linarith

lemma F0_mono {a x : ℝ} (_ : 1 ≤ a) (hx : a ≤ x) : F0 a ≤ F0 x := by
  unfold F0
  have := Real.sqrt_le_sqrt hx
  linarith

/-- The ψ check on `[1500, 10⁶]` against `(4/5)√x`. -/
theorem checkA_psiCert : checkA F0lo isPP 1500 1000000 = true := by native_decide

/-- `|ψ(x) − x| < (4/5)√x` on `[1500, 10⁶]`. -/
theorem psiCert_small {x : ℝ} (h1 : 1500 ≤ x) (h2 : x ≤ 1000000) :
    |ψ x - x| < 4 / 5 * √x := by
  have h := checkA_sound F0lo F0 (fun a ha => F0lo_le ha) (fun a x ha hx => F0_mono ha hx) isPP
    (fun n => ψ (n : ℝ)) psi_succ (by simp [Chebyshev.psi]) checkA_psiCert x
    (by push_cast; linarith) (by push_cast; exact h2)
  rw [psi_eq_psi_coe_floor x]
  exact h

end Schoenfeld.Check
