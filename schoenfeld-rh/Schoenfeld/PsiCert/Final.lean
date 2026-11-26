import Schoenfeld.PsiCert.Chain
import Schoenfeld.PsiCert.Small
import Schoenfeld.Inputs

/-!
# PsiCert

`|ψ(x) − x| ≤ (4/5)√x` for `1500 ≤ x ≤ 10¹⁰`: `[1500, 10⁶]` by `psiCert_small` (the cell
checker of `Schoenfeld/Check/Step.lean`), `(10⁶, 10¹⁰]` by the segmented-sieve run
(`inv_final`).
-/

namespace Schoenfeld

open Chebyshev

/-- **PsiCert**: `|ψ(x) − x| ≤ (4/5)√x` on `[1500, 10¹⁰]`. -/
theorem psiCert : PsiCert := by
  intro x h1 h2
  rcases le_or_gt x 1000000 with h | h
  · exact (Check.psiCert_small h1 h).le
  · have hf := PsiCert.final_a
    have hf' : (10 : ℝ) ^ 10 ≤ (PsiCert.st_final.a : ℝ) := by exact_mod_cast hf
    exact PsiCert.inv_final.2.2.2.2.2 x (by norm_num [SchoenfeldCompute.A0]; linarith)
      (le_trans h2 hf')

end Schoenfeld
