import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
import PsiGRH

/-!
# The psi-grh bounds with GRH and the two analytic inputs supplied by riemann-hypothesis

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

* GRH: `LFunction_ne_zero_of_half_lt_re`.
* `PsiGRH.TruncatedExplicitFormula`: `GlobalTheory.ExplicitFormula.truncated_explicit_formula`.
  Its `psi0 χ u` is `ψ(u, χ) − E₀(χ) u`; `psi0_eq` bridges the two spellings.
* `PsiGRH.ZeroWindowCount`: `GlobalTheory.ZeroWindow.count_zeros_window`, a definitional match.

Neither analytic input uses RH or GRH; they are classical unconditional theorems, imported
rather than re-proved.
-/

open Formalism.MainNotions.GlobalTheoryTheory in
theorem psi0_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) :
    psi0 χ u = PsiGRH.psiChar χ u - PsiGRH.mainTerm χ u := by
  unfold psi0 PsiGRH.psiChar PsiGRH.mainTerm
  rfl

theorem truncatedExplicitFormula : PsiGRH.TruncatedExplicitFormula := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  refine ⟨C, hC, fun N _ χ hχ u T hT hTu => ?_⟩
  obtain ⟨hfin, hb⟩ := h N χ hχ u T hT hTu
  rw [psi0_eq] at hb
  exact ⟨hfin, hb⟩

theorem zeroWindowCount : PsiGRH.ZeroWindowCount :=
  GlobalTheory.ZeroWindow.count_zeros_window

theorem psiChar_unconditional : PsiGRH.PsiCharStatement :=
  PsiGRH.psiChar_of_GRH LFunction_ne_zero_of_half_lt_re truncatedExplicitFormula zeroWindowCount

theorem psiCharLogSq_unconditional : PsiGRH.PsiCharLogSqStatement :=
  PsiGRH.psiCharLogSq_of_GRH LFunction_ne_zero_of_half_lt_re truncatedExplicitFormula
    zeroWindowCount

theorem psiAP_unconditional : PsiGRH.PsiAPStatement :=
  PsiGRH.psiAP_of_GRH LFunction_ne_zero_of_half_lt_re truncatedExplicitFormula zeroWindowCount

theorem thetaAP_unconditional : PsiGRH.ThetaAPStatement :=
  PsiGRH.thetaAP_of_GRH LFunction_ne_zero_of_half_lt_re truncatedExplicitFormula zeroWindowCount

theorem piAP_unconditional : PsiGRH.PiAPStatement :=
  PsiGRH.piAP_of_GRH LFunction_ne_zero_of_half_lt_re truncatedExplicitFormula zeroWindowCount

#print axioms truncatedExplicitFormula
#print axioms zeroWindowCount
#print axioms psiChar_unconditional
#print axioms psiCharLogSq_unconditional
#print axioms psiAP_unconditional
#print axioms thetaAP_unconditional
#print axioms piAP_unconditional
