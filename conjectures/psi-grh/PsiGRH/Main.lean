import PsiGRH.PrimeCount

/-!
# Headline theorems (tier C + H)

Each theorem takes GRH (`Erdos985.DirichletLNonvanishingRightOfHalf`) and the two cited,
unconditional analytic inputs of `PsiGRH/Inputs.lean` as explicit hypotheses.
`Unconditional/PsiGRHUnconditional.lean` discharges all three from riemann-hypothesis.
-/

namespace PsiGRH

/-- Montgomery–Vaughan Theorem 13.7, (13.19), uniform in `q`:
`|ψ(x, χ) − E₀(χ) x| ≤ C √x (log x)(log qx)`. -/
theorem psiChar_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PsiCharStatement :=
  psiCharBound_of_GRH hGRH hEF hZ

/-- `|ψ(x, χ) − E₀(χ) x| ≤ C √x log²(qx)`, uniform in `q`. -/
theorem psiCharLogSq_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PsiCharLogSqStatement := by
  obtain ⟨C, hC, h⟩ := psiCharBound_of_GRH hGRH hEF hZ
  exact ⟨C, hC, psiCharLogSqBound_of_psiCharBound hC h⟩

/-- `|ψ(x; q, a) − x/φ(q)| ≤ C √x (log x)(log qx)` for `(a, q) = 1`, uniform in `q`. -/
theorem psiAP_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PsiAPStatement := by
  obtain ⟨C, hC, h⟩ := psiCharBound_of_GRH hGRH hEF hZ
  exact ⟨C, hC, psiAPBound_of_psiCharBound h⟩

/-- `|ϑ(x; q, a) − x/φ(q)| ≤ C √x (log x)(log qx)` for `(a, q) = 1`, uniform in `q`. -/
theorem thetaAP_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : ThetaAPStatement := by
  obtain ⟨C, hC, h⟩ := psiCharBound_of_GRH hGRH hEF hZ
  exact ⟨C + 3, by linarith, thetaAPBound_of_psiAPBound hC.le (psiAPBound_of_psiCharBound h)⟩

/-- `|π(x; q, a) − li(x)/φ(q)| ≤ C √x log(qx)` for `(a, q) = 1`, uniform in `q`. -/
theorem piAP_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PiAPStatement := by
  obtain ⟨C, hC, h⟩ := psiCharBound_of_GRH hGRH hEF hZ
  have hθ := thetaAPBound_of_psiAPBound hC.le (psiAPBound_of_psiCharBound h)
  exact ⟨4 * (C + 3) + 5, by linarith, piAPBound_of_thetaAPBound (by linarith) hθ⟩

end PsiGRH
