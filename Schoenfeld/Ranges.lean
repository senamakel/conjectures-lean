import Schoenfeld.PiSharp
import Schoenfeld.Check.Pi

/-!
# Schoenfeld's bounds with the three finite ranges discharged

`PsiSmallRange`, `ThetaSmallRange` and `PiSmallRange` are proved in `Schoenfeld/Check/` by
proved-sound checkers (3 `native_decide`), so the remaining cited inputs of
`schoenfeld_of_RH` are Rosser's zero count and PsiCert.
-/

namespace Schoenfeld

/-- **Schoenfeld's ψ bound** from RH, Rosser's zero count and PsiCert. -/
theorem schoenfeldPsi_of_RH_of_cited (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) : SchoenfeldPsi :=
  schoenfeldPsi_of_RH hRH hR hC Check.psiSmallRange

/-- **Schoenfeld's θ bound** from RH, Rosser's zero count and PsiCert. -/
theorem schoenfeldTheta_of_RH_of_cited (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) : SchoenfeldTheta :=
  schoenfeldTheta_of_RH hRH hR hC Check.thetaSmallRange

/-- **Schoenfeld's Corollary 1** from RH, Rosser's zero count and PsiCert. -/
theorem schoenfeldPi_of_RH_of_cited (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) : SchoenfeldPi :=
  schoenfeldPi_of_RH hRH hR hC Check.thetaSmallRange Check.piSmallRange

/-- **Schoenfeld's Theorem 10 and Corollary 1** from RH, Rosser's zero count and PsiCert. -/
theorem schoenfeld_of_RH_of_cited (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) : SchoenfeldStatement :=
  schoenfeld_of_RH hRH hR hC Check.psiSmallRange Check.thetaSmallRange Check.piSmallRange

end Schoenfeld
