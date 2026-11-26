import Schoenfeld.Ranges
import Schoenfeld.PsiCert.Final

/-!
# Schoenfeld's bounds from RH and Rosser's zero count

With the three finite ranges (`Schoenfeld/Check/`) and PsiCert (`Schoenfeld/PsiCert/`) proved,
the only cited input left is `RosserZeroCount`.
-/

namespace Schoenfeld

/-- **Schoenfeld's ψ bound** from RH and Rosser's zero count. -/
theorem schoenfeldPsi_of_RH_of_rosser (hRH : RiemannHypothesis) (hR : RosserZeroCount) :
    SchoenfeldPsi :=
  schoenfeldPsi_of_RH_of_cited hRH hR psiCert

/-- **Schoenfeld's θ bound** from RH and Rosser's zero count. -/
theorem schoenfeldTheta_of_RH_of_rosser (hRH : RiemannHypothesis) (hR : RosserZeroCount) :
    SchoenfeldTheta :=
  schoenfeldTheta_of_RH_of_cited hRH hR psiCert

/-- **Schoenfeld's Corollary 1** from RH and Rosser's zero count. -/
theorem schoenfeldPi_of_RH_of_rosser (hRH : RiemannHypothesis) (hR : RosserZeroCount) :
    SchoenfeldPi :=
  schoenfeldPi_of_RH_of_cited hRH hR psiCert

/-- **Schoenfeld's Theorem 10 and Corollary 1** from RH and Rosser's zero count. -/
theorem schoenfeld_of_RH_of_rosser (hRH : RiemannHypothesis) (hR : RosserZeroCount) :
    SchoenfeldStatement :=
  schoenfeld_of_RH_of_cited hRH hR psiCert

end Schoenfeld
