import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Schoenfeld

/-!
# Schoenfeld's bounds, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem psi_bound : Schoenfeld.PsiBound (1 / 8) 73.2 :=
  Schoenfeld.psiBound_of_RH riemannHypothesis

theorem theta_bound : Schoenfeld.ThetaBound (1 / 4) 599 :=
  Schoenfeld.thetaBound_of_RH riemannHypothesis

theorem pi_bound : Schoenfeld.PiBound (9 / 20) 2657 :=
  Schoenfeld.piBound_of_RH riemannHypothesis

/-! ### Schoenfeld's constant `1/(8π)`

RH is supplied by riemann-hypothesis; the cited inputs stay hypotheses: Rosser's zero count
(`RosserZeroCount`), PsiCert, and the finite ranges. -/

theorem schoenfeld_psi (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert)
    (hS : Schoenfeld.PsiSmallRange) : Schoenfeld.SchoenfeldPsi :=
  Schoenfeld.schoenfeldPsi_of_RH riemannHypothesis hR hC hS

theorem schoenfeld_theta (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert)
    (hS : Schoenfeld.ThetaSmallRange) : Schoenfeld.SchoenfeldTheta :=
  Schoenfeld.schoenfeldTheta_of_RH riemannHypothesis hR hC hS

theorem schoenfeld_pi (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert)
    (hSθ : Schoenfeld.ThetaSmallRange) (hSπ : Schoenfeld.PiSmallRange) : Schoenfeld.SchoenfeldPi :=
  Schoenfeld.schoenfeldPi_of_RH riemannHypothesis hR hC hSθ hSπ

theorem schoenfeld_statement (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert)
    (hSψ : Schoenfeld.PsiSmallRange) (hSθ : Schoenfeld.ThetaSmallRange)
    (hSπ : Schoenfeld.PiSmallRange) : Schoenfeld.SchoenfeldStatement :=
  Schoenfeld.schoenfeld_of_RH riemannHypothesis hR hC hSψ hSθ hSπ

/-! ### The finite ranges discharged

`PsiSmallRange`, `ThetaSmallRange` and `PiSmallRange` are proved in the main library
(`Schoenfeld/Check/`); Rosser's zero count and PsiCert remain hypotheses. -/

theorem schoenfeld_psi_of_cited (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert) :
    Schoenfeld.SchoenfeldPsi :=
  Schoenfeld.schoenfeldPsi_of_RH_of_cited riemannHypothesis hR hC

theorem schoenfeld_theta_of_cited (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert) :
    Schoenfeld.SchoenfeldTheta :=
  Schoenfeld.schoenfeldTheta_of_RH_of_cited riemannHypothesis hR hC

theorem schoenfeld_pi_of_cited (hR : Schoenfeld.RosserZeroCount) (hC : Schoenfeld.PsiCert) :
    Schoenfeld.SchoenfeldPi :=
  Schoenfeld.schoenfeldPi_of_RH_of_cited riemannHypothesis hR hC

theorem schoenfeld_statement_of_cited (hR : Schoenfeld.RosserZeroCount)
    (hC : Schoenfeld.PsiCert) : Schoenfeld.SchoenfeldStatement :=
  Schoenfeld.schoenfeld_of_RH_of_cited riemannHypothesis hR hC

#print axioms psi_bound
#print axioms theta_bound
#print axioms pi_bound
#print axioms schoenfeld_psi
#print axioms schoenfeld_theta
#print axioms schoenfeld_pi
#print axioms schoenfeld_statement
#print axioms schoenfeld_psi_of_cited
#print axioms schoenfeld_theta_of_cited
#print axioms schoenfeld_pi_of_cited
#print axioms schoenfeld_statement_of_cited
