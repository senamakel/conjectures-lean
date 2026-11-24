import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Speiser

/-!
# Speiser's theorem above height 7, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem speiser_above : Speiser.SpeiserAbove 7 :=
  Speiser.speiserAbove_of_RH riemannHypothesis

theorem speiser_of_below (hB : Speiser.SpeiserBelow 7) : Speiser.SpeiserStatement :=
  Speiser.speiser_of_RH_of_below riemannHypothesis hB

#print axioms speiser_above
#print axioms speiser_of_below
