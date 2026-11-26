import Schoenfeld.WithRosser
import RSBounds.Rosser1941

/-!
# Rosser's zero count, proved; Schoenfeld's bounds from RH alone

`RosserZeroCount` (Rosser 1941, Theorem 19) is proved with no hypothesis by
`TernaryGoldbach.RSBounds.Rosser1941.zero_count_bounds`, vendored with its whole import closure
under `Vendor/Rosser/` (216 files from Garald1/RSBounds, calr3/ternary-goldbach and
teal-sea/zeta-lab; see `Vendor/Rosser/README.md`). That proof uses Backlund's argument for
`T ≥ 100` and a certificate for the 29 zeros of height at most 100; it involves no RH.
`Schoenfeld.positiveZeroCount` is a verbatim copy of the vendored `positiveZeroCount`, so the two
statements are the same term.

With it, `schoenfeld_of_RH` proves Schoenfeld's Theorem 10 and Corollary 1 (exact constant
`1/(8π)`) from RH alone.
-/

namespace Schoenfeld

/-- **Rosser's zero count** (Rosser 1941, Theorem 19), proved with no hypothesis. -/
theorem rosserZeroCount : RosserZeroCount :=
  fun T hT => TernaryGoldbach.RSBounds.Rosser1941.zero_count_bounds T hT

/-- **Schoenfeld's ψ bound** (1976, Theorem 10, (6.2)) from RH. -/
theorem schoenfeldPsi_of_RH (hRH : RiemannHypothesis) : SchoenfeldPsi :=
  schoenfeldPsi_of_RH_of_rosser hRH rosserZeroCount

/-- **Schoenfeld's θ bound** (1976, Theorem 10, (6.3)) from RH. -/
theorem schoenfeldTheta_of_RH (hRH : RiemannHypothesis) : SchoenfeldTheta :=
  schoenfeldTheta_of_RH_of_rosser hRH rosserZeroCount

/-- **Schoenfeld's Corollary 1** (1976) from RH. -/
theorem schoenfeldPi_of_RH (hRH : RiemannHypothesis) : SchoenfeldPi :=
  schoenfeldPi_of_RH_of_rosser hRH rosserZeroCount

/-- **Schoenfeld's Theorem 10 and Corollary 1** (1976), `SchoenfeldStatement`, from RH. -/
theorem schoenfeld_of_RH (hRH : RiemannHypothesis) : SchoenfeldStatement :=
  schoenfeld_of_RH_of_rosser hRH rosserZeroCount

end Schoenfeld
