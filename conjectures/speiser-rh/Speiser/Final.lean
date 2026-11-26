import Speiser.Main
import Speiser.Band.Main

/-!
# Speiser's theorem under RH: the whole strip

`SpeiserBelow (5/2)` (`Speiser.Low`, under RH), the band `SpeiserBand (5/2) 7`
(`Speiser.Band.Main`, a verified computation, no hypothesis) and `SpeiserAbove 7`
(`Speiser.Main`, under RH).
-/

namespace Speiser

/-- **RH ⇒ `ζ'(s) ≠ 0` for `0 < Re s < 1/2`.** -/
theorem speiser_of_RH (hRH : RiemannHypothesis) : SpeiserStatement :=
  speiser_of_RH_of_band hRH Band.speiserBand

end Speiser
