import Mertens.Main
import Mertens.Redheffer

/-!
# `det R_n = O(n^{1/2+ε})` under RH

Redheffer's identity `det R_n = M(n)` (tier D, `Mertens/Redheffer.lean`) and Littlewood's bound.
-/

namespace Mertens

open Filter Asymptotics

/-- Under RH, Redheffer's determinant is `O(n^{1/2+ε})` for every `ε > 0`. -/
theorem redheffer_of_RH (hRH : RiemannHypothesis) : RedhefferBound := by
  intro ε hε
  have h := (mertens_of_RH hRH ε hε).comp_tendsto tendsto_natCast_atTop_atTop
  refine IsBigO.congr' h ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [Function.comp, det_redheffer n hn]

end Mertens
