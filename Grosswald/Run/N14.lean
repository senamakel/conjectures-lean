import Grosswald.Alg

/-!
# Verified computation: Algorithm 1 subtree(s) `N14`

Evaluated with `native_decide`. This adds one trust assumption: the auxiliary axiom
`n14._native.native_decide.ax_*` asserting that the compiled evaluation of the Boolean checker
agrees with its definition. The checker's soundness (`Grosswald.Alg.checkNode_sound`) is proved
without such assumptions.
-/

namespace Grosswald.Run

open Grosswald.Alg

/-- Algorithm 1 for `ω(p-1) = 14`, `X = [2]`, `Y = []`. -/
theorem n14 : checkNode 14 40 [2] [] = true := by
  native_decide

end Grosswald.Run
