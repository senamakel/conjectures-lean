import Grosswald.Alg

/-!
# Verified computation: Algorithm 1 subtree(s) `N13C`

Evaluated with `native_decide`. This adds one trust assumption: the auxiliary axiom
`n13_C._native.native_decide.ax_*` asserting that the compiled evaluation of the Boolean checker
agrees with its definition. The checker's soundness (`Grosswald.Alg.checkNode_sound`) is proved
without such assumptions.
-/

namespace Grosswald.Run

open Grosswald.Alg

/-- Algorithm 1 for `ω(p-1) = 13`, `X = [11, 7, 5, 3, 2]`, `Y = [13]`. -/
theorem n13_C : checkNode 13 40 [11, 7, 5, 3, 2] [13] = true := by
  native_decide

end Grosswald.Run
