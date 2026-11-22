import Grosswald.Alg

/-!
# Verified computation: Algorithm 1 subtree(s) `N13D`

Evaluated with `native_decide`. This adds one trust assumption: the auxiliary axiom
`n13_D._native.native_decide.ax_*` asserting that the compiled evaluation of the Boolean checker
agrees with its definition. The checker's soundness (`Grosswald.Alg.checkNode_sound`) is proved
without such assumptions.
-/

namespace Grosswald.Run

open Grosswald.Alg

/-- Algorithm 1 for `ω(p-1) = 13`, `X = [7, 5, 3, 2]`, `Y = [11]`. -/
theorem n13_D : checkNode 13 40 [7, 5, 3, 2] [11] = true := by
  native_decide

end Grosswald.Run
