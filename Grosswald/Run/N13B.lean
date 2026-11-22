import Grosswald.Alg

/-!
# Verified computation: Algorithm 1 subtree(s) `N13B`

Evaluated with `native_decide`. This adds one trust assumption: the auxiliary axiom
`n13_B._native.native_decide.ax_*` asserting that the compiled evaluation of the Boolean checker
agrees with its definition. The checker's soundness (`Grosswald.Alg.checkNode_sound`) is proved
without such assumptions.
-/

namespace Grosswald.Run

open Grosswald.Alg

/-- Algorithm 1 for `ω(p-1) = 13`, `X = [13, 11, 7, 5, 3, 2]`, `Y = [17]`. -/
theorem n13_B : checkNode 13 40 [13, 11, 7, 5, 3, 2] [17] = true := by
  native_decide

end Grosswald.Run
