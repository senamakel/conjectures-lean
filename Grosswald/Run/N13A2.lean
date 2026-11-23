import Grosswald.Alg

/-!
# Verified computation: Algorithm 1 subtree(s) `N13A2`

Evaluated with `native_decide`. This adds one trust assumption: the auxiliary axiom
`n13_A2._native.native_decide.ax_*` asserting that the compiled evaluation of the Boolean checker
agrees with its definition. The checker's soundness (`Grosswald.Alg.checkNode_sound`) is proved
without such assumptions.
-/

namespace Grosswald.Run

open Grosswald.Alg

/-- Algorithm 1 for `ω(p-1) = 13`, `X = [17, 13, 11, 7, 5, 3, 2]`, `Y = [19]`. -/
theorem n13_A2 : checkNode 13 40 [17, 13, 11, 7, 5, 3, 2] [19] = true := by
  native_decide

end Grosswald.Run
