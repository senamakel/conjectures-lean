import Grosswald.Alg

/-!
# Verified computation: root nodes for `ω(p-1) ∉ {12, 13, 14}`, small `n = 13` nodes, and the first 31 primes

Evaluated with `native_decide`. This adds one trust assumption: the auxiliary axiom
`roots_ok._native.native_decide.ax_*` asserting that the compiled evaluation of the Boolean checker
agrees with its definition. The checker's soundness (`Grosswald.Alg.checkNode_sound`) is proved
without such assumptions.
-/

namespace Grosswald.Run

open Grosswald.Alg

/-- The roots `(n, [2], [])` for `1 ≤ n ≤ 30`, `n ∉ {12, 13, 14}`: here the lower bound already
exceeds the upper bound (MTT Corollary 4). -/
theorem roots_ok : ((List.range' 1 30).filter (fun n => n ∉ [12, 13, 14])).all
    (fun n => checkNode n 40 [2] []) = true := by
  native_decide

/-- Three `n = 13` nodes with nothing to enumerate. -/
theorem n13_small : checkNode 13 40 [2] [3] = true ∧ checkNode 13 40 [3, 2] [5] = true ∧
    checkNode 13 40 [5, 3, 2] [7] = true := by
  native_decide

/-- The first 31 primes: their product exceeds `10^47`, so `p < 10^47` forces `ω(p-1) ≤ 30`. -/
theorem first31_ok : LOk 31 [] (firstPrimesAvoiding 31 []) = true ∧
    10 ^ 47 ≤ (firstPrimesAvoiding 31 []).prod := by
  native_decide

end Grosswald.Run
