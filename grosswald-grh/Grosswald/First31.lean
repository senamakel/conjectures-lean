import Grosswald.Alg

/-!
# Verified computation: the first 31 primes

Evaluated with `native_decide` (trust assumption `first31_ok._native.native_decide.ax_*`): their
product exceeds `10^47`, so `p < 10^47` forces `ω(p-1) ≤ 30`.
-/

namespace Grosswald.Run

open Grosswald.Alg

theorem first31_ok : LOk 31 [] (firstPrimesAvoiding 31 []) = true ∧
    10 ^ 47 ≤ (firstPrimesAvoiding 31 []).prod := by
  native_decide

end Grosswald.Run
