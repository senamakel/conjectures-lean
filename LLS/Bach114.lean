import LLS.BachCore
import LLS.Numerics.Intervals114
import LLS.Numerics.Tail114

/-!
# Bach's subgroup bound with constant `11/4` for `q ≥ 2^18`, under GRH

`GoodQ (11/4) q` is certified for `2^18 ≤ q < 2^700` in `Intervals114` and for `q ≥ 2^700` in
`Tail114`; `LLS.bach_of_goodQ` turns it into the bound.
-/

set_option exponentiation.threshold 1024

namespace LLS

open Erdos985 (DirichletLNonvanishingRightOfHalf)

theorem goodQ_114 (q : ℕ) (hq : 2 ^ 18 ≤ q) : GoodQ (11 / 4) q := by
  rcases lt_or_ge q (2 ^ 700) with h | h
  · exact Iv114.goodQ_range q (by simpa using hq) (by simpa using h)
  · exact goodQ_tail114 q h

theorem bach_large114 (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) [NeZero q]
    (hq : 2 ^ 18 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 11 / 4 * Real.log q ^ 2 :=
  bach_of_goodQ hGRH q (goodQ_114 q hq) H hH

end LLS
