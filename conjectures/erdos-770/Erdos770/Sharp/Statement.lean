import Erdos770.Statement

/-!
# Erdős Problem 770 (iii): the explicit bound with constant 5 (target, fixed)

`ExplicitBound` is defined in `Erdos770/Statement.lean`. This file fixes the sharper target
`h n ≤ max (P n) ⌈5 (log n)²⌉` for every `n ≥ 2`. It is not a formal-conjectures statement; it
implies `Erdos770Part3` through `erdos_770_iii_of_explicit`.

On the data (`docs/SHARP.md`) every constant `C > 2 / log² 3 ≈ 1.657` satisfies
`ExplicitBound C 2` for `n ≤ 10⁵`, with `n = 3` extremal (`h 3 = 3`, `P 3 = 2`). The constant `5`
is what the method proves; its limit is `4`.
-/

namespace Erdos770

/-- `h n ≤ max (P n) ⌈5 (log n)²⌉` for every `n ≥ 2`. -/
def ExplicitBound5 : Prop := ExplicitBound 5 2

end Erdos770
