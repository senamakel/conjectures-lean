import Erdos770.Statement

/-!
# Erdős Problem 770 (iii): the explicit bound with constant 200

`ExplicitBound` is defined in `Erdos770/Statement.lean`; this file fixes the target proved from
Bach's bound with constant `2`. It is the sharper form of the `420` bound in `Statement.lean`'s
`ExplicitBound 420 2` and is not a formal-conjectures statement.
-/

namespace Erdos770

/-- `h n ≤ max (P n) ⌈200 (log n)²⌉` for every `n ≥ 2`. -/
def ExplicitBound200 : Prop := ExplicitBound 200 2

end Erdos770
