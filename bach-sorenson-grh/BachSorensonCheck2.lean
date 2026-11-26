import BachSorensonCheck

/-!
# Executable part of the finite check for the constant `2` (core Lean only)

The same walk as `BachSorensonCheck.lean` (prime table by trial division, progression walk
`a, a + q, a + 2q, …`), with the bound `bound2 q ≤ 2 (q log q)²`. Precompiled to native code
for `native_decide` in `BachSorenson/Compute2/`; soundness is `BachSorenson/Checker2.lean`.
-/

namespace BachSorenson.Checker

/-- `⌊2 q² (⌊log₂ q⁸⌋ · 0.6931471803 / 8)²⌋`, strictly below `2 (q log q)²` for `q ≥ 2`. -/
def bound2 (q : Nat) : Nat :=
  2 * q * q * (Nat.log2 (q ^ 8)) ^ 2 * 6931471803 ^ 2 / (64 * 10 ^ 20)

/-- Every residue class coprime to `q` has a marked entry `≤ bound2 q`. (`bound2 q` is the floor
of a number strictly below `2 (q log q)²`, so `≤` suffices; it matters for `q = 2`, where the
prime `3` lies below `2 (2 log 2)² ≈ 3.84` but `bound2 2 = 3`.) -/
def checkQ2 (arr : Array Bool) (q : Nat) : Bool :=
  (List.range q).all fun a =>
    Nat.gcd a q != 1 || findFrom arr q (bound2 q + 1) a ((bound2 q + 1) / q + 1)

/-- The finite check over `lo ≤ q < lo + n`, with a prime table of size `N`. -/
def checkRange2 (N lo n : Nat) : Bool :=
  let arr := primeTable N
  (List.range' lo n).all fun q => decide (q < 2) || checkQ2 arr q

end BachSorenson.Checker
