/-!
# Executable part of the finite check (core Lean only)

These definitions use nothing beyond core Lean so that this library can be precompiled to native
code (`precompileModules`), which `native_decide` in `BachSorenson/Compute/` then runs. The
soundness proofs are in `BachSorenson/Checker.lean`.

For each modulus `q` in range and each residue `a < q` coprime to `q`, the check walks the
progression `a, a + q, a + 2q, …` below `bound q` and looks each term up in a table of primes.
The table is built by trial division; only the soundness direction (a `true` entry is a prime) is
ever used.
-/

namespace BachSorenson.Checker

/-- Trial division from `d`: `true` when no `m ≥ d` with `m * m ≤ n` divides `n`. Returns `false`
when the fuel runs out (which only costs completeness). -/
def trialFrom (n : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | d, fuel + 1 => if n < d * d then true else if n % d == 0 then false else trialFrom n (d + 1) fuel

/-- Primality by trial division. -/
def isPrimeB (n : Nat) : Bool := 2 ≤ n && trialFrom n 2 n

/-- The table `i ↦ isPrimeB i` for `i < N`. -/
def primeTable (N : Nat) : Array Bool := Array.ofFn (n := N) fun i => isPrimeB i.val

/-- Table lookup; `false` outside the table. -/
def marked (arr : Array Bool) (i : Nat) : Bool := arr[i]?.getD false

/-- Walk `p, p + q, p + 2q, …` while below `B`, looking for a marked entry. -/
def findFrom (arr : Array Bool) (q B : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | p, fuel + 1 =>
    if B ≤ p then false else if marked arr p then true else findFrom arr q B (p + q) fuel

/-- `⌊(7/2) q² (⌊log₂ q⁸⌋ · 0.6931471803 / 8)²⌋`, a certified lower bound for
`(7/2) (q log q)²`. -/
def bound (q : Nat) : Nat :=
  7 * q * q * (Nat.log2 (q ^ 8)) ^ 2 * 6931471803 ^ 2 / (2 * 64 * 10 ^ 20)

/-- Every residue class coprime to `q` has a marked entry below `bound q`. -/
def checkQ (arr : Array Bool) (q : Nat) : Bool :=
  (List.range q).all fun a => Nat.gcd a q != 1 || findFrom arr q (bound q) a (bound q / q + 1)

/-- The finite check over `lo ≤ q < lo + n`, with a prime table of size `N`. -/
def checkRange (N lo n : Nat) : Bool :=
  let arr := primeTable N
  (List.range' lo n).all fun q => decide (q < 2) || checkQ arr q

end BachSorenson.Checker
