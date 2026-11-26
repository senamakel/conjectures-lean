/-!
# Executable part of the generation checker (core Lean only)

These definitions use nothing beyond core Lean so that this library can be precompiled to native
code (`precompileModules`), which `native_decide` in `Ankeny/Compute.lean` then runs. The
soundness proofs are in `Ankeny/Checker.lean`.
-/

namespace Ankeny.Checker

/-- Is index `i` marked? -/
def marked (arr : Array Bool) (i : Nat) : Bool := arr[i]?.getD false

/-- Multiply `r` by every generator; mark and enqueue the new residues. -/
def bfsStep (q : Nat) (gens : List Nat) (r : Nat) (st : Array Bool × List Nat) :
    Array Bool × List Nat :=
  gens.foldl (fun acc g =>
    let t := r * g % q
    if marked acc.1 t then acc else (acc.1.setIfInBounds t true, t :: acc.2)) st

/-- Graph search from a work list, with fuel. -/
def bfs (q : Nat) (gens : List Nat) : Nat → Array Bool → List Nat → Array Bool
  | 0, arr, _ => arr
  | _ + 1, arr, [] => arr
  | n + 1, arr, r :: rest =>
    let st := bfsStep q gens r (arr, rest)
    bfs q gens n st.1 st.2

/-- Primes below `2000` (only used to pick candidate generators; never trusted). -/
def smallPrimes : List Nat :=
  (List.range 2000).filter fun g => 2 ≤ g && (List.range' 2 (g - 2)).all fun d => g % d != 0

/-- Candidate generators: the first `k` of the small primes `g ≤ y`, `g < q`, coprime to `q`. -/
def gensFor (q y k : Nat) : List Nat :=
  (smallPrimes.filter fun g => g ≤ y && g < q && Nat.gcd g q == 1).take k

/-- Does the search from `1` with generators `gens` reach every residue coprime to `q`? -/
def reachesAll (q : Nat) (gens : List Nat) : Bool :=
  let arr := bfs q gens (q + 1) ((Array.replicate q false).setIfInBounds 1 true) [1]
  (List.range q).all fun a => Nat.gcd a q != 1 || marked arr a

/-- The checker: try 3 generators, then 8, then all candidates. -/
def checkGen (q y : Nat) : Bool :=
  reachesAll q (gensFor q y 3) || reachesAll q (gensFor q y 8) || reachesAll q (gensFor q y q)

/-- `⌊(cn/cd) (⌊log₂ q⌋ · 0.6931471803)²⌋`, a certified lower bound for `(cn/cd) log² q`. -/
def yOf (cn cd q : Nat) : Nat := cn * (Nat.log2 q) ^ 2 * 6931471803 ^ 2 / (cd * 10 ^ 20)

/-- The finite check over `lo ≤ q < lo + n`, with constant `cn/cd`. -/
def checkRange (cn cd lo n : Nat) : Bool :=
  (List.range' lo n).all fun q => decide (q ≤ 2) || checkGen q (yOf cn cd q)

end Ankeny.Checker
