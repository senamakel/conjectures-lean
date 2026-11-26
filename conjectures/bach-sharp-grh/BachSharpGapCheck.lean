import BachSharpCheck

/-!
# Executable checkers for the gap `2^17 ≤ q < 5 · 2^49` (core Lean only)

Nothing here is trusted. `BachSharp/GenCert.lean` proves `genCert` sound and
`BachSharp/GapSound.lean` proves `checkChunkG` sound (`docs/GAP.md` explains the design).

* `genCert q x`: the units of residue `≤ x` generate `(ZMod q)ˣ`, certified by the Frattini rank
  test. `q` is factored by trial division into prime powers `Q_j = p_j^{e_j}`; for each prime `ℓ`
  dividing some `n_j = φ(Q_j)` the checker lists coordinates `u ↦ (u mod N)^E` (one per odd
  component with `ℓ ∣ n_j`, `(Q_j, n_j/ℓ)`; for `ℓ = 2` also `(4, 1)` if `4 ∣ q`, `(8, 1)` if
  `8 ∣ q`), finds by elimination over `𝔽_ℓ` words `h_i = ∏ s^{e_s}` in the primes `s ≤ x`,
  `s ∤ q` with `ψ_k(h_i) = 1` for `k < i` and `ψ_i(h_i) ≠ 1`, and verifies them.
* `checkChunkG`: lls-grh's block checker with constant `cn/cd`, where the loop over the moduli of
  a block is replaced by a depth-first search over the kernels (the sets of primes `p ≤ x`
  dividing `q`) whose weight can reach the budget; each modulus of such a kernel is accepted by
  its own weight or by `genCert`.
-/

namespace BachSharp.Gap

open LLS.Check

/-! ### Arithmetic -/

/-- `b ^ e % m` by repeated squaring (the fallback is never reached for `e < 2 ^ fuel`). -/
def powModF (m : Nat) : Nat → Nat → Nat → Nat
  | 0, b, e => b ^ e % m
  | fuel + 1, b, e =>
    if e = 0 then 1 % m
    else
      let r := powModF m fuel (b * b % m) (e / 2)
      if e % 2 = 0 then r else b * r % m

/-- `b ^ e % m`. -/
def powMod (b e m : Nat) : Nat := powModF m 64 (b % m) e

/-- Primality by trial division up to `√p`. -/
def isPrimeS (p : Nat) : Bool :=
  2 ≤ p && (List.range' 2 (Nat.sqrt p - 1)).all fun d => p % d != 0

/-- Divide out `d` from `n`: `(n / d^e, e)`. -/
def divOut (d : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, n, e => (n, e)
  | fuel + 1, n, e => if n % d == 0 && 2 ≤ d then divOut d fuel (n / d) (e + 1) else (n, e)

/-- Trial-division factorisation (untrusted; `factOK` checks the result). -/
def factorF : Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, n, acc => if n == 1 then acc.reverse else ((n, 1) :: acc).reverse
  | fuel + 1, d, n, acc =>
    if n ≤ 1 then acc.reverse
    else if n < d * d then ((n, 1) :: acc).reverse
    else if n % d == 0 then
      let r := divOut d 64 n 0
      factorF fuel (d + 1) r.1 ((d, r.2) :: acc)
    else factorF fuel (d + 1) n acc

/-- A factorisation of `n`. -/
def factor (n : Nat) : List (Nat × Nat) := factorF 1000000 2 n []

/-- `fs` is a factorisation of `n` into prime powers `p ^ e`, `e ≥ 1`. -/
def factOK (n : Nat) (fs : List (Nat × Nat)) : Bool :=
  (fs.map fun pe => pe.1 ^ pe.2).prod == n && fs.all fun pe => isPrimeS pe.1 && 1 ≤ pe.2

/-- Strictly increasing first coordinates. -/
def incr : List (Nat × Nat) → Bool
  | a :: b :: l => a.1 < b.1 && incr (b :: l)
  | _ => true

/-! ### Coordinates and words -/

/-- `φ(p ^ e)` for `e ≥ 1`. -/
def phiPE (p e : Nat) : Nat := p ^ (e - 1) * (p - 1)

/-- The coordinates `(N, E)` contributed by the component `p ^ e` for the prime `ℓ`. -/
def coordsOf (ℓ : Nat) (pe : Nat × Nat) : List (Nat × Nat) :=
  if pe.1 = 2 then
    (if ℓ = 2 ∧ 2 ≤ pe.2 then [(4, 1)] else []) ++ (if ℓ = 2 ∧ 3 ≤ pe.2 then [(8, 1)] else [])
  else if phiPE pe.1 pe.2 % ℓ = 0 then [(pe.1 ^ pe.2, phiPE pe.1 pe.2 / ℓ)] else []

/-- All coordinates for `ℓ`. -/
def coords (ℓ : Nat) (fs : List (Nat × Nat)) : List (Nat × Nat) := fs.flatMap (coordsOf ℓ)

/-- A word `∏ s ^ e` reduced mod `N`. -/
def evalW (N : Nat) (w : List (Nat × Nat)) : Nat :=
  w.foldl (fun acc se => acc * powMod se.1 se.2 N % N) (1 % N)

/-- The coordinate `(N, E)` of a word: `(w mod N) ^ E mod N`. -/
def psiW (c : Nat × Nat) (w : List (Nat × Nat)) : Nat := powMod (evalW c.1 w) c.2 c.1

/-- The letters of a word are primes `s ≤ x` prime to `q`, given with `1 ≤ s`. -/
def wordOK (q x : Nat) (w : List (Nat × Nat)) : Bool :=
  w.all fun se => decide (1 ≤ se.1) && decide (se.1 ≤ x) && Nat.gcd se.1 q == 1

/-- The echelon conditions for coordinates `cs` and words `ws`. -/
def echOK (q x : Nat) (cs : List (Nat × Nat)) (ws : List (List (Nat × Nat))) : Bool :=
  ws.length == cs.length &&
  (List.range cs.length).all fun i =>
    let w := ws.getD i []
    wordOK q x w &&
    (List.range i).all (fun k => psiW (cs.getD k (1, 1)) w == 1 % (cs.getD k (1, 1)).1) &&
    psiW (cs.getD i (1, 1)) w != 1 % (cs.getD i (1, 1)).1

/-! ### The search for echelon words (untrusted) -/

/-- A row: pivot, coordinate values, word. -/
structure Row where
  piv : Nat
  vals : List Nat
  word : List (Nat × Nat)

/-- `w1 · w2 ^ t`, exponents mod `ℓ`. -/
def addW (ℓ t : Nat) (w1 w2 : List (Nat × Nat)) : List (Nat × Nat) :=
  w2.foldl (fun acc se =>
    match acc.find? (fun a => a.1 == se.1) with
    | some a => acc.map fun b => if b.1 == se.1 then (b.1, (a.2 + t * se.2) % ℓ) else b
    | none => acc ++ [(se.1, t * se.2 % ℓ)]) w1

/-- The `t < ℓ` with `c · z ^ t ≡ 1 (mod N)`. -/
def dlogF (N z : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, c, t => if c % N == 1 % N then t else dlogF N z fuel (c * z % N) (t + 1)

/-- Reduce `(vals, word)` against the rows (ascending pivots). -/
def reduceV (ℓ : Nat) (cs : List (Nat × Nat)) : List Row → List Nat → List (Nat × Nat) →
    List Nat × List (Nat × Nat)
  | [], v, w => (v, w)
  | r :: rs, v, w =>
    let c := v.getD r.piv 1
    let N := (cs.getD r.piv (1, 1)).1
    if c % N == 1 % N then reduceV ℓ cs rs v w
    else
      let t := dlogF N (r.vals.getD r.piv 1) (ℓ + 1) c 0
      let v' := (List.range cs.length).map fun i =>
        let Ni := (cs.getD i (1, 1)).1
        v.getD i 1 * powMod (r.vals.getD i 1) t Ni % Ni
      reduceV ℓ cs rs v' (addW ℓ t w r.word)

/-- Insert a row keeping pivots ascending. -/
def insRow (r : Row) : List Row → List Row
  | [] => [r]
  | s :: rs => if r.piv < s.piv then r :: s :: rs else s :: insRow r rs

/-- Process candidate letters until `cs.length` rows are found. -/
def searchE (q x ℓ : Nat) (cs : List (Nat × Nat)) : List Nat → List Row → List Row
  | [], rows => rows
  | s :: ss, rows =>
    if rows.length = cs.length then rows
    else if x < s ∨ q % s = 0 then searchE q x ℓ cs ss rows
    else
      let v := cs.map fun c => powMod (s % c.1) c.2 c.1
      let red := reduceV ℓ cs rows v [(s, 1)]
      let piv := (List.range cs.length).find? fun i =>
        red.1.getD i 1 % (cs.getD i (1, 1)).1 != 1 % (cs.getD i (1, 1)).1
      match piv with
      | some i => searchE q x ℓ cs ss (insRow ⟨i, red.1, red.2⟩ rows)
      | none => searchE q x ℓ cs ss rows

/-- The words for `ℓ`, in pivot order. -/
def wordsFor (q x ℓ : Nat) (cs : List (Nat × Nat)) : List (List (Nat × Nat)) :=
  (searchE q x ℓ cs primesL []).map fun r => r.word.filter fun se => se.2 != 0

/-! ### The certificate -/

/-- Add the primes of `fs` to `L`. -/
def addPrimes (L : List Nat) (fs : List (Nat × Nat)) : List Nat :=
  fs.foldl (fun acc pe => if acc.contains pe.1 then acc else pe.1 :: acc) L

/-- The certificate that the units `≤ x` generate `(ZMod q)ˣ`. -/
def genCert (q x : Nat) : Bool :=
  let fs := factor q
  factOK q fs && incr fs &&
  let nfs := fs.map fun pe => factor (phiPE pe.1 pe.2)
  let L := nfs.foldl addPrimes []
  (fs.zip nfs).all (fun pr => factOK (phiPE pr.1.1 pr.1.2) pr.2 && pr.2.all fun le => L.contains le.1) &&
  L.all fun ℓ => isPrimeS ℓ &&
    let cs := coords ℓ fs
    echOK q x cs (wordsFor q x ℓ cs)

/-! ### Kernel enumeration in a block -/

/-- `⌊log₂ n^8⌋`. -/
def lam8 (n : Nat) : Nat := Nat.log2 (n ^ 8)

/-- Attach to each `(p, w)` a suffix maximum of `⌈w / λ(p)⌉`. -/
def rhoList : List (Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | pw :: l =>
    let t := rhoList l
    let r0 := (pw.2 + lam8 pw.1 - 1) / lam8 pw.1
    (pw.1, pw.2, max r0 (match t with | [] => 0 | e :: _ => e.2.2)) :: t

/-- Each entry has `w ≤ ρ λ(p)`, `2 ≤ p`, `ρ` nonincreasing and `p` increasing. -/
def rhoOK : List (Nat × Nat × Nat) → Bool
  | [] => true
  | e :: l => decide (2 ≤ e.1) && decide (e.2.1 ≤ e.2.2 * lam8 e.1) &&
      (match l with
       | [] => true
       | f :: _ => decide (e.1 < f.1) && decide (f.2.2 ≤ e.2.2)) && rhoOK l

/-- `Σ_{(p, w, _) ∈ l, p ∣ q} w`. -/
def sumR (q : Nat) (l : List (Nat × Nat × Nat)) : Nat :=
  sumDiv q (l.map fun e => (e.1, e.2.1)) 0

/-- One modulus at a node. -/
def visitQ (x Bn w : Nat) (rest : List (Nat × Nat × Nat)) (excl : List Nat) (P q : Nat) : Bool :=
  excl.any (fun p => q % p == 0 && P % p != 0) || decide (w + sumR q rest < Bn) || genCert q x

/-- Every multiple of `P` in `[a, b)`. -/
def visitAll (a b x Bn w : Nat) (rest : List (Nat × Nat × Nat)) (excl : List Nat) (P : Nat) :
    Bool :=
  let k0 := (a + P - 1) / P
  let k1 := (b - 1) / P
  allQ (fun k => visitQ x Bn w rest excl P (k * P)) k0 (k1 + 1 - k0)

/-- The search below a node `(rest, P, w, excl)`. -/
def dfs (a b x Bn T : Nat) : Nat → List (Nat × Nat × Nat) → Nat → Nat → List Nat → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, rest, P, w, excl =>
    let R := (b - 1) / P
    let pruned := w < Bn &&
      (match rest with
       | [] => true
       | e :: _ => decide (R < e.1) || decide (w + e.2.2 * (8 * Nat.log2 R + 8) < Bn))
    if pruned then true
    else if Bn ≤ w || (b - 1) / P - (a - 1) / P ≤ T then visitAll a b x Bn w rest excl P
    else match rest with
      | [] => false
      | e :: rest' =>
        P % e.1 != 0 && dfs a b x Bn T fuel rest' (P * e.1) (w + e.2.1) excl &&
          dfs a b x Bn T fuel rest' P w (e.1 :: excl)

/-- The integer budget of a block. -/
def bnOf (d : BD) : Nat := (Bq d * (SC : Rat)).floor.toNat

def blockOKG (cn cd m T a b : Nat) : Bool :=
  let d := BachSharp.Check.mkBDC cn cd m a b
  decide (0 ≤ d.La) && decide ((d.x : Rat) ≤ (cn : Rat) * d.La * d.La / (cd : Rat)) &&
  decide (64 ≤ d.x) && sideOK d && (unifOK d ||
    (decide (d.x < NP) && wListOK d && decide ((bnOf d : Rat) / (SC : Rat) ≤ Bq d) &&
      let rl := rhoList (wList d)
      rhoOK rl && dfs a b d.x (bnOf d) T (rl.length + 2) rl 1 0 []))

/-- Blocks `[a, a + max 1 ⌊a/2^w⌋)` up to `hi`. -/
def goG (cn cd m w T hi : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, a =>
    if hi ≤ a then true
    else
      let b := min hi (a + max 1 (a >>> w))
      blockOKG cn cd m T a b && goG cn cd m w T hi fuel b

/-- The check for `lo ≤ q < hi` (`3 ≤ lo`) with constant `cn/cd`. -/
def checkChunkG (cn cd m w T lo hi : Nat) : Bool :=
  decide (3 ≤ lo) && decide (1 ≤ m) && decide (0 < cd) && goG cn cd m w T hi (hi - lo) lo

end BachSharp.Gap
