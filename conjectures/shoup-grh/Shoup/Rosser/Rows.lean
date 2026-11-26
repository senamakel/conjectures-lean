import Shoup.Rosser.Check

/-!
# The row checks of the Rosser table

A cell `(g, β, α)` claims `U ≤ V (1 + β/D)` and, when `g ≥ 200`, `L ≥ V (1 - α/D)`, at every
`s = log Y / log z ≥ g/100`.

* lower row (`lrowOK`): head `β` of the last cell with `g' + 100 ≤ g`, then the entries
  `((g' + 100)/g, β')` of the cells with `g < g' + 100`; end `1300/g`;
* upper row (`urowOK`): head `1` (or `α` of the last cell with `210 ≤ g'`, `g' + 100 ≤ g`),
  then `((g' + 100)/g, α')` for the cells with `210 ≤ g'`, `g < g' + 100`; end `1300/g`;
* tail rows (`tailOK`), for `s ≥ 12`, normalised by `s^{-6}`: heights `(u - 1/12)^{-6}`, and
  at least `X = 13^6 β` (or `13^6 α`) of the cell `g = 1100` below `u = 13/12`; end `4`.
-/

namespace Shoup.Rosser

open Shoup.Fixed

def headL (cells : List Ent) (S : ℕ) : Option Ent :=
  (cells.filter fun d => decide (d.1 + 100 ≤ S)).getLast?

def entsL (cells : List Ent) (S b0 : ℕ) : List Ent :=
  (1, 1, b0) :: (cells.filter fun d => decide (S < d.1 + 100)).map fun d => (d.1 + 100, S, d.2.1)

def rowTail (l : List Ent) (S target : ℕ) : Bool :=
  chainOK l && boundsOK l 1300 S && decide (0 < S) && decide (S ≤ 1300) &&
    decide (momU l 1300 S + crudeU 1300 S ≤ target)

def lrowOK (cells : List Ent) (c : Ent) : Bool :=
  match headL cells c.1 with
  | none => false
  | some c0 => rowTail (entsL cells c.1 c0.2.1) c.1 c.2.2

def headU (cells : List Ent) (S : ℕ) : ℕ :=
  match (cells.filter fun d => decide (210 ≤ d.1 ∧ d.1 + 100 ≤ S)).getLast? with
  | none => Dn
  | some c0 => c0.2.2

def entsU (cells : List Ent) (S : ℕ) : List Ent :=
  (1, 1, headU cells S) ::
    (cells.filter fun d => decide (210 ≤ d.1 ∧ S < d.1 + 100)).map fun d => (d.1 + 100, S, d.2.2)

def urowOK (cells : List Ent) (c : Ent) : Bool :=
  rowTail (entsU cells c.1) c.1 c.2.1

def tpts : List (ℕ × ℕ) :=
  (List.range 11).map (fun q => (120 + q, 120)) ++ (List.range 59).map (fun j => (815 + 35 * j, 720))

def tH (X : ℕ) (x : ℕ × ℕ) : ℕ :=
  if 12 * x.1 < 13 * x.2 then max X (psiU x.1 x.2) else psiU x.1 x.2

def entsT (X : ℕ) : List Ent := tpts.map fun x => (x.1, x.2, tH X x)

def tailOK (X : ℕ) : Bool :=
  chainOK (entsT X) && boundsOK (entsT X) 4 1 && decide (momU (entsT X) 4 1 + tailCrude ≤ Dn)

def tailCells (cells : List Ent) : Bool :=
  match cells.find? (fun d => decide (d.1 = 1100)) with
  | none => false
  | some c => tailOK (13 ^ 6 * c.2.1) && tailOK (13 ^ 6 * c.2.2)

def allOK (cells : List Ent) : Bool :=
  cells.all (fun c => (decide (c.1 < 200) || lrowOK cells c) && urowOK cells c) &&
    tailCells cells &&
    cells.any (fun c => decide (c.1 = 210 ∧ c.2.2 ≤ Dn)) &&
    cells.any (fun c => decide (c.1 = 205 ∧ 100 * c.2.2 ≤ 98 * Dn))

end Shoup.Rosser
