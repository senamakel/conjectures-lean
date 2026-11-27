import Mathlib
import Implications.C4PolarityCnfGates

/-!
# DIMACS encoding of polarity lexicographic constraints

This module mirrors `Cnf.lex_at_least` in
`scripts/encode_c4_polarity_42_cnf.py`. Positions with the same DIMACS variable
are skipped without allocating a prefix variable, as in the Python encoder.
-/

namespace Implications.C4PolarityLexEncoding

open Implications.C4PolarityCnfGates

/-- Value of a signed DIMACS literal under a Boolean variable assignment. -/
def literalValue (a : Nat → Bool) (lit : Int) : Bool :=
  if 0 < lit then a lit.natAbs else !(a lit.natAbs)

/-- Value of a DIMACS clause (a disjunction of signed literals). -/
def clauseValue (a : Nat → Bool) (clause : List Int) : Bool :=
  clause.any (literalValue a)

/-- Value of a DIMACS formula (a conjunction of clauses). -/
def cnfValue (a : Nat → Bool) (clauses : List (List Int)) : Bool :=
  clauses.all (clauseValue a)

private def pos (v : Nat) : Int := Int.ofNat v
private def neg (v : Nat) : Int := -(Int.ofNat v)

/-- One nontrivial iteration of the Python lex loop: its guard clause followed
by the five clauses defining the next equality-prefix variable. -/
def lexStepClauses (prefix x y same : Nat) : List (List Int) :=
  [[neg prefix, pos x, neg y],
   [neg same, pos prefix],
   [neg same, neg x, pos y],
   [neg same, pos x, neg y],
   [neg prefix, pos x, pos y, pos same],
   [neg prefix, neg x, neg y, pos same]]

/-- Compile the exact loop in `Cnf.lex_at_least`. `prefix` is the current
equality-prefix variable and `next` is the next unused variable number. -/
def lexClauses (prefix next : Nat) : List Nat → List Nat → List (List Int)
  | x :: xs, y :: ys =>
      if x == y then lexClauses prefix next xs ys
      else lexStepClauses prefix x y next ++ lexClauses next (next + 1) xs ys
  | _, _ => []

/-- Fresh DIMACS IDs allocated by the lex loop, in allocation order. -/
def lexFreshIds (next : Nat) : List Nat → List Nat → List Nat
  | x :: xs, y :: ys =>
      if x == y then lexFreshIds next xs ys
      else next :: lexFreshIds (next + 1) xs ys
  | _, _ => []

/-- Each unequal variable pair allocates exactly one fresh prefix variable;
identical variables are skipped. -/
theorem lexFreshIds_length (next : Nat) (left right : List Nat) :
    (lexFreshIds next left right).length =
      (List.zip left right).countP (fun p => p.1 != p.2) := by
  induction left generalizing right next with
  | nil => cases right <;> rfl
  | cons x xs ih =>
      cases right with
      | nil => rfl
      | cons y ys =>
          simp only [lexFreshIds, List.zip_cons_cons, List.countP_cons]
          split <;> simp [ih]

/-- The final unused variable is the starting ID plus the number of non-skipped
positions. This is the numbering convention of the Python loop. -/
def lexNext (next : Nat) : List Nat → List Nat → Nat
  | x :: xs, y :: ys =>
      if x == y then lexNext next xs ys else lexNext (next + 1) xs ys
  | _, _ => next

theorem lexNext_eq (next : Nat) (left right : List Nat) :
    lexNext next left right = next + (lexFreshIds next left right).length := by
  induction left generalizing right next with
  | nil => cases right <;> simp [lexNext, lexFreshIds]
  | cons x xs ih =>
      cases right with
      | nil => simp [lexNext, lexFreshIds]
      | cons y ys =>
          simp only [lexNext, lexFreshIds]
          split <;> simp [ih, Nat.add_assoc]

/-- The lex-loop allocator uses consecutive IDs starting at `next`. -/
theorem lexFreshIds_eq_range (next : Nat) (left right : List Nat) :
    lexFreshIds next left right = List.range ((lexFreshIds next left right).length) |>.map (· + next) := by
  induction left generalizing right next with
  | nil => cases right <;> simp [lexFreshIds]
  | cons x xs ih =>
      cases right with
      | nil => simp [lexFreshIds]
      | cons y ys =>
          simp only [lexFreshIds]
          split
          · simpa using ih ys next
          · simp only [List.length_cons]
            rw [ih ys (next + 1)]
            simp [List.range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- DIMACS clauses for an equality-prefix gate are satisfied when `same` is
assigned the exact prefix conjunction. -/
theorem lexStep_extension (a : Nat → Bool) (prefix x y same : Nat)
    (hp : a prefix = true) (hx : a x = true) (hy : a y = false) :
    ∃ b : Nat → Bool, (∀ n, n ≠ same → b n = a n) ∧
      b same = (a prefix && (a x == a y)) ∧
      cnfValue b (lexStepClauses prefix x y same) = true := by
  refine ⟨Function.update a same (a prefix && (a x == a y)), ?_, ?_, ?_⟩
  · intro n hns
    simp [Function.update, hns]
  · simp [Function.update]
  · have hguard : (!a prefix || a x || !a y) = true := by simp [hp, hx, hy]
    have hgate : prefixEqualityClauses (a prefix) (a x) (a y)
        (a prefix && (a x == a y)) = true := by
      apply prefix_equality_iff.mpr
    simp [cnfValue, clauseValue, literalValue, lexStepClauses, pos, neg,
      hguard, hgate, Function.update]

end Implications.C4PolarityLexEncoding

#print axioms Implications.C4PolarityLexEncoding.lexFreshIds_length
#print axioms Implications.C4PolarityLexEncoding.lexNext_eq
#print axioms Implications.C4PolarityLexEncoding.lexFreshIds_eq_range
#print axioms Implications.C4PolarityLexEncoding.lexStep_extension
