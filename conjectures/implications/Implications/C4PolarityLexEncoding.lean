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

def literalValue (a : Nat → Bool) (lit : Int) : Bool :=
  match lit with
  | .ofNat n => a n
  | .negSucc n => !a (n + 1)

def clauseValue (a : Nat → Bool) (clause : List Int) : Bool :=
  clause.any (literalValue a)

def cnfValue (a : Nat → Bool) (clauses : List (List Int)) : Bool :=
  clauses.all (clauseValue a)

private def pos (v : Nat) : Int := Int.ofNat v
private def neg (v : Nat) : Int := -(Int.ofNat v)

@[simp] private theorem literalValue_pos (a : Nat → Bool) (v : Nat) (_hv : 0 < v) :
    literalValue a (pos v) = a v := by
  simp [literalValue, pos]

@[simp] private theorem literalValue_neg (a : Nat → Bool) (v : Nat) (hv : 0 < v) :
    literalValue a (neg v) = !a v := by
  have hneg : neg v = Int.negOfNat v := by simp [neg, Int.negOfNat_eq]
  rw [hneg]
  cases v with
  | zero => omega
  | succ n => simp [literalValue, Int.negOfNat]

/-- One nontrivial iteration of the Python lex loop: its guard clause followed
by the five clauses defining the next equality-prefix variable. -/
def lexStepClauses (pref x y same : Nat) : List (List Int) :=
  [[neg pref, pos x, neg y],
   [neg same, pos pref],
   [neg same, neg x, pos y],
   [neg same, pos x, neg y],
   [neg pref, pos x, pos y, pos same],
   [neg pref, neg x, neg y, pos same]]

/-- Compile the exact loop in `Cnf.lex_at_least`. `prefix` is the current
equality-prefix variable and `next` is the next unused variable number. -/
def lexClauses (pref next : Nat) : List Nat → List Nat → List (List Int)
  | x :: xs, y :: ys =>
      if x == y then lexClauses pref next xs ys
      else lexStepClauses pref x y next ++ lexClauses next (next + 1) xs ys
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
          by_cases hxy : x = y
          · simp [hxy, ih]
          · simp [hxy, ih]

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
          by_cases hxy : x = y
          · simp [lexNext, lexFreshIds, hxy, ih]
          · simp [lexNext, lexFreshIds, hxy, ih, Nat.add_assoc, Nat.add_comm]

/-- Every auxiliary ID is at least the allocator's initial next variable. -/
theorem lexFreshIds_ge (next : Nat) (left right : List Nat) :
    ∀ v ∈ lexFreshIds next left right, next ≤ v := by
  induction left generalizing right next with
  | nil => cases right <;> simp [lexFreshIds]
  | cons x xs ih =>
      cases right with
      | nil => simp [lexFreshIds]
      | cons y ys =>
          by_cases hxy : x = y
          · simpa [lexFreshIds, hxy] using ih next ys
          · have hbeq : (x == y) = false := by simp [hxy]
            intro v hv
            simp [lexFreshIds, hbeq] at hv
            rcases hv with rfl | hv
            · exact Nat.le_refl _
            · have hge := lexFreshIds_ge (next + 1) xs ys v hv
              omega

/-- The lex allocator never reuses an auxiliary DIMACS variable. -/
theorem lexFreshIds_nodup (next : Nat) (left right : List Nat) :
    (lexFreshIds next left right).Nodup := by
  induction left generalizing right next with
  | nil => cases right <;> simp [lexFreshIds]
  | cons x xs ih =>
      cases right with
      | nil => simp [lexFreshIds]
      | cons y ys =>
          by_cases hxy : x = y
          · simpa [lexFreshIds, hxy] using ih next ys
          · have hbeq : (x == y) = false := by simp [hxy]
            simp [lexFreshIds, hbeq]

/-- Identical DIMACS variables have the same assigned bit, which justifies
skipping that position without an auxiliary equality gate. -/
theorem identical_variables_same_value (a : Nat → Bool) {x y : Nat}
    (hxy : x = y) : a x = a y := by
  subst y
  rfl

/-- DIMACS clauses for an equality-prefix gate are satisfied when `same` is
assigned the exact prefix conjunction. -/
theorem lexStep_auxiliary_assignment_satisfies (a : Nat → Bool)
    (pref x y same : Nat) (hp0 : 0 < pref) (hx0 : 0 < x)
    (hy0 : 0 < y) (hs0 : 0 < same)
    (hp : a pref = true) (hx : a x = true) (hy : a y = false)
    (hs : a same = (a pref && (a x == a y))) :
    cnfValue a (lexStepClauses pref x y same) = true := by
  simp [cnfValue, clauseValue, lexStepClauses, hp, hx, hy, hs]

end Implications.C4PolarityLexEncoding

#print axioms Implications.C4PolarityLexEncoding.lexFreshIds_length
#print axioms Implications.C4PolarityLexEncoding.lexNext_eq
#print axioms Implications.C4PolarityLexEncoding.lexStep_auxiliary_assignment_satisfies
