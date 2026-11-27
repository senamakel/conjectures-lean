import Mathlib
import Implications.C4PolarityCnfGates
import Implications.C4PolarityThresholdEncoding

/-!
# DIMACS encoding of polarity lexicographic constraints

This module mirrors `Cnf.lex_at_least` in
`scripts/encode_c4_polarity_42_cnf.py`. Positions with the same DIMACS variable
are skipped without allocating a prefix variable, as in the Python encoder.
-/

namespace Implications.C4PolarityLexEncoding

open Implications.C4PolarityCnfGates
open Implications.C4PolarityThresholdEncoding

private def pos (v : Nat) : Int := Int.ofNat v
private def neg (v : Nat) : Int := Int.negOfNat v

@[simp] private theorem literalValue_pos (a : Nat → Bool) (v : Nat) (_hv : 0 < v) :
    literalValue a (pos v) = a v := by
  simp [literalValue, pos]

@[simp] private theorem literalValue_neg (a : Nat → Bool) (v : Nat) (hv : 0 < v) :
    literalValue a (neg v) = !a v := by
  change literalValue a (Int.negOfNat v) = !a v
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

/-- The permuted deletion-vector variables, using the permutation's indices as
the Python list comprehension does. Valid permutations have in-range indices. -/
def permutationVariables (deleted permutation : List Nat) : List Nat :=
  permutation.map fun i => deleted[i]!

/-- Concatenate the exact lex clauses for every permutation, threading the
fresh-variable counter across comparisons as the encoder does. -/
def orbitLexClauses (truth next : Nat) (deleted : List Nat) :
    List (List Nat) → List (List Int)
  | [] => []
  | permutation :: rest =>
      let image := permutationVariables deleted permutation
      lexClauses truth next deleted image ++
        orbitLexClauses truth (lexNext next deleted image) deleted rest

/-- Final unused variable after all lex comparisons in an orbit list. -/
def orbitLexNext (next : Nat) (deleted : List Nat) : List (List Nat) → Nat
  | [] => next
  | permutation :: rest =>
      let image := permutationVariables deleted permutation
      orbitLexNext (lexNext next deleted image) deleted rest

/-- Number of non-skipped positions over a list of permutations. -/
def orbitLexFreshCount (deleted : List Nat) : List (List Nat) → Nat
  | [] => 0
  | permutation :: rest =>
      (lexFreshIds 0 deleted (permutationVariables deleted permutation)).length +
        orbitLexFreshCount deleted rest

theorem orbitLexNext_eq (next : Nat) (deleted : List Nat) (permutations : List (List Nat)) :
    orbitLexNext next deleted permutations = next + orbitLexFreshCount deleted permutations := by
  induction permutations generalizing next with
  | nil => simp [orbitLexNext, orbitLexFreshCount]
  | cons permutation rest ih =>
      simp only [orbitLexNext, orbitLexFreshCount]
      rw [ih]
      rw [lexNext_eq]
      simp_rw [lexFreshIds_length]
      omega

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
    (hguard : (!a pref || a x || !a y) = true)
    (hs : a same = (a pref && (a x == a y))) :
    cnfValue a (lexStepClauses pref x y same) = true := by
  simp only [cnfValue, List.all_cons, List.all_nil, clauseValue, List.any_cons,
    List.any_nil, lexStepClauses]
  simp only [literalValue_neg a pref hp0, literalValue_neg a x hx0,
    literalValue_neg a y hy0, literalValue_neg a same hs0,
    literalValue_pos a pref hp0, literalValue_pos a x hx0,
    literalValue_pos a y hy0, literalValue_pos a same hs0]
  cases hp : a pref <;> cases hx : a x <;> cases hy : a y <;>
    simp_all [pos, hguard, hs]

/-- A satisfying assignment to the comparison clauses extends the input
assignment by setting the fresh prefix variable to the equality-prefix value. -/
theorem lexStep_extension (a : Nat → Bool) (pref x y same : Nat)
    (hp0 : 0 < pref) (hx0 : 0 < x) (hy0 : 0 < y) (hs0 : 0 < same)
    (hguard : (!a pref || a x || !a y) = true)
    (hps : pref ≠ same) (hxs : x ≠ same) (hys : y ≠ same) :
    ∃ b : Nat → Bool, (∀ n, n ≠ same → b n = a n) ∧
      b same = (a pref && (a x == a y)) ∧
      cnfValue b (lexStepClauses pref x y same) = true := by
  let b := Function.update a same (a pref && (a x == a y))
  have hbp : b pref = a pref := by simp [b, Function.update, hps]
  have hbx : b x = a x := by simp [b, Function.update, hxs]
  have hby : b y = a y := by simp [b, Function.update, hys]
  have hguardB : (!b pref || b x || !b y) = true := by
    simpa [hbp, hbx, hby] using hguard
  have hsame : b same = (a pref && (a x == a y)) := by
    simp [b, Function.update]
  refine ⟨b, ?_, hsame, ?_⟩
  · intro n hns
    simp [b, Function.update, hns]
  · rw [lexStep_auxiliary_assignment_satisfies b pref x y same hp0 hx0 hy0 hs0]
    · exact hguardB
    · simpa [hbp, hbx, hby] using hsame

end Implications.C4PolarityLexEncoding

#print axioms Implications.C4PolarityLexEncoding.lexFreshIds_length
#print axioms Implications.C4PolarityLexEncoding.lexNext_eq
#print axioms Implications.C4PolarityLexEncoding.orbitLexNext_eq
#print axioms Implications.C4PolarityLexEncoding.lexStep_auxiliary_assignment_satisfies
#print axioms Implications.C4PolarityLexEncoding.lexStep_extension
