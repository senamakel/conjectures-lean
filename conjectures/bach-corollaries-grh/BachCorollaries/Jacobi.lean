import BachCorollaries.Statement

/-!
# An executable Jacobi symbol

`jacobiCalc a b` is the usual binary algorithm (reduce `a` mod `b`, pull out factors of `2` with
the second supplement, swap with quadratic reciprocity). `jacobiCalc_eq` proves that it equals
Mathlib's `jacobiSym a b` for every odd `b`, so the test in `BachCorollaries/Test.lean` can use it
without factoring `b`.
-/

namespace BachCorollaries

/-- The Jacobi symbol `(a/b)`, computed by the binary algorithm. Correct for odd `b`. -/
def jacobiCalc (a b : ℕ) : ℤ :=
  if b ≤ 1 then 1
  else if a % b = 0 then 0
  else if a % b % 2 = 0 then
    let x := jacobiCalc (a % b / 2) b
    if b % 8 = 3 ∨ b % 8 = 5 then -x else x
  else
    let x := jacobiCalc (b % (a % b)) (a % b)
    if a % b % 4 = 3 ∧ b % 4 = 3 then -x else x
termination_by (b, a)
decreasing_by
  · exact Prod.Lex.right _ (lt_of_lt_of_le (Nat.div_lt_self (by omega) one_lt_two) (Nat.mod_le a b))
  · exact Prod.Lex.left _ _ (Nat.mod_lt a (by omega))

theorem jacobiCalc_eq (a b : ℕ) (hb : Odd b) : jacobiCalc a b = jacobiSym a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ihb =>
  induction a using Nat.strong_induction_on with
  | _ a iha =>
  have hb2 : b % 2 = 1 := Nat.odd_iff.mp hb
  have hmod : jacobiSym (a : ℤ) b = jacobiSym ((a % b : ℕ) : ℤ) b := by
    rw [Int.natCast_mod, ← jacobiSym.mod_left]
  rw [jacobiCalc]
  split_ifs with h1 h0 he hc hc
  · have : b = 1 := by omega
    rw [this, jacobiSym.one_right]
  · rw [hmod, h0, Nat.cast_zero, jacobiSym.zero_left (by omega)]
  · rw [iha _ (lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero h0) one_lt_two)
      (Nat.mod_le a b)), hmod,
      ← jacobiSym.even_odd (a := ((a % b : ℕ) : ℤ)) (b := b) (by omega) hb2, if_pos hc,
      Int.natCast_div, Nat.cast_ofNat]
  · rw [iha _ (lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero h0) one_lt_two)
      (Nat.mod_le a b)), hmod,
      ← jacobiSym.even_odd (a := ((a % b : ℕ) : ℤ)) (b := b) (by omega) hb2, if_neg hc,
      Int.natCast_div, Nat.cast_ofNat]
  · have hr : Odd (a % b) := Nat.odd_iff.mpr (by omega)
    rw [ihb _ (Nat.mod_lt a (by omega)) _ hr, hmod,
      ← jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp hr) hb2, if_pos hc,
      Int.natCast_mod, ← jacobiSym.mod_left]
  · have hr : Odd (a % b) := Nat.odd_iff.mpr (by omega)
    rw [ihb _ (Nat.mod_lt a (by omega)) _ hr, hmod,
      ← jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp hr) hb2, if_neg hc,
      Int.natCast_mod, ← jacobiSym.mod_left]

end BachCorollaries
