import Mathlib

/-!
Boolean semantics for the local gates emitted by
`scripts/encode_c4_polarity_42_cnf.py`.

These lemmas certify the threshold recurrence, edge indicator, and symmetry
prefix gates as predicates on assignments. They do not yet prove that the
whole graph encoding is equivalent to the generated CNF.
-/

namespace Implications.C4PolarityCnfGates

/-- A disjunction of signed Boolean literals, with `true` representing a
positive literal and `false` a negative literal. -/
def clauseSat (literals : List Bool) : Bool := literals.any id

/-- The four clauses emitted for one threshold recurrence gate. -/
def thresholdGateClauses (above x below out : Bool) : Bool :=
  clauseSat [!above, out] &&
    clauseSat [!x, !below, out] &&
    clauseSat [!out, above, x] &&
    clauseSat [!out, above, below]

theorem threshold_gate_iff (above x below out : Bool) :
    thresholdGateClauses above x below out = true ↔
      out = (above || (x && below)) := by
  cases above <;> cases x <;> cases below <;> cases out <;> decide

/-- The three clauses emitted for the conjunction indicator of an edge. -/
def edgeAndClauses (edge x y : Bool) : Bool :=
  clauseSat [!edge, x] && clauseSat [!edge, y] &&
    clauseSat [edge, !x, !y]

theorem edge_and_iff (edge x y : Bool) :
    edgeAndClauses edge x y = true ↔ edge = (x && y) := by
  cases edge <;> cases x <;> cases y <;> decide

/-- The five clauses defining one equality-prefix output in the symmetry
breaking comparator. -/
def prefixEqualityClauses (pref x y same : Bool) : Bool :=
  clauseSat [!same, pref] &&
    clauseSat [!same, !x, y] &&
    clauseSat [!same, x, !y] &&
    clauseSat [!pref, x, y, same] &&
    clauseSat [!pref, !x, !y, same]

theorem prefix_equality_iff (pref x y same : Bool) :
    prefixEqualityClauses pref x y same = true ↔
      same = (pref && (x == y)) := by
  cases pref <;> cases x <;> cases y <;> cases same <;> decide

/-- Whether at least `k` entries of a Boolean list are true. -/
def atLeast (k : Nat) (xs : List Bool) : Bool :=
  decide (k ≤ xs.count true)

/-- Appending a Boolean input updates the threshold counter by the recurrence
used by the encoder. -/
theorem atLeast_append_singleton (k : Nat) (xs : List Bool) (x : Bool) :
    atLeast k (xs ++ [x]) =
      (atLeast k xs || (x && atLeast (k - 1) xs)) := by
  cases x
  · simp [atLeast, List.count_append]
  · simp [atLeast, List.count_append]; omega

theorem atLeast_zero_nil : atLeast 0 [] = true := by
  simp [atLeast]

theorem atLeast_succ_nil (k : Nat) : atLeast (k + 1) [] = false := by
  simp [atLeast]

/-- The lexicographic `≥` predicate used by the symmetry-breaking clauses. -/
def lexAtLeast : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys =>
      if x == y then lexAtLeast xs ys else x && !y
  | _, _ => false

/-- Satisfaction of all comparison clauses, carrying the equality prefix. -/
def lexConstraint : Bool → List Bool → List Bool → Bool
  | _, [], [] => true
  | pref, x :: xs, y :: ys =>
      ((!pref) || x || !y) &&
        lexConstraint (pref && (x == y)) xs ys
  | _, _, _ => false

theorem lex_constraint_iff (xs ys : List Bool) (hlen : xs.length = ys.length) :
    lexConstraint true xs ys = lexAtLeast xs ys := by
  have hfalse : ∀ (xs ys : List Bool), xs.length = ys.length →
      lexConstraint false xs ys = true := by
    intro xs
    induction xs with
    | nil =>
        intro ys hlen
        cases ys <;> simp [lexConstraint] at hlen ⊢
    | cons x xs ih =>
        intro ys hlen
        cases ys with
        | nil => simp at hlen
        | cons y ys =>
            simp only [List.length_cons, Nat.succ.injEq] at hlen
            simp [lexConstraint, ih ys hlen]
  induction xs generalizing ys with
  | nil => cases ys <;> simp [lexConstraint, lexAtLeast] at hlen ⊢
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          cases x <;> cases y <;>
            simp [lexConstraint, lexAtLeast, ih ys hlen, hfalse xs ys hlen]

end Implications.C4PolarityCnfGates

#print axioms Implications.C4PolarityCnfGates.threshold_gate_iff
#print axioms Implications.C4PolarityCnfGates.edge_and_iff
#print axioms Implications.C4PolarityCnfGates.prefix_equality_iff
#print axioms Implications.C4PolarityCnfGates.atLeast_append_singleton
#print axioms Implications.C4PolarityCnfGates.lex_constraint_iff
