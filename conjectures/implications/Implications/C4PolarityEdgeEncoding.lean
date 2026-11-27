import Implications.C4PolarityDimacs
import Implications.C4PolarityCnfGates

/-!
The edge variables in the polarity encoder follow the 57 deletion bits and
their 16-column counter. Extending an assignment on this fresh interval
satisfies every edge gate without changing earlier values.
-/

namespace Implications.C4PolarityEdgeEncoding

open C4PolarityDimacs C4PolarityCnfGates

/-- The distinguished true literal has ID 1, followed by the deletion bits. -/
def deletionId (i : Fin 57) : Nat := i.val + 2

/-- Last ID allocated by the deletion counter. -/
def deletionCounterEnd : Nat := 1 + 57 + 57 * 16

/-- ID for the edge in position `k` of the encoder's orthogonal-pair list. -/
def edgeId (k : Nat) : Nat := deletionCounterEnd + k + 1

/-- The three clauses emitted together for one edge variable. -/
def edgeClauses (k : Nat) (p : Fin 57 × Fin 57) : List (List Int) :=
  let e : Int := edgeId k
  let x : Int := deletionId p.1
  let y : Int := deletionId p.2
  [[-e, x], [-e, y], [e, -x, -y]]

/-- Set the edge outputs on their allocated interval, preserving all other
values in the assignment. -/
def extendEdges (base : Nat → Bool) (pairs : List (Fin 57 × Fin 57)) (v : Nat) : Bool :=
  if deletionCounterEnd < v then
    match pairs[v - (deletionCounterEnd + 1)]? with
    | some (i, j) => base (deletionId i) && base (deletionId j)
    | none => base v
  else
    base v

theorem extendEdges_preserves_counter (base : Nat → Bool) (pairs : List (Fin 57 × Fin 57))
    (v : Nat) (hv : v ≤ deletionCounterEnd) : extendEdges base pairs v = base v := by
  simp [extendEdges, Nat.not_lt.mpr hv]

theorem extendEdges_at_edge (base : Nat → Bool) (pairs : List (Fin 57 × Fin 57))
    (k : Nat) (hk : k < pairs.length) :
    extendEdges base pairs (edgeId k) =
      (base (deletionId pairs[k].1) && base (deletionId pairs[k].2)) := by
  have hgt : deletionCounterEnd < edgeId k := by unfold edgeId; omega
  have hindex : edgeId k - (deletionCounterEnd + 1) = k := by unfold edgeId; omega
  simp [extendEdges, hgt, hindex, List.getElem?_eq_getElem hk]

theorem extendEdges_at_deletion (base : Nat → Bool) (pairs : List (Fin 57 × Fin 57))
    (i : Fin 57) : extendEdges base pairs (deletionId i) = base (deletionId i) := by
  apply extendEdges_preserves_counter
  have hi := i.isLt
  unfold deletionId deletionCounterEnd
  omega

private theorem literal_pos (a : Nat → Bool) (v : Nat) (hv : 0 < v) :
    evalLiteral a (v : Int) = a v := by
  simp [evalLiteral,hv]

private theorem literal_neg (a : Nat → Bool) (v : Nat) (hv : 0 < v) :
    evalLiteral a (-(v : Int)) = !(a v) := by
  have h : ¬ (v : Int) < 0 := by omega
  simp [evalLiteral,h]

/-- All three exact signed clauses hold for each edge output in the extension. -/
theorem edgeClauses_satisfied (base : Nat → Bool) (pairs : List (Fin 57 × Fin 57))
    (k : Nat) (hk : k < pairs.length) :
    (edgeClauses k pairs[k]).all (fun clause => clause.any (evalLiteral (extendEdges base pairs))) =
      true := by
  let a := extendEdges base pairs
  have he : 0 < edgeId k := by unfold edgeId; omega
  have hd (i : Fin 57) : 0 < deletionId i := by unfold deletionId; omega
  have hgate := (edge_and_iff (a (edgeId k)) (a (deletionId pairs[k].1))
    (a (deletionId pairs[k].2))).mpr (by
      simp [a, extendEdges_at_edge base pairs k hk, extendEdges_at_deletion])
  simpa [a, edgeAndClauses, clauseSat, edgeClauses, and_assoc, literal_pos _ _ he, literal_neg _ _ he,
    literal_pos _ _ (hd _), literal_neg _ _ (hd _)] using hgate

/-- The entire edge-clause stage, in increasing variable-allocation order. -/
def edgeFormula (pairs : List (Fin 57 × Fin 57)) : List (List Int) :=
  (List.finRange pairs.length).flatMap fun k => edgeClauses k.val pairs[k]

theorem edgeFormula_satisfied (base : Nat → Bool) (pairs : List (Fin 57 × Fin 57)) :
    (edgeFormula pairs).all (fun clause => clause.any (evalLiteral (extendEdges base pairs))) =
      true := by
  rw [edgeFormula, List.all_flatMap]
  exact List.all_eq_true.mpr (fun k _ => edgeClauses_satisfied base pairs k.val k.isLt)

/-- After the 224 edge variables, the length-232, width-34 score counter
allocates its final output at DIMACS ID 9082. -/
theorem scoreCounterLastId : edgeId 223 + 232 * 34 = 9082 := rfl

end Implications.C4PolarityEdgeEncoding

#print axioms Implications.C4PolarityEdgeEncoding.edgeClauses_satisfied
#print axioms Implications.C4PolarityEdgeEncoding.scoreCounterLastId
#print axioms Implications.C4PolarityEdgeEncoding.edgeFormula_satisfied
