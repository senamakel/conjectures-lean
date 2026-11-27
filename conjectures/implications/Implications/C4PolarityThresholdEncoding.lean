import Implications.C4PolarityCnfGates

/-!
DIMACS representation of the threshold-counter block emitted by
`encode_c4_polarity_42_cnf.py`.

Variable identifiers are one-based naturals and literals are signed integers.
The construction below allocates outputs in the same input-major,
threshold-minor order as the Python encoder.
-/

namespace Implications.C4PolarityThresholdEncoding

/-- Evaluate a signed DIMACS literal using a valuation of variable IDs. -/
def literalValue (assignment : Nat → Bool) (lit : Int) : Bool :=
  if lit < 0 then !assignment lit.natAbs else assignment lit.natAbs

/-- A clause is true when at least one of its signed literals is true. -/
def clauseValue (assignment : Nat → Bool) (clause : List Int) : Bool :=
  clause.any (literalValue assignment)

/-- A CNF is true when every clause is true. -/
def cnfValue (assignment : Nat → Bool) (clauses : List (List Int)) : Bool :=
  clauses.all (clauseValue assignment)

/-- The four exact DIMACS clauses emitted for one threshold gate. -/
def thresholdGateDimacs (above x below out : Int) : List (List Int) :=
  [[-above, out], [-x, -below, out], [-out, above, x], [-out, above, below]]

/-- The identifier for threshold `k` after processing input row `row`. The
threshold index is one-based, and each row receives a contiguous block. -/
def thresholdVar (nextVar limit row k : Nat) : Int :=
  Int.ofNat (nextVar + row * limit + k)

/-- Fresh output identifiers belonging to one input row, in increasing
threshold order. -/
def thresholdRowVars (nextVar limit : Nat) : List Int :=
  (List.range limit).map fun j => Int.ofNat (nextVar + j + 1)

/-- Fresh identifiers for the entire counter in input-major order. -/
def thresholdFreshVariables (nextVar limit inputCount : Nat) : List Int :=
  (List.range (inputCount * limit)).map fun j => Int.ofNat (nextVar + j + 1)

theorem thresholdFreshVariables_length (nextVar limit inputCount : Nat) :
    (thresholdFreshVariables nextVar limit inputCount).length = inputCount * limit := by
  simp [thresholdFreshVariables]

theorem thresholdFreshVariables_gt_base {nextVar limit inputCount : Nat}
    {v : Int} (hv : v ∈ thresholdFreshVariables nextVar limit inputCount) :
    Int.ofNat nextVar < v := by
  simp only [thresholdFreshVariables, List.mem_map, List.mem_range] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  norm_cast
  omega

theorem thresholdVar_gt_base {nextVar limit row k : Nat} (hk : 0 < k) :
    Int.ofNat nextVar < thresholdVar nextVar limit row k := by
  simp [thresholdVar]
  norm_cast
  omega

/-- The four-clause DIMACS gate agrees with the Boolean recurrence when all
four input and output literals are nonzero. -/
theorem thresholdGateDimacs_iff (assignment : Nat → Bool)
    (above x below out : Int)
    (ha : above ≠ 0) (hx : x ≠ 0) (hb : below ≠ 0) (ho : out ≠ 0) :
    cnfValue assignment (thresholdGateDimacs above x below out) = true ↔
      literalValue assignment out =
        (literalValue assignment above ||
          (literalValue assignment x && literalValue assignment below)) := by
  have hneg : ∀ lit : Int, lit ≠ 0 →
      literalValue assignment (-lit) = !literalValue assignment lit := by
    intro lit hlit
    by_cases hlt : lit < 0
    · have hpos : ¬ -lit < 0 := by omega
      simp [literalValue, hlt, hpos, Int.natAbs_neg]
    · have hpos : 0 < lit := by omega
      have hneglt : -lit < 0 := by omega
      simp [literalValue, hlt, hpos, hneglt, Int.natAbs_neg]
  have hgate := Implications.C4PolarityCnfGates.threshold_gate_iff
    (literalValue assignment above) (literalValue assignment x)
    (literalValue assignment below) (literalValue assignment out)
  simpa [Implications.C4PolarityCnfGates.thresholdGateClauses,
    Implications.C4PolarityCnfGates.clauseSat, cnfValue, thresholdGateDimacs,
    clauseValue, hneg above ha, hneg x hx, hneg below hb, hneg out ho] using hgate

/-- Build the clauses for one row, zipping `previous[k]`,
`previous[k - 1]`, and the newly allocated output. -/
def thresholdRowClauses (x : Int) (previous outputs : List Int) : List (List Int) :=
  ((previous.drop 1).zip (previous.take outputs.length)).zip outputs |>.flatMap
    (fun (ab, out) => thresholdGateDimacs ab.1 x ab.2 out)

/-- Recursively append one row of threshold gates per input. The state list
contains the literal for thresholds `0` through `limit`; threshold zero is
the distinguished true literal. -/
def thresholdBuildAux (limit : Nat) (trueLit : Int) :
    Nat → List Int → List Int → List (List Int) × List Int
  | _, [], previous => ([], previous)
  | nextVar, x :: xs, previous =>
      let outputs := [trueLit] ++ thresholdRowVars nextVar limit
      let row := thresholdRowClauses x previous (outputs.drop 1)
      let (rest, finalRow) :=
        thresholdBuildAux limit trueLit (nextVar + limit) xs outputs
      (row ++ rest, finalRow)

/-- The initial state and all gate clauses for a threshold counter. -/
def thresholdBuild (trueLit : Int) (nextVar limit : Nat) (inputs : List Int) :
    List (List Int) × List Int :=
  thresholdBuildAux limit trueLit nextVar inputs
    ([trueLit] ++ List.replicate limit (-trueLit))

/-- Unit clauses selecting thresholds 15 and not 16, as in the deletion
counter emitted by the encoder. -/
def deletionCounterBoundClauses (count : List Int) : List (List Int) :=
  [[count[15]!], [-count[16]!]]

/-- Unit clause requiring at least 34 score inputs. -/
def scoreCounterBoundClause (count : List Int) : List (List Int) :=
  [[count[34]!]]

theorem deletionCounterFreshCount :
    (thresholdFreshVariables 58 16 57).length = 912 := by
  norm_num [thresholdFreshVariables]

theorem scoreCounterFreshCount :
    (thresholdFreshVariables 970 34 232).length = 7888 := by
  norm_num [thresholdFreshVariables]

theorem deletionCounterLastThresholds :
    thresholdVar 58 16 56 15 = 969 ∧ thresholdVar 58 16 56 16 = 970 := by
  norm_num [thresholdVar]

theorem scoreCounterLastThreshold :
    thresholdVar 970 34 231 34 = 8858 := by
  norm_num [thresholdVar]

end Implications.C4PolarityThresholdEncoding

#print axioms Implications.C4PolarityThresholdEncoding.thresholdGateDimacs_iff
#print axioms Implications.C4PolarityThresholdEncoding.deletionCounterFreshCount
#print axioms Implications.C4PolarityThresholdEncoding.scoreCounterFreshCount
