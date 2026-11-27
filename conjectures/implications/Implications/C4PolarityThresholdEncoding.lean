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
  match lit with
  | .ofNat n => assignment n
  | .negSucc n => !assignment (n + 1)

/-- A clause is true when at least one of its signed literals is true. -/
def clauseValue (assignment : Nat → Bool) (clause : List Int) : Bool :=
  clause.any (literalValue assignment)

/-- A CNF is true when every clause is true. -/
def cnfValue (assignment : Nat → Bool) (clauses : List (List Int)) : Bool :=
  clauses.all (clauseValue assignment)

/-- Extend an assignment by setting one fresh DIMACS variable. -/
def extendVariable (assignment : Nat → Bool) (varId : Nat) (value : Bool) : Nat → Bool :=
  fun v => if v = varId then value else assignment v

theorem literalValue_extendVariable_of_ne (assignment : Nat → Bool)
    (varId : Nat) (value : Bool) (lit : Int)
    (h : lit.natAbs ≠ varId) :
    literalValue (extendVariable assignment varId value) lit =
      literalValue assignment lit := by
  cases lit <;> simp_all [literalValue, extendVariable]

theorem literalValue_extendVariable_self (assignment : Nat → Bool)
    (varId : Nat) (value : Bool) :
    literalValue (extendVariable assignment varId value) (Int.ofNat varId) = value := by
  simp [literalValue, extendVariable]

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

theorem thresholdFreshVariables_nodup (nextVar limit inputCount : Nat) :
    (thresholdFreshVariables nextVar limit inputCount).Nodup := by
  apply List.Nodup.map
    (f := fun j : Nat => Int.ofNat (nextVar + j + 1))
  · intro i j hij
    change Int.ofNat (nextVar + i + 1) = Int.ofNat (nextVar + j + 1) at hij
    have hNat : nextVar + i + 1 = nextVar + j + 1 := Int.ofNat.inj hij
    omega
  · exact List.nodup_range

theorem thresholdFreshVariables_gt_base {nextVar limit inputCount : Nat}
    {v : Int} (hv : v ∈ thresholdFreshVariables nextVar limit inputCount) :
    Int.ofNat nextVar < v := by
  simp only [thresholdFreshVariables, List.mem_map, List.mem_range] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  have hNat : nextVar < nextVar + j + 1 := by omega
  exact Int.ofNat_lt.mpr hNat

theorem thresholdVar_gt_base {nextVar limit row k : Nat} (hk : 0 < k) :
    Int.ofNat nextVar < thresholdVar nextVar limit row k := by
  have hNat : nextVar < nextVar + row * limit + k := by omega
  change Int.ofNat nextVar < Int.ofNat (nextVar + row * limit + k)
  exact Int.ofNat_lt.mpr hNat

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
    cases lit with
    | ofNat n =>
        cases n with
        | zero => contradiction
        | succ n => rfl
    | negSucc n =>
        have hcast : (Int.ofNat n : Int) + 1 = Int.ofNat (n + 1) := by
          rfl
        change literalValue assignment (Int.ofNat n + 1) =
          !literalValue assignment (Int.negSucc n)
        rw [hcast]
        simp [literalValue]
  have hgate := Implications.C4PolarityCnfGates.threshold_gate_iff
    (literalValue assignment above) (literalValue assignment x)
    (literalValue assignment below) (literalValue assignment out)
  simpa [Implications.C4PolarityCnfGates.thresholdGateClauses,
    Implications.C4PolarityCnfGates.clauseSat, cnfValue, thresholdGateDimacs,
    clauseValue, and_assoc, hneg above ha, hneg x hx, hneg below hb, hneg out ho] using hgate

/-- Any threshold gate can be satisfied by extending the assignment at its
fresh output variable with the Boolean recurrence value. -/
theorem thresholdGateDimacs_extend (assignment : Nat → Bool)
    (varId : Nat) (above x below : Int)
    (value : Bool) (hvar : 0 < varId)
    (hrec : value =
      (literalValue assignment above ||
        (literalValue assignment x && literalValue assignment below)))
    (ha : above ≠ 0) (hx : x ≠ 0) (hb : below ≠ 0)
    (habove : above.natAbs ≠ varId)
    (hxFresh : x.natAbs ≠ varId)
    (hbelow : below.natAbs ≠ varId) :
    cnfValue (extendVariable assignment varId value)
      (thresholdGateDimacs above x below (Int.ofNat varId)) = true := by
  have hpos : (0 : Int) < Int.ofNat varId := by
    cases varId with
    | zero => omega
    | succ n => simp
  have hout : Int.ofNat varId ≠ 0 := ne_of_gt hpos
  apply (thresholdGateDimacs_iff (extendVariable assignment varId value)
    above x below (Int.ofNat varId) ha hx hb hout).2
  rw [literalValue_extendVariable_self]
  simp only [literalValue_extendVariable_of_ne _ _ _ _ habove,
    literalValue_extendVariable_of_ne _ _ _ _ hxFresh,
    literalValue_extendVariable_of_ne _ _ _ _ hbelow]
  exact hrec

/-- Build the clauses for one row, zipping `previous[k]`,
`previous[k - 1]`, and the newly allocated output. -/
def thresholdRowClauses (x : Int) (previous outputs : List Int) : List (List Int) :=
  ((previous.drop 1).zip (previous.take outputs.length)).zip outputs |>.flatMap
    (fun (ab, out) => thresholdGateDimacs ab.1 x ab.2 out)

theorem thresholdRowClauses_length (x : Int) (previous outputs : List Int)
    (hprev : previous.length = outputs.length + 1) :
    (thresholdRowClauses x previous outputs).length = 4 * outputs.length := by
  simp [thresholdRowClauses, thresholdGateDimacs, List.length_flatMap,
    List.sum_map_mul_right, hprev]

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
#print axioms Implications.C4PolarityThresholdEncoding.thresholdGateDimacs_extend
#print axioms Implications.C4PolarityThresholdEncoding.thresholdRowClauses_length
#print axioms Implications.C4PolarityThresholdEncoding.deletionCounterFreshCount
#print axioms Implications.C4PolarityThresholdEncoding.scoreCounterFreshCount
