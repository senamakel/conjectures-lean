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

/-- Unit clause that fixes the encoder's distinguished variable to true. -/
def thresholdTrueUnit (trueLit : Int) : List (List Int) := [[trueLit]]

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

theorem thresholdVar_mem_fresh {nextVar limit inputCount row k : Nat}
    (hrow : row < inputCount) (hk : 0 < k) (hkLimit : k ≤ limit) :
    thresholdVar nextVar limit row k ∈
      thresholdFreshVariables nextVar limit inputCount := by
  unfold thresholdFreshVariables
  apply List.mem_map.mpr
  refine ⟨row * limit + k - 1, List.mem_range.mpr ?_, ?_⟩
  · have hrowMul : row * limit < inputCount * limit :=
      Nat.mul_lt_mul_of_pos_right hrow (by omega)
    have hk' : k - 1 < limit := by omega
    have hassoc : row * limit + k - 1 = row * limit + (k - 1) := by omega
    have hbound : (row + 1) * limit ≤ inputCount * limit := by
      exact Nat.mul_le_mul_right limit (Nat.succ_le_of_lt hrow)
    have hstep : row * limit + (k - 1) < (row + 1) * limit := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left hk' (row * limit)
    rw [hassoc]
    exact lt_of_lt_of_le hstep hbound
  · have hassoc : row * limit + k - 1 = row * limit + (k - 1) := by omega
    have hNat : nextVar + (row * limit + (k - 1)) + 1 =
        nextVar + row * limit + k := by omega
    simpa [thresholdVar, hassoc] using congrArg Int.ofNat hNat

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

/-- One threshold gate with its allocated positive output identifier. -/
structure ThresholdGate where
  output : Nat
  above : Int
  input : Int
  below : Int
  deriving Repr

/-- The Boolean value assigned to a gate output by its recurrence. -/
def thresholdGateValue (assignment : Nat → Bool) (gate : ThresholdGate) : Bool :=
  literalValue assignment gate.above ||
    (literalValue assignment gate.input && literalValue assignment gate.below)

/-- Extend an assignment at one gate output using its recurrence. -/
def extendThresholdGate (assignment : Nat → Bool) (gate : ThresholdGate) : Nat → Bool :=
  extendVariable assignment gate.output (thresholdGateValue assignment gate)

/-- Extend an assignment through gates in allocation order. -/
def extendThresholdGates (assignment : Nat → Bool) : List ThresholdGate → Nat → Bool
  | [] => assignment
  | gate :: gates => extendThresholdGates (extendThresholdGate assignment gate) gates

/-- Gates are ordered when each output is fresh from its inputs and every
later output is allocated after the current one. -/
def ThresholdGate.Ordered : List ThresholdGate → Prop
  | [] => True
  | gate :: gates =>
      0 < gate.output ∧
      gate.above ≠ 0 ∧ gate.input ≠ 0 ∧ gate.below ≠ 0 ∧
      gate.above.natAbs < gate.output ∧
      gate.input.natAbs < gate.output ∧
      gate.below.natAbs < gate.output ∧
      (∀ later ∈ gates, gate.output < later.output) ∧
      Ordered gates

theorem extendThresholdGates_preserves (assignment : Nat → Bool)
    (gates : List ThresholdGate) (lit : Int)
    (hfresh : ∀ gate ∈ gates, lit.natAbs ≠ gate.output) :
    literalValue (extendThresholdGates assignment gates) lit =
      literalValue assignment lit := by
  induction gates generalizing assignment with
  | nil => rfl
  | cons gate gates ih =>
      simp only [extendThresholdGates]
      rw [ih]
      · exact literalValue_extendVariable_of_ne assignment gate.output
          (thresholdGateValue assignment gate) lit (hfresh gate (by simp))
      · intro later hlater
        exact hfresh later (by simp [hlater])

/-- Every gate in an ordered chain is satisfied after the chain assigns all
fresh output variables in order. -/
theorem thresholdGateList_satisfies (assignment : Nat → Bool)
    (gates : List ThresholdGate) (hordered : ThresholdGate.Ordered gates) :
    ∀ gate ∈ gates,
      cnfValue (extendThresholdGates assignment gates)
        (thresholdGateDimacs gate.above gate.input gate.below (Int.ofNat gate.output)) = true := by
  induction gates generalizing assignment with
  | nil => simp
  | cons gate gates ih =>
      rcases hordered with ⟨hpos, hAboveNe, hInputNe, hBelowNe,
        hAboveLt, hInputLt, hBelowLt, hLater, hTail⟩
      intro current hmem
      let afterGate := extendThresholdGate assignment gate
      let finalAssignment := extendThresholdGates afterGate gates
      cases hmem with
      | head =>
        have hAbovePres : literalValue finalAssignment gate.above =
            literalValue assignment gate.above := by
          change literalValue (extendThresholdGates afterGate gates) gate.above = _
          calc
            _ = literalValue afterGate gate.above :=
              extendThresholdGates_preserves afterGate gates gate.above (by
                intro later hlaterMem
                have hlt := hLater later hlaterMem
                omega)
            _ = literalValue assignment gate.above := by
              exact literalValue_extendVariable_of_ne assignment gate.output
                (thresholdGateValue assignment gate) gate.above (by omega)
        have hInputPres : literalValue finalAssignment gate.input =
            literalValue assignment gate.input := by
          change literalValue (extendThresholdGates afterGate gates) gate.input = _
          calc
            _ = literalValue afterGate gate.input :=
              extendThresholdGates_preserves afterGate gates gate.input (by
                intro later hlaterMem
                have hlt := hLater later hlaterMem
                omega)
            _ = literalValue assignment gate.input := by
              exact literalValue_extendVariable_of_ne assignment gate.output
                (thresholdGateValue assignment gate) gate.input (by omega)
        have hBelowPres : literalValue finalAssignment gate.below =
            literalValue assignment gate.below := by
          change literalValue (extendThresholdGates afterGate gates) gate.below = _
          calc
            _ = literalValue afterGate gate.below :=
              extendThresholdGates_preserves afterGate gates gate.below (by
                intro later hlaterMem
                have hlt := hLater later hlaterMem
                omega)
            _ = literalValue assignment gate.below := by
              exact literalValue_extendVariable_of_ne assignment gate.output
                (thresholdGateValue assignment gate) gate.below (by omega)
        have hOutputPres : literalValue finalAssignment (Int.ofNat gate.output) =
            thresholdGateValue assignment gate := by
          change literalValue (extendThresholdGates afterGate gates)
            (Int.ofNat gate.output) = _
          calc
            _ = literalValue afterGate (Int.ofNat gate.output) := by
              apply extendThresholdGates_preserves
              intro later hlaterMem
              have hlt := hLater later hlaterMem
              have habs : (Int.ofNat gate.output).natAbs = gate.output := by simp
              rw [habs]
              omega
            _ = thresholdGateValue assignment gate := by
              change literalValue
                (extendVariable assignment gate.output (thresholdGateValue assignment gate))
                (Int.ofNat gate.output) = thresholdGateValue assignment gate
              exact literalValue_extendVariable_self assignment gate.output
                (thresholdGateValue assignment gate)
        have hOutputNe : Int.ofNat gate.output ≠ 0 := by
          intro hz
          have hnat : gate.output = 0 := Int.ofNat.inj (by simpa using hz)
          omega
        apply (thresholdGateDimacs_iff finalAssignment gate.above gate.input gate.below
          (Int.ofNat gate.output) hAboveNe hInputNe hBelowNe hOutputNe).2
        rw [hOutputPres, hAbovePres, hInputPres, hBelowPres]
        rfl
      | tail _ hmem =>
        exact ih afterGate hTail current hmem

/-- Build the clauses for one row, zipping `previous[k]`,
`previous[k - 1]`, and the newly allocated output. -/
def thresholdRowClauses (x : Int) (previous outputs : List Int) : List (List Int) :=
  ((previous.drop 1).zip (previous.take outputs.length)).zip outputs |>.flatMap
    (fun (ab, out) => thresholdGateDimacs ab.1 x ab.2 out)

/-- Gate records represented by the exact tuples zipped in one emitted row. -/
def thresholdRowGates (x : Int) (previous outputs : List Int) : List ThresholdGate :=
  ((previous.drop 1).zip (previous.take outputs.length)).zip outputs |>.map
    (fun (ab, out) => ⟨out.natAbs, ab.1, x, ab.2⟩)

/-- The row clauses are exactly the concatenation of the corresponding gate
clauses, when each output literal is the positive form of its variable. -/
theorem thresholdRowClauses_eq_gateClauses (x : Int) (previous outputs : List Int)
    (hout : ∀ out ∈ outputs, Int.ofNat out.natAbs = out) :
    thresholdRowClauses x previous outputs =
      (thresholdRowGates x previous outputs).flatMap
        (fun gate => thresholdGateDimacs gate.above gate.input gate.below
          (Int.ofNat gate.output)) := by
  simp [thresholdRowClauses, thresholdRowGates, thresholdGateDimacs, hout]

theorem thresholdRowClauses_length (x : Int) (previous outputs : List Int)
    (hprev : previous.length = outputs.length + 1) :
    (thresholdRowClauses x previous outputs).length = 4 * outputs.length := by
  simp [thresholdRowClauses, thresholdGateDimacs, List.length_flatMap,
    Nat.mul_comm, hprev]

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

/-- Output literals in the final row, including threshold zero, which is the
distinguished true literal. -/
def thresholdFinalRow (trueLit : Int) (nextVar limit row : Nat) : List Int :=
  [trueLit] ++ (List.range limit).map fun j => thresholdVar nextVar limit row (j + 1)

theorem deletionCounterFreshCount :
    (thresholdFreshVariables 58 16 57).length = 912 := by
  norm_num [thresholdFreshVariables]

theorem scoreCounterFreshCount :
    (thresholdFreshVariables 1194 34 232).length = 7888 := by
  norm_num [thresholdFreshVariables]

theorem deletionCounterLastThresholds :
    thresholdVar 58 16 56 15 = 969 ∧ thresholdVar 58 16 56 16 = 970 := by
  norm_num [thresholdVar]

theorem scoreCounterLastThreshold :
    thresholdVar 1194 34 231 34 = 9082 := by
  norm_num [thresholdVar]

theorem deletionCounterUnits_are_encoder_units :
    deletionCounterBoundClauses (thresholdFinalRow 1 58 16 56) = [[969], [-970]] := by
  norm_num [deletionCounterBoundClauses, thresholdFinalRow, thresholdVar]

theorem scoreCounterUnit_is_encoder_unit :
    scoreCounterBoundClause (thresholdFinalRow 1 1194 34 231) = [[9082]] := by
  norm_num [scoreCounterBoundClause, thresholdFinalRow, thresholdVar]

end Implications.C4PolarityThresholdEncoding

#print axioms Implications.C4PolarityThresholdEncoding.thresholdGateDimacs_iff
#print axioms Implications.C4PolarityThresholdEncoding.thresholdGateDimacs_extend
#print axioms Implications.C4PolarityThresholdEncoding.thresholdRowClauses_length
#print axioms Implications.C4PolarityThresholdEncoding.deletionCounterFreshCount
#print axioms Implications.C4PolarityThresholdEncoding.scoreCounterFreshCount
#print axioms Implications.C4PolarityThresholdEncoding.deletionCounterUnits_are_encoder_units
#print axioms Implications.C4PolarityThresholdEncoding.scoreCounterUnit_is_encoder_unit
