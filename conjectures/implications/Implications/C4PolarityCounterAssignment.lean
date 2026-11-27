import Implications.C4PolarityThresholdEncoding

/-! A valuation of the actual row-major output variable IDs of a counter. -/

namespace Implications.C4PolarityCounterAssignment

open C4PolarityThresholdEncoding C4PolarityCnfGates

/-- Assign a threshold value to every variable in the allocated interval.
Variables outside the interval retain their base value. -/
def valuation (a : Nat → Bool) (base width : Nat) (inputs : List Bool) (v : Nat) : Bool :=
  if base < v ∧ v ≤ base + inputs.length * width then
    let offset := v - (base + 1)
    atLeast (offset % width + 1) (inputs.take (offset / width + 1))
  else a v

theorem valuation_preserves (a : Nat → Bool) (base width : Nat) (inputs : List Bool)
    (v : Nat) (hv : v ≤ base) : valuation a base width inputs v = a v := by
  simp [valuation, Nat.not_lt.mpr hv]

theorem valuation_cell (a : Nat → Bool) (base width : Nat) (inputs : List Bool)
    (row k : Nat) (hr : row < inputs.length) (hk : 0 < k) (hw : k ≤ width) :
    literalValue (valuation a base width inputs) (thresholdVar base width row k) =
      atLeast k (inputs.take (row + 1)) := by
  have hwidth : 0 < width := by omega
  have hblock := Nat.mul_le_mul_right width (show row + 1 ≤ inputs.length by omega)
  rw [Nat.succ_mul] at hblock
  have hmem : base < base + row * width + k ∧
      base + row * width + k ≤ base + inputs.length * width := by omega
  have hoff : base + row * width + k - (base + 1) = row * width + (k - 1) := by omega
  have hsmall : k - 1 < width := by omega
  have hdiv : (row * width + (k - 1)) / width = row := by
    rw [Nat.mul_comm row width, Nat.mul_add_div hwidth, Nat.div_eq_of_lt hsmall, Nat.add_zero]
  have hmod : (row * width + (k - 1)) % width + 1 = k := by
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hsmall]
    omega
  simp only [thresholdVar, literalValue, valuation, ite_eq_left hmem, hoff, hdiv, hmod]

theorem valuation_preserves_literal (a : Nat → Bool) (base width : Nat) (inputs : List Bool)
    (l : Int) (hl : l.natAbs ≤ base) :
    literalValue (valuation a base width inputs) l = literalValue a l := by
  cases l with
  | ofNat n => exact valuation_preserves a base width inputs n hl
  | negSucc n =>
    change (!(valuation a base width inputs (n + 1))) = (!(a (n + 1)))
    rw [valuation_preserves a base width inputs (n + 1) hl]

/-- The literal for column `k` from before processing the input at row `r`.
Column zero always reads the true variable, while positive columns start false. -/
def previous (base width r k : Nat) : Int :=
  if k = 0 then 1 else if r = 0 then -1 else thresholdVar base width (r - 1) k

theorem previous_ne_zero (base width r k : Nat) : previous base width r k ≠ 0 := by
  unfold previous
  split
  · decide
  · rename_i hk
    split
    · decide
    · unfold thresholdVar
      change Int.ofNat _ ≠ Int.ofNat 0
      intro h
      have := Int.ofNat.inj h
      omega

theorem valuation_previous (a : Nat → Bool) (base width : Nat) (inputs : List Bool)
    (ha : a 1 = true) (hb : 1 ≤ base) (r k : Nat)
    (hr : r ≤ inputs.length) (hk : k ≤ width) :
    literalValue (valuation a base width inputs) (previous base width r k) =
      atLeast k (inputs.take r) := by
  have htrue := (valuation_preserves a base width inputs 1 hb).trans ha
  cases k with
  | zero => simpa [previous, literalValue, atLeast] using htrue
  | succ k =>
    cases r with
    | zero =>
      change (!valuation a base width inputs 1) = atLeast (k + 1) []
      simp [htrue, atLeast]
    | succ r =>
      simpa [previous] using valuation_cell a base width inputs r (k + 1)
        (by omega) (by omega) hk

/-- The direct valuation satisfies the exact four DIMACS clauses for any
numbered cell. Input literals lie in the pre-existing allocation. -/
theorem numbered_gate_satisfied
    (a : Nat → Bool) (base width : Nat) (inputs : List Int)
    (ha : a 1 = true) (hb : 1 ≤ base)
    (r : Nat) (hr : r < inputs.length) (k : Nat) (hk : 0 < k) (hw : k ≤ width)
    (hin : inputs[r] ≠ 0) (hbound : inputs[r].natAbs ≤ base) :
    cnfValue (valuation a base width (inputs.map (literalValue a)))
      (thresholdGateDimacs (previous base width r k) inputs[r]
        (previous base width r (k - 1)) (thresholdVar base width r k)) = true := by
  let bits := inputs.map (literalValue a)
  have hlen : bits.length = inputs.length := by simp [bits]
  have hr' : r < bits.length := by omega
  have hout : thresholdVar base width r k ≠ 0 := by
    unfold thresholdVar
    change Int.ofNat _ ≠ Int.ofNat 0
    intro h
    have := Int.ofNat.inj h
    omega
  apply (thresholdGateDimacs_iff _ _ _ _ _ (previous_ne_zero _ _ _ _) hin
    (previous_ne_zero _ _ _ _) hout).mpr
  rw [valuation_cell a base width bits r k hr' hk hw,
    valuation_previous a base width bits ha hb r k hr'.le hw,
    valuation_previous a base width bits ha hb r (k - 1) hr'.le (by omega),
    valuation_preserves_literal a base width bits inputs[r] hbound,
    List.take_succ_eq_append_getElem hr', atLeast_append_singleton]
  simp [bits]

/-- Concatenate the signed cells in the order used by the encoder. -/
def numberedCounter (base width : Nat) (inputs : List Int) : List (List Int) :=
  (List.finRange inputs.length).flatMap fun row =>
    (List.finRange width).flatMap fun col =>
      thresholdGateDimacs (previous base width row.val (col.val + 1)) inputs[row.val]
        (previous base width row.val col.val) (thresholdVar base width row.val (col.val + 1))

theorem numberedCounter_satisfied
    (a : Nat → Bool) (base width : Nat) (inputs : List Int)
    (ha : a 1 = true) (hb : 1 ≤ base)
    (hinputs : ∀ l ∈ inputs, l ≠ 0 ∧ l.natAbs ≤ base) :
    cnfValue (valuation a base width (inputs.map (literalValue a)))
      (numberedCounter base width inputs) = true := by
  unfold numberedCounter cnfValue
  simp only [List.all_flatMap, List.all_eq_true]
  intro row _ col _
  have h := hinputs inputs[row.val] (List.getElem_mem row.isLt)
  simpa only [Nat.add_sub_cancel, cnfValue, List.all_eq_true] using
    numbered_gate_satisfied a base width inputs ha hb row.val row.isLt
      (col.val + 1) (by omega) col.isLt h.1 h.2

/-- Variables beyond the last allocated ID also retain their input value. -/
theorem valuation_preserves_above (a : Nat → Bool) (base width : Nat) (inputs : List Bool)
    (v : Nat) (hv : base + inputs.length * width < v) :
    valuation a base width inputs v = a v := by
  simp [valuation, Nat.not_le.mpr hv]

/-- The concrete deletion counter has 57 rows of width 16. Its final two
signed unit clauses hold when exactly fifteen inputs are true. -/
theorem deletion_units_satisfied (a : Nat → Bool) (bits : List Bool)
    (hlen : bits.length = 57) (hcount : bits.count true = 15) :
    cnfValue (valuation a 58 16 bits) [[969], [-970]] = true := by
  have htake : bits.take 57 = bits := by rw [← hlen]; simp
  have h15 := valuation_cell a 58 16 bits 56 15 (by omega) (by decide) (by decide)
  have h16 := valuation_cell a 58 16 bits 56 16 (by omega) (by decide) (by decide)
  change valuation a 58 16 bits 969 = atLeast 15 (bits.take 57) at h15
  change valuation a 58 16 bits 970 = atLeast 16 (bits.take 57) at h16
  have h15' : valuation a 58 16 bits 969 = true := by
    simpa [htake, atLeast, hcount] using h15
  have h16' : valuation a 58 16 bits 970 = false := by
    simpa [htake, atLeast, hcount] using h16
  change ((valuation a 58 16 bits 969 || false) &&
    (((!valuation a 58 16 bits 970) || false) && true)) = true
  simp [h15', h16']

/-- The concrete score counter has 232 rows of width 34. Its final unit
clause holds when at least thirty-four inputs are true. -/
theorem score_unit_satisfied (a : Nat → Bool) (bits : List Bool)
    (hlen : bits.length = 232) (hcount : 34 ≤ bits.count true) :
    cnfValue (valuation a 1194 34 bits) [[9082]] = true := by
  have htake : bits.take 232 = bits := by rw [← hlen]; simp
  have h34 := valuation_cell a 1194 34 bits 231 34 (by omega) (by decide) (by decide)
  change valuation a 1194 34 bits 9082 = atLeast 34 (bits.take 232) at h34
  change ((valuation a 1194 34 bits 9082 || false) && true) = true
  simpa [htake, atLeast, hcount] using h34

end Implications.C4PolarityCounterAssignment

#print axioms Implications.C4PolarityCounterAssignment.valuation_cell
#print axioms Implications.C4PolarityCounterAssignment.numbered_gate_satisfied
#print axioms Implications.C4PolarityCounterAssignment.numberedCounter_satisfied
#print axioms Implications.C4PolarityCounterAssignment.deletion_units_satisfied
#print axioms Implications.C4PolarityCounterAssignment.score_unit_satisfied
