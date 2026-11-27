import Implications.C4PolarityCnfGates

/-! Correctness of Boolean threshold rows and the encoder's final unit tests. -/

namespace Implications.C4PolarityCounterSemantics

open C4PolarityCnfGates

/-- The recurrence determines every in-range cell, including the zero column
that is supplied by the encoder's distinguished true variable. -/
theorem counter_cell_eq_atLeast
    (inputs : List Bool) (width : Nat) (cell : Nat → Nat → Bool)
    (hzero : ∀ r ≤ inputs.length, cell r 0 = true)
    (hinit : ∀ k, 0 < k → k ≤ width → cell 0 k = false)
    (hstep : ∀ r : Nat, ∀ hr : r < inputs.length, ∀ k,
      0 < k → k ≤ width →
      cell (r + 1) k = (cell r k || (inputs[r] && cell r (k - 1)))) :
    ∀ r ≤ inputs.length, ∀ k ≤ width, cell r k = atLeast k (inputs.take r) := by
  intro r
  induction r with
  | zero =>
    intro _ k hk
    cases k with
    | zero => simp [atLeast, hzero]
    | succ k => simpa [atLeast] using hinit (k + 1) (by omega) hk
  | succ r ih =>
    intro hr k hk
    cases k with
    | zero => simp [atLeast, hzero _ hr]
    | succ k =>
      have hlt : r < inputs.length := by omega
      have hle : r ≤ inputs.length := hlt.le
      rw [hstep r hlt (k + 1) (by omega) hk,
        ih hle (k + 1) hk, ih hle (k + 1 - 1) (by omega),
        List.take_succ_eq_append_getElem hlt, atLeast_append_singleton]

/-- The two deletion-counter units require exactly fifteen true input bits. -/
theorem deletion_units_iff (inputs : List Bool) :
    (atLeast 15 inputs = true ∧ atLeast 16 inputs = false) ↔
      inputs.count true = 15 := by
  simp only [atLeast, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

/-- The score unit requires at least thirty-four true input bits. -/
theorem score_unit_iff (inputs : List Bool) :
    atLeast 34 inputs = true ↔ 34 ≤ inputs.count true := by
  simp [atLeast]

end Implications.C4PolarityCounterSemantics

#print axioms Implications.C4PolarityCounterSemantics.counter_cell_eq_atLeast
