import Implications.WilfThreeCycleGlobal
import Implications.WilfReversal

/-! Checked stationary-maximum comparisons in reversed length-eight archive orientations. -/

namespace Implications.WilfStationaryMaxOrientations

open WilfMarked WilfPatternSwap WilfThreeCycleOrder WilfReversal

private theorem exactCount_eq_of_stationaryMax (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8) (m : Equiv.Perm (Fin 8))
    (hm : ∀ i : Fin 8, m i ≠ i → i = 1 ∨ i = 3 ∨ i = 4)
    (hm1 : m 1 ≠ 1)
    (hpq : p ∘ m = q) (hqp : q ∘ m.symm = p)
    (hcheckP : ∀ d, 1 ≤ d → d < 8 →
      (overlapCompatible p d = true ↔ d = 5 ∨ d = 7))
    (hcheckQ : ∀ d, 1 ≤ d → d < 8 →
      (overlapCompatible q d = true ↔ d = 5 ∨ d = 7))
    (hinjP : Function.Injective p)
    (hfixP : m 6 = 6)
    (hmaxP : ∀ i : Fin 8, i ≠ 6 → p i < p 6)
    (hsecondP : ∀ i : Fin 8, i ≠ 6 → i ≠ 5 → p i < p 5)
    (hcrossP : p 0 < p (m 1))
    (hinjQ : Function.Injective q)
    (hfixQ : m.symm 6 = 6)
    (hmaxQ : ∀ i : Fin 8, i ≠ 6 → q i < q 6)
    (hsecondQ : ∀ i : Fin 8, i ≠ 6 → i ≠ 5 → q i < q 5)
    (hcrossQ : q 0 < q (m.symm 1)) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet q) marks := by
  apply WilfThreeCycleGlobal.exactOccurrenceCount_eq_of_markedSwap
    n marks p q m hm hm1 hcheckP hcheckQ hpq hqp
  · intro f hf hn i j
    simpa only [← hpq, Function.comp_apply] using
      overlap_cycle_order p m hinjP hfixP hmaxP hsecondP hcrossP f hf hn i j
  · intro f hf hn i j
    simpa only [← hqp, Function.comp_apply] using
      overlap_cycle_order q m.symm hinjQ hfixQ hmaxQ hsecondQ hcrossQ f hf hn i j

private def swap14 : Equiv.Perm (Fin 8) := Equiv.swap 1 4
private def swap13 : Equiv.Perm (Fin 8) := Equiv.swap 1 3

private def pattern34265781 : Fin 8 → Fin 8 := ![2, 3, 1, 5, 4, 6, 7, 0]
private def pattern35264781 : Fin 8 → Fin 8 := ![2, 4, 1, 5, 3, 6, 7, 0]
private def pattern36254781 : Fin 8 → Fin 8 := ![2, 5, 1, 4, 3, 6, 7, 0]

private def pattern34165782 : Fin 8 → Fin 8 := ![2, 3, 0, 5, 4, 6, 7, 1]
private def pattern36154782 : Fin 8 → Fin 8 := ![2, 5, 0, 4, 3, 6, 7, 1]
private def pattern35164782 : Fin 8 → Fin 8 := ![2, 4, 0, 5, 3, 6, 7, 1]

private def pattern46352781 : Fin 8 → Fin 8 := ![3, 5, 2, 4, 1, 6, 7, 0]
private def pattern45362781 : Fin 8 → Fin 8 := ![3, 4, 2, 5, 1, 6, 7, 0]
private def pattern46253781 : Fin 8 → Fin 8 := ![3, 5, 1, 4, 2, 6, 7, 0]
private def pattern45263781 : Fin 8 → Fin 8 := ![3, 4, 1, 5, 2, 6, 7, 0]
private def pattern46351782 : Fin 8 → Fin 8 := ![3, 5, 2, 4, 0, 6, 7, 1]
private def pattern45361782 : Fin 8 → Fin 8 := ![3, 4, 2, 5, 0, 6, 7, 1]
private def pattern46153782 : Fin 8 → Fin 8 := ![3, 5, 0, 4, 2, 6, 7, 1]
private def pattern45163782 : Fin 8 → Fin 8 := ![3, 4, 0, 5, 2, 6, 7, 1]
private def pattern45261783 : Fin 8 → Fin 8 := ![3, 4, 1, 5, 0, 6, 7, 2]
private def pattern46251783 : Fin 8 → Fin 8 := ![3, 5, 1, 4, 0, 6, 7, 2]
private def pattern45162783 : Fin 8 → Fin 8 := ![3, 4, 0, 5, 1, 6, 7, 2]
private def pattern46152783 : Fin 8 → Fin 8 := ![3, 5, 0, 4, 1, 6, 7, 2]

private theorem swap14_34265781 : pattern34265781 ∘ swap14 = pattern35264781 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_35264781 : pattern35264781 ∘ swap14 = pattern34265781 := by
  funext i; fin_cases i <;> rfl
private theorem cycleInv_34265781 : pattern34265781 ∘ cycle.symm = pattern36254781 := by
  funext i; fin_cases i <;> rfl
private theorem cycle_36254781 : pattern36254781 ∘ cycle = pattern34265781 := by
  funext i; fin_cases i <;> rfl

private theorem cycleInv_34165782 : pattern34165782 ∘ cycle.symm = pattern36154782 := by
  funext i; fin_cases i <;> rfl
private theorem cycle_36154782 : pattern36154782 ∘ cycle = pattern34165782 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_34165782 : pattern34165782 ∘ swap14 = pattern35164782 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_35164782 : pattern35164782 ∘ swap14 = pattern34165782 := by
  funext i; fin_cases i <;> rfl

private theorem swap13_46352781 : pattern46352781 ∘ swap13 = pattern45362781 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_45362781 : pattern45362781 ∘ swap13 = pattern46352781 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_46253781 : pattern46253781 ∘ swap13 = pattern45263781 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_45263781 : pattern45263781 ∘ swap13 = pattern46253781 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_46351782 : pattern46351782 ∘ swap13 = pattern45361782 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_45361782 : pattern45361782 ∘ swap13 = pattern46351782 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_46153782 : pattern46153782 ∘ swap13 = pattern45163782 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_45163782 : pattern45163782 ∘ swap13 = pattern46153782 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_45261783 : pattern45261783 ∘ swap13 = pattern46251783 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_46251783 : pattern46251783 ∘ swap13 = pattern45261783 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_45162783 : pattern45162783 ∘ swap13 = pattern46152783 := by
  funext i; fin_cases i <;> rfl
private theorem swap13_46152783 : pattern46152783 ∘ swap13 = pattern45162783 := by
  funext i; fin_cases i <;> rfl

theorem exactOccurrenceCount_eq_34265781_35264781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern34265781) marks =
      WilfCounts.exactCount (occurrenceSet pattern35264781) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern34265781 pattern35264781 swap14
    (by decide) (by decide) swap14_34265781 swap14_35264781
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_34265781_36254781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern34265781) marks =
      WilfCounts.exactCount (occurrenceSet pattern36254781) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern34265781 pattern36254781 cycle.symm
    (by decide) (by decide) cycleInv_34265781 cycle_36254781
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_34165782_36154782 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern34165782) marks =
      WilfCounts.exactCount (occurrenceSet pattern36154782) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern34165782 pattern36154782 cycle.symm
    (by decide) (by decide) cycleInv_34165782 cycle_36154782
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_34165782_35164782 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern34165782) marks =
      WilfCounts.exactCount (occurrenceSet pattern35164782) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern34165782 pattern35164782 swap14
    (by decide) (by decide) swap14_34165782 swap14_35164782
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_46352781_45362781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern46352781) marks =
      WilfCounts.exactCount (occurrenceSet pattern45362781) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern46352781 pattern45362781 swap13
    (by decide) (by decide) swap13_46352781 swap13_45362781
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_46253781_45263781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern46253781) marks =
      WilfCounts.exactCount (occurrenceSet pattern45263781) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern46253781 pattern45263781 swap13
    (by decide) (by decide) swap13_46253781 swap13_45263781
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_46351782_45361782 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern46351782) marks =
      WilfCounts.exactCount (occurrenceSet pattern45361782) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern46351782 pattern45361782 swap13
    (by decide) (by decide) swap13_46351782 swap13_45361782
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_46153782_45163782 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern46153782) marks =
      WilfCounts.exactCount (occurrenceSet pattern45163782) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern46153782 pattern45163782 swap13
    (by decide) (by decide) swap13_46153782 swap13_45163782
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_45261783_46251783 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern45261783) marks =
      WilfCounts.exactCount (occurrenceSet pattern46251783) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern45261783 pattern46251783 swap13
    (by decide) (by decide) swap13_45261783 swap13_46251783
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exactOccurrenceCount_eq_45162783_46152783 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern45162783) marks =
      WilfCounts.exactCount (occurrenceSet pattern46152783) marks := by
  exact exactCount_eq_of_stationaryMax n marks pattern45162783 pattern46152783 swap13
    (by decide) (by decide) swap13_45162783 swap13_46152783
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! The tokens below are the archive's original orientations, obtained by reversing the
corresponding target windows. The supplementary `left8.pkl` archive places the first six in
blocks 11 and 57 and the remaining pairs in blocks 18, 37, 49, 56, 69, and 70. -/

def pattern18756243 : Fin 8 → Fin 8 := reversePattern pattern34265781
def pattern18746253 : Fin 8 → Fin 8 := reversePattern pattern35264781
def pattern18745263 : Fin 8 → Fin 8 := reversePattern pattern36254781
def pattern28756143 : Fin 8 → Fin 8 := reversePattern pattern34165782
def pattern28745163 : Fin 8 → Fin 8 := reversePattern pattern36154782
def pattern28746153 : Fin 8 → Fin 8 := reversePattern pattern35164782
def pattern18725364 : Fin 8 → Fin 8 := reversePattern pattern46352781
def pattern18726354 : Fin 8 → Fin 8 := reversePattern pattern45362781
def pattern18735264 : Fin 8 → Fin 8 := reversePattern pattern46253781
def pattern18736254 : Fin 8 → Fin 8 := reversePattern pattern45263781
def pattern28715364 : Fin 8 → Fin 8 := reversePattern pattern46351782
def pattern28716354 : Fin 8 → Fin 8 := reversePattern pattern45361782
def pattern28735164 : Fin 8 → Fin 8 := reversePattern pattern46153782
def pattern28736154 : Fin 8 → Fin 8 := reversePattern pattern45163782
def pattern38716254 : Fin 8 → Fin 8 := reversePattern pattern45261783
def pattern38715264 : Fin 8 → Fin 8 := reversePattern pattern46251783
def pattern38726154 : Fin 8 → Fin 8 := reversePattern pattern45162783
def pattern38725164 : Fin 8 → Fin 8 := reversePattern pattern46152783

theorem exactOccurrenceCount_eq_18756243_18746253 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18756243) marks =
      WilfCounts.exactCount (occurrenceSet pattern18746253) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern34265781 pattern35264781
    (fun m => exactOccurrenceCount_eq_34265781_35264781 n m) marks

theorem exactOccurrenceCount_eq_18756243_18745263 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18756243) marks =
      WilfCounts.exactCount (occurrenceSet pattern18745263) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern34265781 pattern36254781
    (fun m => exactOccurrenceCount_eq_34265781_36254781 n m) marks

theorem exactOccurrenceCount_eq_28756143_28745163 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28756143) marks =
      WilfCounts.exactCount (occurrenceSet pattern28745163) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern34165782 pattern36154782
    (fun m => exactOccurrenceCount_eq_34165782_36154782 n m) marks

theorem exactOccurrenceCount_eq_28756143_28746153 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28756143) marks =
      WilfCounts.exactCount (occurrenceSet pattern28746153) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern34165782 pattern35164782
    (fun m => exactOccurrenceCount_eq_34165782_35164782 n m) marks

theorem exactOccurrenceCount_eq_18725364_18726354 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18725364) marks =
      WilfCounts.exactCount (occurrenceSet pattern18726354) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern46352781 pattern45362781
    (fun m => exactOccurrenceCount_eq_46352781_45362781 n m) marks

theorem exactOccurrenceCount_eq_18735264_18736254 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18735264) marks =
      WilfCounts.exactCount (occurrenceSet pattern18736254) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern46253781 pattern45263781
    (fun m => exactOccurrenceCount_eq_46253781_45263781 n m) marks

theorem exactOccurrenceCount_eq_28715364_28716354 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28715364) marks =
      WilfCounts.exactCount (occurrenceSet pattern28716354) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern46351782 pattern45361782
    (fun m => exactOccurrenceCount_eq_46351782_45361782 n m) marks

theorem exactOccurrenceCount_eq_28735164_28736154 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28735164) marks =
      WilfCounts.exactCount (occurrenceSet pattern28736154) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern46153782 pattern45163782
    (fun m => exactOccurrenceCount_eq_46153782_45163782 n m) marks

theorem exactOccurrenceCount_eq_38716254_38715264 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern38716254) marks =
      WilfCounts.exactCount (occurrenceSet pattern38715264) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern45261783 pattern46251783
    (fun m => exactOccurrenceCount_eq_45261783_46251783 n m) marks

theorem exactOccurrenceCount_eq_38726154_38725164 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern38726154) marks =
      WilfCounts.exactCount (occurrenceSet pattern38725164) marks :=
  WilfReversal.exactOccurrenceCount_eq_reverse_of_eq n pattern45162783 pattern46152783
    (fun m => exactOccurrenceCount_eq_45162783_46152783 n m) marks

/-- Transitivity closes every member of source archive block 11. -/
theorem exactOccurrenceCount_eq_block11_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18746253) marks =
      WilfCounts.exactCount (occurrenceSet pattern18745263) marks := by
  exact (exactOccurrenceCount_eq_18756243_18746253 n marks).symm.trans
    (exactOccurrenceCount_eq_18756243_18745263 n marks)

/-- Transitivity closes every member of source archive block 57. -/
theorem exactOccurrenceCount_eq_block57_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28745163) marks =
      WilfCounts.exactCount (occurrenceSet pattern28746153) marks := by
  exact (exactOccurrenceCount_eq_28756143_28745163 n marks).symm.trans
    (exactOccurrenceCount_eq_28756143_28746153 n marks)

/-- The two members of source archive block 18 have equal exact counts. -/
theorem exactOccurrenceCount_eq_block18_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18725364) marks =
      WilfCounts.exactCount (occurrenceSet pattern18726354) marks :=
  exactOccurrenceCount_eq_18725364_18726354 n marks

/-- The two members of source archive block 37 have equal exact counts. -/
theorem exactOccurrenceCount_eq_block37_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern18735264) marks =
      WilfCounts.exactCount (occurrenceSet pattern18736254) marks :=
  exactOccurrenceCount_eq_18735264_18736254 n marks

/-- The two members of source archive block 49 have equal exact counts. -/
theorem exactOccurrenceCount_eq_block49_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28715364) marks =
      WilfCounts.exactCount (occurrenceSet pattern28716354) marks :=
  exactOccurrenceCount_eq_28715364_28716354 n marks

/-- The two members of source archive block 56 have equal exact counts. -/
theorem exactOccurrenceCount_eq_block56_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern28735164) marks =
      WilfCounts.exactCount (occurrenceSet pattern28736154) marks :=
  exactOccurrenceCount_eq_28735164_28736154 n marks

/-- The two members of source archive block 69 have equal exact counts. -/
theorem exactOccurrenceCount_eq_block69_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern38716254) marks =
      WilfCounts.exactCount (occurrenceSet pattern38715264) marks :=
  exactOccurrenceCount_eq_38716254_38715264 n marks

/-- The two members of source archive block 70 have equal exact counts. -/
theorem exactOccurrenceCount_eq_block70_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern38726154) marks =
      WilfCounts.exactCount (occurrenceSet pattern38725164) marks :=
  exactOccurrenceCount_eq_38726154_38725164 n marks

#print axioms exactOccurrenceCount_eq_34265781_35264781
#print axioms exactOccurrenceCount_eq_34265781_36254781
#print axioms exactOccurrenceCount_eq_34165782_36154782
#print axioms exactOccurrenceCount_eq_34165782_35164782
#print axioms exactOccurrenceCount_eq_46352781_45362781
#print axioms exactOccurrenceCount_eq_46253781_45263781
#print axioms exactOccurrenceCount_eq_46351782_45361782
#print axioms exactOccurrenceCount_eq_46153782_45163782
#print axioms exactOccurrenceCount_eq_45261783_46251783
#print axioms exactOccurrenceCount_eq_45162783_46152783
#print axioms exactOccurrenceCount_eq_18756243_18746253
#print axioms exactOccurrenceCount_eq_18756243_18745263
#print axioms exactOccurrenceCount_eq_28756143_28745163
#print axioms exactOccurrenceCount_eq_28756143_28746153
#print axioms exactOccurrenceCount_eq_18725364_18726354
#print axioms exactOccurrenceCount_eq_18735264_18736254
#print axioms exactOccurrenceCount_eq_28715364_28716354
#print axioms exactOccurrenceCount_eq_28735164_28736154
#print axioms exactOccurrenceCount_eq_38716254_38715264
#print axioms exactOccurrenceCount_eq_38726154_38725164
#print axioms exactOccurrenceCount_eq_block11_common
#print axioms exactOccurrenceCount_eq_block57_common
#print axioms exactOccurrenceCount_eq_block18_common
#print axioms exactOccurrenceCount_eq_block37_common
#print axioms exactOccurrenceCount_eq_block49_common
#print axioms exactOccurrenceCount_eq_block56_common
#print axioms exactOccurrenceCount_eq_block69_common
#print axioms exactOccurrenceCount_eq_block70_common

