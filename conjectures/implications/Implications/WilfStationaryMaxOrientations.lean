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

