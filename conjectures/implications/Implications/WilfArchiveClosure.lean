import Implications.WilfThreeCycleGlobal
import Implications.WilfChainCertificate
import Implications.WilfCertifiedSwap

/-! Checked transitive closure of additional length-eight Wilf archive blocks. -/

namespace Implications.WilfArchiveClosure

open WilfMarked WilfPatternSwap WilfThreeCycleOrder

/-- The zero-based position transposition used by the archived comparisons. -/
private def swap14 : Equiv.Perm (Fin 8) := Equiv.swap 1 4

private theorem exactOccurrenceCount_eq_swap14 (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8) (hpq : p ∘ swap14 = q) (hqp : q ∘ swap14 = p)
    (hinjP : Function.Injective p)
    (hmaxP : ∀ i : Fin 8, i ≠ 6 → p i < p 6)
    (hsecondP : ∀ i : Fin 8, i ≠ 6 → i ≠ 5 → p i < p 5)
    (hcrossP : p 0 < p (swap14 1))
    (hinjQ : Function.Injective q)
    (hmaxQ : ∀ i : Fin 8, i ≠ 6 → q i < q 6)
    (hsecondQ : ∀ i : Fin 8, i ≠ 6 → i ≠ 5 → q i < q 5)
    (hcrossQ : q 0 < q (swap14 1))
    (hcheckP : ∀ d, 1 ≤ d → d < 8 →
      (overlapCompatible p d = true ↔ d = 5 ∨ d = 7))
    (hcheckQ : ∀ d, 1 ≤ d → d < 8 →
      (overlapCompatible q d = true ↔ d = 5 ∨ d = 7)) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet q) marks := by
  apply WilfThreeCycleGlobal.exactOccurrenceCount_eq_of_markedSwap n marks p q swap14
  · decide
  · decide
  · exact hcheckP
  · exact hcheckQ
  · exact hpq
  · exact hqp
  · intro f hf hn i j
    simpa only [← hpq, Function.comp_apply] using
      overlap_cycle_order p swap14 hinjP (by decide) hmaxP hsecondP hcrossP f hf hn i j
  · intro f hf hn i j
    have hswap : swap14.symm = swap14 := by simp [swap14]
    rw [hswap]
    simpa only [← hqp, Function.comp_apply, Equiv.symm_symm] using
      overlap_cycle_order q swap14 hinjQ (by decide) hmaxQ hsecondQ hcrossQ f hf hn i j

def pattern26134785 : Fin 8 → Fin 8 := ![1, 5, 0, 2, 3, 6, 7, 4]
def pattern24136785 : Fin 8 → Fin 8 := ![1, 3, 0, 2, 5, 6, 7, 4]
def pattern26135784 : Fin 8 → Fin 8 := ![1, 5, 0, 2, 4, 6, 7, 3]
def pattern25136784 : Fin 8 → Fin 8 := ![1, 4, 0, 2, 5, 6, 7, 3]
def pattern26145783 : Fin 8 → Fin 8 := ![1, 5, 0, 3, 4, 6, 7, 2]
def pattern25146783 : Fin 8 → Fin 8 := ![1, 4, 0, 3, 5, 6, 7, 2]

def pattern36124785 : Fin 8 → Fin 8 := ![2, 5, 0, 1, 3, 6, 7, 4]
def pattern34126785 : Fin 8 → Fin 8 := ![2, 3, 0, 1, 5, 6, 7, 4]
def pattern36214785 : Fin 8 → Fin 8 := ![2, 5, 1, 0, 3, 6, 7, 4]
def pattern34216785 : Fin 8 → Fin 8 := ![2, 3, 1, 0, 5, 6, 7, 4]
def pattern35126784 : Fin 8 → Fin 8 := ![2, 4, 0, 1, 5, 6, 7, 3]
def pattern36125784 : Fin 8 → Fin 8 := ![2, 5, 0, 1, 4, 6, 7, 3]
def pattern36215784 : Fin 8 → Fin 8 := ![2, 5, 1, 0, 4, 6, 7, 3]
def pattern35216784 : Fin 8 → Fin 8 := ![2, 4, 1, 0, 5, 6, 7, 3]

private theorem swap14_26134785 : pattern26134785 ∘ swap14 = pattern24136785 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_24136785 : pattern24136785 ∘ swap14 = pattern26134785 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_26135784 : pattern26135784 ∘ swap14 = pattern25136784 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_25136784 : pattern25136784 ∘ swap14 = pattern26135784 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_26145783 : pattern26145783 ∘ swap14 = pattern25146783 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_25146783 : pattern25146783 ∘ swap14 = pattern26145783 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_36124785 : pattern36124785 ∘ swap14 = pattern34126785 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_34126785 : pattern34126785 ∘ swap14 = pattern36124785 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_36214785 : pattern36214785 ∘ swap14 = pattern34216785 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_34216785 : pattern34216785 ∘ swap14 = pattern36214785 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_35126784 : pattern35126784 ∘ swap14 = pattern36125784 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_36125784 : pattern36125784 ∘ swap14 = pattern35126784 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_36215784 : pattern36215784 ∘ swap14 = pattern35216784 := by
  funext i; fin_cases i <;> rfl
private theorem swap14_35216784 : pattern35216784 ∘ swap14 = pattern36215784 := by
  funext i; fin_cases i <;> rfl

theorem exactOccurrenceCount_eq_26134785_24136785 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern26134785) marks =
      WilfCounts.exactCount (occurrenceSet pattern24136785) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern26134785 pattern24136785
    swap14_26134785 swap14_24136785 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

theorem exactOccurrenceCount_eq_26135784_25136784 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern26135784) marks =
      WilfCounts.exactCount (occurrenceSet pattern25136784) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern26135784 pattern25136784
    swap14_26135784 swap14_25136784 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

theorem exactOccurrenceCount_eq_26145783_25146783 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern26145783) marks =
      WilfCounts.exactCount (occurrenceSet pattern25146783) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern26145783 pattern25146783
    swap14_26145783 swap14_25146783 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

theorem exactOccurrenceCount_eq_36124785_34126785 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern36124785) marks =
      WilfCounts.exactCount (occurrenceSet pattern34126785) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern36124785 pattern34126785
    swap14_36124785 swap14_34126785 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

theorem exactOccurrenceCount_eq_36214785_34216785 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern36214785) marks =
      WilfCounts.exactCount (occurrenceSet pattern34216785) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern36214785 pattern34216785
    swap14_36214785 swap14_34216785 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

theorem exactOccurrenceCount_eq_35126784_36125784 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern35126784) marks =
      WilfCounts.exactCount (occurrenceSet pattern36125784) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern35126784 pattern36125784
    swap14_35126784 swap14_36125784 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

theorem exactOccurrenceCount_eq_36215784_35216784 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern36215784) marks =
      WilfCounts.exactCount (occurrenceSet pattern35216784) marks := by
  exact exactOccurrenceCount_eq_swap14 n marks pattern36215784 pattern35216784
    swap14_36215784 swap14_35216784 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd hs; interval_cases d <;> decide)
    (by intro d hd hs; interval_cases d <;> decide)

private def pattern23147685 : Fin 8 → Fin 8 := ![1, 2, 0, 3, 6, 5, 7, 4]
private def pattern23156784 : Fin 8 → Fin 8 := ![1, 2, 0, 4, 5, 6, 7, 3]
private def pattern23157684 : Fin 8 → Fin 8 := ![1, 2, 0, 4, 6, 5, 7, 3]
private def pattern23167584 : Fin 8 → Fin 8 := ![1, 2, 0, 5, 6, 4, 7, 3]
private def pattern24156783 : Fin 8 → Fin 8 := ![1, 3, 0, 4, 5, 6, 7, 2]
private def pattern34217685 : Fin 8 → Fin 8 := ![2, 3, 1, 0, 6, 5, 7, 4]

/-- The three patterns in archived block 42 have a common exact-count representative. -/
theorem exactOccurrenceCount_eq_block42_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern26134785) marks =
      WilfCounts.exactCount (occurrenceSet pattern23147685) marks := by
  exact (WilfThreeCycleGlobal.exactOccurrenceCount_eq_26134785_23146785 n marks).trans
    (WilfChainCertificate.exactOccurrenceCount_eq_23147685_23146785 n marks).symm

/-- All four listed patterns in archived block 43 have a common exact-count representative. -/
theorem exactOccurrenceCount_eq_block43_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern26135784) marks =
      WilfCounts.exactCount (occurrenceSet pattern23167584) marks := by
  exact (WilfThreeCycleGlobal.exactOccurrenceCount_eq_26135784_23156784 n marks).trans
    ((WilfChainCertificate.exactOccurrenceCount_eq_23156784_23157684 n marks).trans
      (WilfCertifiedSwap.exactOccurrenceCount_eq_23157684_23167584 n marks))

/-- The two members of archived block 47 not already connected by its source edge agree. -/
theorem exactOccurrenceCount_eq_block47_members (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern24156783) marks =
      WilfCounts.exactCount (occurrenceSet pattern25146783) marks := by
  exact (WilfThreeCycleGlobal.exactOccurrenceCount_eq_26145783_24156783 n marks).symm.trans
    (exactOccurrenceCount_eq_26145783_25146783 n marks)

/-- The three members of archived block 63 have a common exact-count representative. -/
theorem exactOccurrenceCount_eq_block63_common (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern36214785) marks =
      WilfCounts.exactCount (occurrenceSet pattern34217685) marks := by
  exact (exactOccurrenceCount_eq_36214785_34216785 n marks).trans
    (WilfChainCertificate.exactOccurrenceCount_eq_34216785_34217685 n marks)

#print axioms exactOccurrenceCount_eq_26134785_24136785
#print axioms exactOccurrenceCount_eq_26135784_25136784
#print axioms exactOccurrenceCount_eq_26145783_25146783
#print axioms exactOccurrenceCount_eq_36124785_34126785
#print axioms exactOccurrenceCount_eq_36214785_34216785
#print axioms exactOccurrenceCount_eq_35126784_36125784
#print axioms exactOccurrenceCount_eq_36215784_35216784
#print axioms exactOccurrenceCount_eq_block42_common
#print axioms exactOccurrenceCount_eq_block43_common
#print axioms exactOccurrenceCount_eq_block47_members
#print axioms exactOccurrenceCount_eq_block63_common

end Implications.WilfArchiveClosure
