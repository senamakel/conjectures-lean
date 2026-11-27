import Implications.WilfPatternSwap
import Implications.WilfTwoWindowOrder

/-! Exact marked occurrence counts from two-window order certificates. -/

namespace Implications.WilfCertifiedSwap

open WilfMarked WilfGlobalSwap WilfPatternSwap WilfTwoWindowOrder

/-- The two-window certificate yields super-strong consecutive Wilf equivalence
for 23157684 and 23167584. -/
theorem exactOccurrenceCount_eq_23157684_23167584 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern23157684) marks =
      WilfCounts.exactCount (occurrenceSet pattern23167584) marks := by
  apply exactOccurrenceCount_eq_of_certificate n marks pattern23157684 pattern23167584
  · apply overlap_compatible_only_at_5_or_7_of_decide
    intro d hd hn
    interval_cases d <;> decide
  · apply overlap_compatible_only_at_5_or_7_of_decide
    intro d hd hn
    interval_cases d <;> decide
  · decide
  · decide
  · exact fun π t ht => replacement_order_of_occurrences π _ (Or.inl rfl) t ht
  · exact fun π t ht => replacement_order_of_occurrences π _ (Or.inr rfl) t ht
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

#print axioms exactOccurrenceCount_eq_23157684_23167584

end Implications.WilfCertifiedSwap
