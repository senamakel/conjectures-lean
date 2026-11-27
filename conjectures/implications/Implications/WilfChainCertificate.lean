import Implications.WilfCertifiedSwap

/-! Local comparison chains for the swap at positions four and six. -/

namespace Implications.WilfChainCertificate

open WilfMarked WilfPatternSwap WilfTwoWindowOrder

/-- A rank inequality supplied by either window. -/
private def Edge (p : Fin 8 → Fin 8) (a b : Fin 13) : Prop :=
  ∃ i j : Fin 8, p i < p j ∧
    ((a = position 0 i ∧ b = position 0 j) ∨ (a = position 5 i ∧ b = position 5 j))

private instance (p : Fin 8 → Fin 8) (a b : Fin 13) : Decidable (Edge p a b) := by
  unfold Edge
  infer_instance

/-- A certificate provides intermediate vertices in a chain of strict inequalities. -/
private def Chain (p : Fin 8 → Fin 8) (a b : Fin 13) : List (Fin 13) → Prop
  | [] => Edge p a b
  | x :: xs => Edge p a x ∧ Chain p x b xs

private instance (p : Fin 8 → Fin 8) (a b : Fin 13) (xs : List (Fin 13)) :
    Decidable (Chain p a b xs) := by
  induction xs generalizing a with
  | nil => exact inferInstanceAs (Decidable (Edge p a b))
  | cons x xs ih =>
    letI : Decidable (Chain p x b xs) := ih x
    exact inferInstanceAs (Decidable (Edge p a x ∧ Chain p x b xs))

private theorem edge_sound {α : Type*} [Preorder α] {p : Fin 8 → Fin 8}
    {f : Fin 13 → α} (h0 : WindowOrder p f 0) (h5 : WindowOrder p f 5)
    {a b : Fin 13} (he : Edge p a b) : f a < f b := by
  obtain ⟨i, j, hij, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := he
  · exact h0 i j hij
  · exact h5 i j hij

private theorem chain_sound {α : Type*} [Preorder α] {p : Fin 8 → Fin 8}
    {f : Fin 13 → α} (h0 : WindowOrder p f 0) (h5 : WindowOrder p f 5)
    {a b : Fin 13} {xs : List (Fin 13)} (h : Chain p a b xs) : f a < f b := by
  induction xs generalizing a with
  | nil => exact edge_sound h0 h5 h
  | cons x xs ih =>
    change Edge p a x ∧ Chain p x b xs at h
    exact (edge_sound h0 h5 h.1).trans (ih h.2)

/-- Check the direction of the comparison after replacing the later first entry. -/
private def Check (p : Fin 8 → Fin 8) (j : Fin 8) (xs : List (Fin 13)) : Prop :=
  if p 0 < p j then Chain p 3 (position 5 j) xs else Chain p (position 5 j) 3 xs

private instance (p : Fin 8 → Fin 8) (j : Fin 8) (xs : List (Fin 13)) :
    Decidable (Check p j xs) := by
  unfold Check
  infer_instance

private theorem certificate_of_chains (p : Fin 8 → Fin 8)
    (paths : Fin 8 → List (Fin 13)) (h : ∀ j : Fin 8, j ≠ 0 → Check p j (paths j)) :
    FirstOrderCertificate p := by
  intro n π t ht hfirst hsecond j hj
  apply lift_replacement_order p j _ π t ht hfirst hsecond
  intro f h0 h5
  have hpath := h j hj
  by_cases hr : p 0 < p j
  · rw [Check, if_pos hr] at hpath
    exact iff_of_true (chain_sound h0 h5 hpath) hr
  · rw [Check, if_neg hr] at hpath
    exact iff_of_false (not_lt_of_gt (chain_sound h0 h5 hpath)) hr

private theorem exact_count_of_chains (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8)
    (pp qp : Fin 8 → List (Fin 13))
    (hp : ∀ j : Fin 8, j ≠ 0 → Check p j (pp j))
    (hq : ∀ j : Fin 8, j ≠ 0 → Check q j (qp j))
    (hpo : ∀ d : Fin 8, 0 < d → (overlapCompatible p d.val = true ↔ d.val = 5 ∨ d.val = 7))
    (hqo : ∀ d : Fin 8, 0 < d → (overlapCompatible q d.val = true ↔ d.val = 5 ∨ d.val = 7))
    (hp0 : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j)
    (hq0 : ∀ j : Fin 8, j ≠ 0 → q 0 ≠ q j)
    (hps : p ∘ windowSwap = q) (hqs : q ∘ windowSwap = p) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet q) marks :=
  exactOccurrenceCount_eq_of_certificate n marks p q
    (fun d hd hn h => (hpo ⟨d, hn⟩ hd).mp h)
    (fun d hd hn h => (hqo ⟨d, hn⟩ hd).mp h)
    hp0 hq0 (certificate_of_chains p pp hp) (certificate_of_chains q qp hq) hps hqs

private def pattern34275681 : Fin 8 → Fin 8 := ![2, 3, 1, 6, 4, 5, 7, 0]
private def pattern34265781 : Fin 8 → Fin 8 := ![2, 3, 1, 5, 4, 6, 7, 0]

theorem exactOccurrenceCount_eq_34275681_34265781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern34275681) marks =
      WilfCounts.exactCount (occurrenceSet pattern34265781) marks :=
  exact_count_of_chains n marks pattern34275681 pattern34265781
    ![[], [], [], [6], [6], [6], [6], [5]] ![[], [], [], [5], [5], [5], [5], [7]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

private def pattern45372681 : Fin 8 → Fin 8 := ![3, 4, 2, 6, 1, 5, 7, 0]
private def pattern45362781 : Fin 8 → Fin 8 := ![3, 4, 2, 5, 1, 6, 7, 0]

theorem exactOccurrenceCount_eq_45372681_45362781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern45372681) marks =
      WilfCounts.exactCount (occurrenceSet pattern45362781) marks :=
  exact_count_of_chains n marks pattern45372681 pattern45362781
    ![[], [], [], [6], [5], [6], [6], [5]] ![[], [], [], [5], [7], [5], [5], [7]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

private def pattern56472381 : Fin 8 → Fin 8 := ![4, 5, 3, 6, 1, 2, 7, 0]
private def pattern56432781 : Fin 8 → Fin 8 := ![4, 5, 3, 2, 1, 6, 7, 0]

theorem exactOccurrenceCount_eq_56472381_56432781 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern56472381) marks =
      WilfCounts.exactCount (occurrenceSet pattern56432781) marks :=
  exact_count_of_chains n marks pattern56472381 pattern56432781
    ![[], [], [], [6], [5], [5], [6], [5]] ![[], [], [], [7], [7], [5], [5], [7]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

private def pattern23158674 : Fin 8 → Fin 8 := ![1, 2, 0, 4, 7, 5, 6, 3]
private def pattern23168574 : Fin 8 → Fin 8 := ![1, 2, 0, 5, 7, 4, 6, 3]

theorem exactOccurrenceCount_eq_23158674_23168574 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern23158674) marks =
      WilfCounts.exactCount (occurrenceSet pattern23168574) marks :=
  exact_count_of_chains n marks pattern23158674 pattern23168574
    ![[], [], [], [5], [5], [5], [5], [5]] ![[], [], [], [6], [6], [6], [6], [6]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

private def pattern45371682 : Fin 8 → Fin 8 := ![3, 4, 2, 6, 0, 5, 7, 1]
private def pattern45361782 : Fin 8 → Fin 8 := ![3, 4, 2, 5, 0, 6, 7, 1]

theorem exactOccurrenceCount_eq_45371682_45361782 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern45371682) marks =
      WilfCounts.exactCount (occurrenceSet pattern45361782) marks :=
  exact_count_of_chains n marks pattern45371682 pattern45361782
    ![[], [], [], [6], [5], [6], [6], [5]] ![[], [], [], [5], [7], [5], [5], [7]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

private def pattern56431782 : Fin 8 → Fin 8 := ![4, 5, 3, 2, 0, 6, 7, 1]
private def pattern56471382 : Fin 8 → Fin 8 := ![4, 5, 3, 6, 0, 2, 7, 1]

theorem exactOccurrenceCount_eq_56431782_56471382 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern56431782) marks =
      WilfCounts.exactCount (occurrenceSet pattern56471382) marks :=
  exact_count_of_chains n marks pattern56431782 pattern56471382
    ![[], [], [], [7], [7], [5], [5], [7]] ![[], [], [], [6], [5], [5], [6], [5]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

private def pattern67541382 : Fin 8 → Fin 8 := ![5, 6, 4, 3, 0, 2, 7, 1]
private def pattern67531482 : Fin 8 → Fin 8 := ![5, 6, 4, 2, 0, 3, 7, 1]

theorem exactOccurrenceCount_eq_67541382_67531482 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern67541382) marks =
      WilfCounts.exactCount (occurrenceSet pattern67531482) marks :=
  exact_count_of_chains n marks pattern67541382 pattern67531482
    ![[], [], [], [5], [5], [5], [6], [5]] ![[], [], [], [7], [7], [7], [5], [7]]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)

#print axioms exactOccurrenceCount_eq_34275681_34265781
#print axioms exactOccurrenceCount_eq_45372681_45362781
#print axioms exactOccurrenceCount_eq_56472381_56432781
#print axioms exactOccurrenceCount_eq_23158674_23168574
#print axioms exactOccurrenceCount_eq_45371682_45361782
#print axioms exactOccurrenceCount_eq_56431782_56471382
#print axioms exactOccurrenceCount_eq_67541382_67531482

end Implications.WilfChainCertificate
