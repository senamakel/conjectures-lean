import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! Semantics of sequential at-most-one clauses and one-way indicator gates. -/

namespace C4SequentialAtMostOne

/-- The prefix variable at index `k` records whether any earlier input
is true. The initial prefix is false and the last input has no output prefix. -/
def Sequential {n : ℕ} (input : Fin n → Prop) (seen : ℕ → Prop) : Prop :=
  ¬ seen 0 ∧
  (∀ i : Fin n, i.val + 1 < n →
    (input i → seen (i.val + 1)) ∧ (seen i.val → seen (i.val + 1))) ∧
  ∀ i : Fin n, ¬ (input i ∧ seen i.val)

/-- The sequential clauses admit prefix values exactly when no two inputs
can both hold. -/
theorem exists_sequential_iff {n : ℕ} (input : Fin n → Prop) :
    (∃ seen, Sequential input seen) ↔ ∀ i j : Fin n, i < j → ¬ (input i ∧ input j) := by
  constructor
  · rintro ⟨seen, _, hstep, hno⟩ i j hij ⟨hi, hj⟩
    have hij' : i.val + 1 ≤ j.val := hij
    have hprefix : ∀ k : ℕ, i.val + 1 ≤ k → k ≤ j.val → seen k := by
      intro k hik
      induction k, hik using Nat.le_induction with
      | base =>
        intro _
        exact (hstep i (Nat.lt_of_le_of_lt hij' j.isLt)).1 hi
      | succ k hik ih =>
        intro hkj
        have hk : k + 1 < n := Nat.lt_of_le_of_lt hkj j.isLt
        exact (hstep ⟨k, by omega⟩ hk).2 (ih (Nat.le_of_succ_le hkj))
    exact hno j ⟨hj, hprefix j.val hij' (Nat.le_refl _)⟩
  · intro hno
    refine ⟨fun k => ∃ i : Fin n, i.val < k ∧ input i, ?_, ?_, ?_⟩
    · rintro ⟨i, hlt, _⟩
      exact (Nat.not_lt_zero _) hlt
    · intro i _
      constructor
      · intro hi
        exact ⟨i, Nat.lt_succ_self _, hi⟩
      · rintro ⟨j, hj, hinput⟩
        exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self _), hinput⟩
    · rintro i ⟨hi, j, hji, hj⟩
      exact hno j i hji ⟨hj, hi⟩

/-- One-way gates from the original inputs to the auxiliary flags suffice.
An allowed assignment extends by making each flag equal to its input. -/
theorem exists_flags_sequential_iff {n : ℕ} (input : Fin n → Prop) :
    (∃ flags : Fin n → Prop, (∀ i, input i → flags i) ∧ ∃ seen, Sequential flags seen) ↔
      ∀ i j : Fin n, i < j → ¬ (input i ∧ input j) := by
  constructor
  · rintro ⟨flags, himplies, hprefix⟩ i j hij ⟨hi, hj⟩
    exact (exists_sequential_iff flags).mp hprefix i j hij ⟨himplies i hi, himplies j hj⟩
  · intro h
    exact ⟨input, fun _ hi => hi, (exists_sequential_iff input).mpr h⟩

#print axioms exists_flags_sequential_iff

end C4SequentialAtMostOne
