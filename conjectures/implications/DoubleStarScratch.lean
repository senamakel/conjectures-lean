import Mathlib

open SimpleGraph

private def starForward {n m : ℕ} : (Fin n ⊕ Fin m) → (Fin n ⊕ Fin m) → Prop
  | .inl i, .inr j => i = 0 ∨ j = 0
  | _, _ => False

private instance {n m : ℕ} : DecidableRel (@starForward n m) := by
  intro x y
  cases x <;> cases y <;> unfold starForward <;> infer_instance

private def doubleStar (n m : ℕ) : SimpleGraph (Fin n ⊕ Fin m) := fromRel starForward

private instance {n m : ℕ} : DecidableRel (doubleStar n m).Adj :=
  inferInstanceAs (DecidableRel (fromRel (@starForward n m)).Adj)

private lemma star_first {n m : ℕ} (j : Fin m) : (doubleStar n m).Adj (.inl 0) (.inr j) := by
  simp [doubleStar, fromRel_adj, starForward]

private lemma star_second {n m : ℕ} (i : Fin n) : (doubleStar n m).Adj (.inl i) (.inr 0) := by
  simp [doubleStar, fromRel_adj, starForward]

private lemma doubleStar_isTree {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (doubleStar n m).IsTree := by
  rw [isTree_iff_connected_and_card]
  constructor
  · refine (connected_iff_exists_forall_reachable _).mpr ⟨.inl 0, fun x => ?_⟩
    cases x with
    | inl i => exact (star_first 0).reachable.trans (star_second i).reachable.symm
    | inr j => exact (star_first j).reachable
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
    decide +kernel
