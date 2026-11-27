import Implications.SplitGraphComponents
import Implications.SplitGraphTrees

/-! A simultaneous choice of distinct clique attachments for the outsiders of a triple row. -/

namespace Implications.SplitGraphAttachments

open SplitGraphTrees

variable {V : Type*} [DecidableEq V]

/-- Two clique neighbors can be chosen for every outsider without reusing a
clique vertex. The fixed row's center is excluded from the target. -/
theorem exists_outsider_attachments
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (ht : t ∈ C) (hA : (row G I t).card = 3)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ f : ((I \ row G I t : Finset V) × Bool) ↪ (C.erase t : Finset V),
      ∀ i b, G.Adj (f (i, b) : V) (i : V) := by
  classical
  let O := I \ row G I t
  have hat (i : O) : ∃ x y : V, x ∈ C.erase t ∧ y ∈ C.erase t ∧
      x ≠ y ∧ G.Adj x i.val ∧ G.Adj y i.val := by
    have hi := Finset.mem_sdiff.mp i.property
    obtain ⟨x, hx, y, hy, hxy, hxi, hyi⟩ := hdeg i.val hi.1
    have hnot (q : V) (hq : G.Adj q i.val) : q ≠ t := by
      rintro rfl
      exact hi.2 (Finset.mem_filter.mpr ⟨hi.1, hq⟩)
    exact ⟨x, y, Finset.mem_erase.mpr ⟨hnot x hxi, hx⟩,
      Finset.mem_erase.mpr ⟨hnot y hyi, hy⟩, hxy, hxi, hyi⟩
  choose x y hx hy hxy hxi hyi using hat
  let f : O × Bool → (C.erase t : Finset V) := fun (i, b) =>
    if b then ⟨y i, hy i⟩ else ⟨x i, hx i⟩
  have hadj (i : O) (b : Bool) : G.Adj (f (i, b) : V) i.val := by
    cases b
    · exact hxi i
    · exact hyi i
  refine ⟨⟨f, ?_⟩, hadj⟩
  rintro ⟨i, b⟩ ⟨j, d⟩ he
  have heV := congrArg Subtype.val he
  let q : V := f (i, b)
  have hq := Finset.mem_erase.mp (f (i, b)).property
  have hin (k : O) (had : G.Adj q k.val) : k.val ∈ row G I q \ row G I t := by
    have hk := Finset.mem_sdiff.mp k.property
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hk.1, had⟩, hk.2⟩
  have hi := hin i (hadj i b)
  have hj := hin j (by simpa only [q, heV] using hadj j d)
  have hdiff' : (row G I t \ row G I q ∪ row G I q \ row G I t).card ≤ 2 :=
    hdiff t ht q hq.2 hq.1.symm
  have hone := (SplitGraphComponents.tripleRow_outside_counts
    (row G I t) (row G I q) hA (hrow q hq.2) hdiff' ⟨i.val, hi⟩).2
  have hij : i = j := Subtype.ext (Finset.card_le_one_iff.mp hone.le hi hj)
  subst j
  have hbd : b = d := by
    cases b <;> cases d
    · rfl
    · exact (hxy i (show x i = y i from heV)).elim
    · exact (hxy i (show y i = x i from heV).symm).elim
    · rfl
  rw [hbd]

/-- The clique has room for both attachments of every outsider and the center. -/
theorem twice_outsiders_add_one_le_clique_card
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (ht : t ∈ C) (hA : (row G I t).card = 3)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    2 * (I \ row G I t).card + 1 ≤ C.card := by
  obtain ⟨f, _⟩ := exists_outsider_attachments G C I t ht hA hrow hdiff hdeg
  have h := Fintype.card_le_of_injective f f.injective
  simp [Finset.card_erase_of_mem ht] at h
  have := Finset.card_pos.mpr ⟨t, ht⟩
  omega

#print axioms exists_outsider_attachments
#print axioms twice_outsiders_add_one_le_clique_card

end Implications.SplitGraphAttachments
