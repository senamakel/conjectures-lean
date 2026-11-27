import Implications.SplitGraphSmallRows
import Implications.SplitGraphSmallRowsPath

/-!
The triangle alternative for three selected degree-two clique rows.
-/

namespace SplitGraphSmallRowsThree

open SplitGraphTrees

variable {α : Type*} [DecidableEq α]

/-- Three distinct, pairwise-intersecting two-element rows with no common
element are exactly the three edges of a triangle. -/
theorem three_pair_rows_are_triangle
    (F : Finset (Finset α))
    (hcardF : F.card = 3)
    (hcard : ∀ s ∈ F, s.card = 2)
    (hint : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → ∃ x, x ∈ s ∧ x ∈ t)
    (hnocenter : ¬ ∃ x, ∀ s ∈ F, x ∈ s) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      F = {({a,b} : Finset α), {b,c}, {a,c}} := by
  classical
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain hcenter | htriangle :=
    SplitGraphSmallRows.pairwise_intersecting_two_sets F hne hcard hint
  · exact (hnocenter hcenter).elim
  · obtain ⟨a,b,c,hab,hac,hbc,hsub⟩ := htriangle
    have hFsub : F ⊆ ({({a,b} : Finset α), {b,c}, {a,c}} : Finset (Finset α)) := by
      intro s hs
      have hs' := hsub s hs
      have hcardS := hcard s hs
      have hsTriple : s ⊆ ({a,b,c} : Finset α) := by simpa using hs'
      have hpair : s = {a,b} ∨ s = {b,c} ∨ s = {a,c} := by
        rcases Finset.card_eq_two.mp hcardS with ⟨x,y,hxy,heq⟩
        have hx : x = a ∨ x = b ∨ x = c := by
          have := hsTriple (by simp [heq])
          simpa using this
        have hy : y = a ∨ y = b ∨ y = c := by
          have := hsTriple (by simp [heq])
          simpa using this
        rcases hx with hxa | hxb | hxc <;>
          rcases hy with hya | hyb | hyc <;>
          subst x <;> subst y <;> simp_all [Finset.pair_comm]
      rcases hpair with h | h | h <;> simp [h]
    have htargetCard : ({({a,b} : Finset α), {b,c}, {a,c}} : Finset (Finset α)).card = 3 := by
      simp [hab, hac, hbc]
    have hEq := Finset.eq_of_subset_of_card_le hFsub
      (by rw [hcardF, htargetCard])
    exact ⟨a,b,c,hab,hac,hbc,hEq.symm⟩

end SplitGraphSmallRowsThree
