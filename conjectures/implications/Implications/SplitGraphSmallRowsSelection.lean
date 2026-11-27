import Implications.SplitGraphSmallRows
import Implications.SplitGraphTrees

/-!
Choose two neighbors per independent vertex and bound the resulting
selected-row overlaps in the small-row split-graph case.
-/

namespace SplitGraphSmallRowsSelection

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The independent vertices that select a given clique vertex. -/
def selectedRow (I : Finset V) (left right : V → V) (q : V) : Finset V :=
  I.filter (fun i => left i = q ∨ right i = q)

/-- Under the small-row hypotheses, both chosen neighbors exist for every
independent vertex, each selected row has size at most two, and at most
three clique vertices are selected twice. -/
theorem exists_selected_neighbors
    (G : SimpleGraph V) (C I : Finset V)
    (hrows : ∀ q ∈ C, (row G I q).card ≤ 2)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ left right : V → V,
      (∀ i ∈ I, left i ∈ C) ∧ (∀ i ∈ I, right i ∈ C) ∧
      (∀ i ∈ I, G.Adj (left i) i) ∧ (∀ i ∈ I, G.Adj (right i) i) ∧
      (∀ i ∈ I, left i ≠ right i) ∧
      (∀ q ∈ C, (selectedRow I left right q).card ≤ 2) ∧
      (C.filter (fun q => (selectedRow I left right q).card = 2)).card ≤ 3 := by
  classical
  have hchoose (i : V) :
      ∃ q d : V, i ∈ I → q ∈ C ∧ d ∈ C ∧ q ≠ d ∧ G.Adj q i ∧ G.Adj d i := by
    by_cases hi : i ∈ I
    · obtain ⟨q,hq,d,hd,hne,hqa,hda⟩ := hdeg i hi
      exact ⟨q,d,fun _ => ⟨hq,hd,hne,hqa,hda⟩⟩
    · exact ⟨i,i,fun h => (hi h).elim⟩
  choose left right hes using hchoose
  have hlC : ∀ i ∈ I, left i ∈ C := fun i hi => (hes i hi).1
  have hrC : ∀ i ∈ I, right i ∈ C := fun i hi => (hes i hi).2.1
  have hneq : ∀ i ∈ I, left i ≠ right i := fun i hi => (hes i hi).2.2.1
  have hlR : ∀ i ∈ I, i ∈ row G I (left i) := fun i hi =>
    Finset.mem_filter.mpr ⟨hi, (hes i hi).2.2.2.1⟩
  have hrR : ∀ i ∈ I, i ∈ row G I (right i) := fun i hi =>
    Finset.mem_filter.mpr ⟨hi, (hes i hi).2.2.2.2⟩
  have hsub (q : V) : selectedRow I left right q ⊆ row G I q := by
    intro i hi
    obtain ⟨hiI, hq | hq⟩ := Finset.mem_filter.mp hi
    · exact hq ▸ hlR i hiI
    · exact hq ▸ hrR i hiI
  exact ⟨left, right, hlC, hrC, (fun i hi => (hes i hi).2.2.2.1),
    (fun i hi => (hes i hi).2.2.2.2), hneq,
    (fun q hq => (Finset.card_le_card (hsub q)).trans (hrows q hq)),
    SplitGraphSmallRows.chosen_neighbor_rows_card_le_three C I (row G I) left right
      (fun q _ => Finset.filter_subset _ _) hrows hdiff hlC hrC hlR hrR hneq⟩

end SplitGraphSmallRowsSelection

#print axioms SplitGraphSmallRowsSelection.exists_selected_neighbors
