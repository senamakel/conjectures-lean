import Implications.C4Extremal42SearchConstraints
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Logic.Equiv.Fintype

/-! The degree-six root and its neighbors can be assigned fixed SAT labels. -/

namespace C4Extremal42

open Implications.C4PolaritySurvivorBound

/-- A degree-six vertex can be labelled 0 and its neighbors labelled 1 through 6. -/
theorem exists_degree_six_root_relabel
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj] (v : Fin 42) (hv : G.degree v = 6) :
    ∃ σ : Equiv.Perm (Fin 42), σ v = 0 ∧
      ∀ u, G.Adj v (σ.symm u) ↔ 0 < u ∧ u ≤ 6 := by
  let S : Finset (Fin 42) := Finset.Ioc 0 6
  have hS : S.card = 6 := by decide
  have hcard : (G.neighborFinset v).card = S.card := by simp [hv, hS]
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq (G.neighborFinset v) S hcard
  have hnot : e v ∉ S := by
    rw [← he, Finset.mem_map_equiv, Equiv.symm_apply_apply, G.mem_neighborFinset]
    exact G.irrefl
  have hzero : (0 : Fin 42) ∉ S := by simp [S]
  let swapRoot := Equiv.swap (e v) 0
  refine ⟨e.trans swapRoot, by simp [swapRoot], ?_⟩
  have hswap : ∀ u, swapRoot.symm u ∈ S ↔ u ∈ S := by
    intro u
    constructor
    · intro h
      have hne : swapRoot.symm u ≠ e v := fun heq => hnot (heq ▸ h)
      have hne0 : swapRoot.symm u ≠ 0 := fun heq => hzero (heq ▸ h)
      have hfix := Equiv.swap_apply_of_ne_of_ne hne hne0
      have heq : u = swapRoot.symm u := by
        calc
          u = swapRoot (swapRoot.symm u) := (swapRoot.apply_symm_apply u).symm
          _ = swapRoot.symm u := hfix
      exact heq.symm ▸ h
    · intro h
      have hne : u ≠ e v := fun heq => hnot (heq ▸ h)
      have hne0 : u ≠ 0 := fun heq => hzero (heq ▸ h)
      simpa only [swapRoot, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hne hne0] using h
  intro u
  change G.Adj v (e.symm (swapRoot.symm u)) ↔ 0 < u ∧ u ≤ 6
  calc
    _ ↔ swapRoot.symm u ∈ S := by rw [← he, Finset.mem_map_equiv, G.mem_neighborFinset]
    _ ↔ u ∈ S := hswap u
    _ ↔ _ := Finset.mem_Ioc

/-- Every candidate improving 137 edges has a root with the fixed labels
used in the rooted 138-edge search. -/
theorem exists_root_relabel_of_edge_count_gt_137
    (h41 : Ex41C4Bound) (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hfree : C4VertexExtension.C4Free G) (hedges : 137 < G.edgeFinset.card) :
    ∃ (v : Fin 42) (σ : Equiv.Perm (Fin 42)), σ v = 0 ∧
      ∀ u, G.Adj v (σ.symm u) ↔ 0 < u ∧ u ≤ 6 := by
  have hdel := deletion_count_le_132_of_ex41 h41 G hfree
  have hupper := simpleGraph_edge_count_le_138 G hdel
  have heq : G.edgeFinset.card = 138 := by omega
  obtain ⟨v, hv, _⟩ := simpleGraph_extremal_vertex_degree_six G hdel heq
  obtain ⟨σ, hroot, hn⟩ := exists_degree_six_root_relabel G v hv
  exact ⟨v, σ, hroot, hn⟩

/-- Move a candidate to an isomorphic graph whose root has the fixed
adjacencies used by the SAT encoder. -/
theorem exists_root_labelled_graph_of_edge_count_gt_137
    (h41 : Ex41C4Bound) (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hfree : C4VertexExtension.C4Free G) (hedges : 137 < G.edgeFinset.card) :
    ∃ H : SimpleGraph (Fin 42), Nonempty (G ≃g H) ∧
      ∀ u, H.Adj 0 u ↔ 0 < u ∧ u ≤ 6 := by
  obtain ⟨v, σ, hroot, hneighbors⟩ := exists_root_relabel_of_edge_count_gt_137 h41 G hfree hedges
  let H := G.comap σ.symm
  refine ⟨H, ⟨⟨σ, ?_⟩⟩, ?_⟩
  · intro a b
    change G.Adj (σ.symm (σ a)) (σ.symm (σ b)) ↔ G.Adj a b
    simp
  · intro u
    change G.Adj (σ.symm 0) (σ.symm u) ↔ 0 < u ∧ u ≤ 6
    have hz : σ.symm 0 = v := by rw [← hroot, Equiv.symm_apply_apply]
    rw [hz]
    exact hneighbors u

#print axioms exists_root_relabel_of_edge_count_gt_137
#print axioms exists_root_labelled_graph_of_edge_count_gt_137

end C4Extremal42
