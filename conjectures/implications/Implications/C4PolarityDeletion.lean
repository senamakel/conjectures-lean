import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-! Graph-level accounting for deleting points from the order-seven polarity graph. -/

namespace Implications.C4PolarityDeletion

open Finset

/-- The edge count of the graph induced on a finite vertex set. -/
noncomputable def inducedEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.induce (S : Set V)).edgeFinset.card

private theorem degree_sum_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    (hdisj : Disjoint S T) (hunion : S ∪ T = Finset.univ) :
    (∑ v ∈ T, G.degree v) + 2 * inducedEdgeCount G S =
      (∑ v ∈ S, G.degree v) + 2 * inducedEdgeCount G T := by
  classical
  have hdeg_split (v : V) : G.degree v =
      (G.neighborFinset v ∩ T).card + (G.neighborFinset v ∩ S).card := by
    rw [SimpleGraph.degree]
    have hdisj' : Disjoint (G.neighborFinset v ∩ T) (G.neighborFinset v ∩ S) :=
      hdisj.symm.mono Finset.inter_subset_right Finset.inter_subset_right
    rw [← Finset.card_union_of_disjoint hdisj', ← Finset.inter_union_distrib_left,
      Finset.union_comm T S, hunion, Finset.inter_univ]
  have hwithin (A : Finset V) :
      (∑ v ∈ A, (G.neighborFinset v ∩ A).card) =
        2 * inducedEdgeCount G A := by
    change (∑ v ∈ A, (G.neighborFinset v ∩ A).card) =
      2 * (G.induce (A : Set V)).edgeFinset.card
    rw [← (G.induce (A : Set V)).sum_degrees_eq_twice_card_edges]
    rw [← Finset.sum_coe_sort A (fun v => (G.neighborFinset v ∩ A).card)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [SimpleGraph.degree]
    refine Finset.card_bij
      (fun u hu => (⟨u, (Finset.mem_inter.mp hu).2⟩ : {x : V // x ∈ A}))
      (fun u hu => by
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
        exact (SimpleGraph.mem_neighborFinset G v.1 u).mp (Finset.mem_inter.mp hu).1)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun u hu => ⟨u.1, Finset.mem_inter.mpr
        ⟨(SimpleGraph.mem_neighborFinset G v.1 u.1).mpr
          ((SimpleGraph.mem_neighborFinset _ v u).mp hu), u.2⟩, rfl⟩)
  have hneighbor_filter (v : V) (A : Finset V) :
      (G.neighborFinset v ∩ A).card =
        ∑ u ∈ A, if G.Adj v u then 1 else 0 := by
    have hset : G.neighborFinset v ∩ A = A.filter (fun u => G.Adj v u) := by
      ext u
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hset, Finset.card_filter]
  have hcross :
      (∑ v ∈ T, (G.neighborFinset v ∩ S).card) =
        (∑ v ∈ S, (G.neighborFinset v ∩ T).card) := by
    simp_rw [hneighbor_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp [G.adj_comm]
  have hT : (∑ v ∈ T, G.degree v) =
      2 * inducedEdgeCount G T + ∑ v ∈ T, (G.neighborFinset v ∩ S).card := by
    simp_rw [hdeg_split, Finset.sum_add_distrib, hwithin T]
  have hS : (∑ v ∈ S, G.degree v) =
      (∑ v ∈ S, (G.neighborFinset v ∩ T).card) + 2 * inducedEdgeCount G S := by
    simp_rw [hdeg_split, Finset.sum_add_distrib, hwithin S]
  rw [hT, hS, hcross]
  ring

/-- An order-seven polarity graph has 57 points, 224 edges, eight absolute points,
and degree seven at absolute points and eight elsewhere. -/
def HasOrderSevenPolarityProfile {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Prop :=
  Fintype.card V = 57 ∧ A.card = 8 ∧ G.edgeFinset.card = 224 ∧
    ∀ v, G.degree v = if v ∈ A then 7 else 8

/-- Deleting 15 vertices retains `104 + e(D) + |D ∩ A|` edges in any graph with
an order-seven polarity degree profile. Here `e(D)` is the edge count induced on
exactly the deleted vertices. -/
theorem retained_edge_count_eq_104_add_deleted_score
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A D : Finset V)
    (hprofile : HasOrderSevenPolarityProfile G A) (hD : D.card = 15) :
    inducedEdgeCount G (Finset.univ \ D) =
      104 + inducedEdgeCount G D + (D ∩ A).card := by
  classical
  rcases hprofile with ⟨_hV, _hA, hE, hdeg⟩
  let R := Finset.univ \ D
  have hdisj : Disjoint R D := by
    apply Finset.disjoint_left.mpr
    intro v hvR hvD
    exact (Finset.mem_sdiff.mp hvR).2 hvD
  have hunion : R ∪ D = Finset.univ := by
    ext v
    simp [R]
  have hpart := degree_sum_partition G R D hdisj hunion
  have htotal :
      (∑ v ∈ D, G.degree v) + (∑ v ∈ R, G.degree v) =
        2 * G.edgeFinset.card := by
    calc
      (∑ v ∈ D, G.degree v) + (∑ v ∈ R, G.degree v) =
          (∑ v ∈ R, G.degree v) + (∑ v ∈ D, G.degree v) := by ring
      _ = ∑ v ∈ R ∪ D, G.degree v := (Finset.sum_union hdisj).symm
      _ = ∑ v, G.degree v := by rw [hunion]
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hdeg_form (v : V) :
      G.degree v = 8 - (if v ∈ A then 1 else 0) := by
    rw [hdeg]
    split_ifs <;> omega
  have hdegsum :
      (∑ v ∈ D, G.degree v) + (D ∩ A).card = 120 := by
    have hsum := Finset.sum_tsub_distrib D
      (f := fun _ : V => 8) (g := fun v => if v ∈ A then 1 else 0)
      (by intro v hv; split_ifs <;> omega)
    have hcount : (∑ v ∈ D, if v ∈ A then 1 else 0) = (D ∩ A).card := by
      rw [← Finset.card_filter]
      congr 1
    calc
      (∑ v ∈ D, G.degree v) + (D ∩ A).card =
          (∑ v ∈ D, (8 - (if v ∈ A then 1 else 0))) + (D ∩ A).card := by
        congr 1
        exact Finset.sum_congr rfl fun v _ => hdeg_form v
      _ = (∑ _v ∈ D, (8 : ℕ)) -
          (∑ v ∈ D, if v ∈ A then 1 else 0) + (D ∩ A).card := by rw [hsum]
      _ = 8 * D.card - (D ∩ A).card + (D ∩ A).card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hcount]
        omega
      _ = 120 := by rw [hD]; omega
  have hcountRelation :
      inducedEdgeCount G R + (∑ v ∈ D, G.degree v) =
        G.edgeFinset.card + inducedEdgeCount G D := by
    omega
  have hresult :
      inducedEdgeCount G R = 104 + inducedEdgeCount G D + (D ∩ A).card := by
    rw [hE] at hcountRelation
    omega
  simpa [R] using hresult

/-- If every one-vertex deletion of a 42-vertex graph has at most 132 edges
and the graph has 138 edges, every vertex has degree at least six. -/
theorem min_degree_six_of_delete_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hV : Fintype.card V = 42)
    (hE : G.edgeFinset.card = 138)
    (hDel : ∀ v, (G.induce ({v}ᶜ : Set V)).edgeFinset.card ≤ 132) :
    ∀ v, 6 ≤ G.degree v := by
  intro v
  have hdel := hDel v
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet] at hdel
  omega

#print axioms retained_edge_count_eq_104_add_deleted_score
#print axioms min_degree_six_of_delete_bound

end Implications.C4PolarityDeletion
