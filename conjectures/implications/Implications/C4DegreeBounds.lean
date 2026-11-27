import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Implications.C4VertexExtension

/-!
# Degree constraints in finite C4-free graphs

In a C4-free graph, the neighborhoods of the neighbors of a vertex, with that
vertex removed, are pairwise disjoint.  This gives a general degree window
from any lower bound on all degrees.  At order 42, a degree-eight vertex has
neighbor degree excess at most one above the all-six baseline.
-/

namespace C4DegreeBounds

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def outerNeighbors (u v : V) : Finset V := (G.neighborFinset u).erase v

theorem outerNeighbors_disjoint {v u w : V}
    (hC4 : C4VertexExtension.C4Free G)
    (hu : u ∈ G.neighborFinset v) (hw : w ∈ G.neighborFinset v) (huw : u ≠ w) :
    Disjoint (outerNeighbors G u v) (outerNeighbors G w v) := by
  rw [Finset.disjoint_left]
  intro z hzu hzw
  have hzu' : z ∈ G.neighborFinset u ∧ z ≠ v := by
    simpa [outerNeighbors] using hzu
  have hzw' : z ∈ G.neighborFinset w ∧ z ≠ v := by
    simpa [outerNeighbors] using hzw
  have huv : G.Adj u v := G.mem_neighborFinset.mp hu
  have hwv : G.Adj w v := G.mem_neighborFinset.mp hw
  have hnot := hC4 huw hzw'.2.symm huv hwv
  exact hnot ⟨G.mem_neighborFinset.mp hzu'.1, G.mem_neighborFinset.mp hzw'.1⟩

theorem sum_outerNeighbors_card_le (v : V)
    (hC4 : C4VertexExtension.C4Free G) :
    (∑ u ∈ G.neighborFinset v, (outerNeighbors G u v).card) ≤ Fintype.card V - 1 := by
  classical
  let S := G.neighborFinset v
  let T := outerNeighbors G · v
  have hdisj : (S : Set V).PairwiseDisjoint T := by
    intro u hu w hw huw
    exact outerNeighbors_disjoint G hC4 hu hw huw
  have hsubset : S.biUnion T ⊆ Finset.univ.erase v := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨u, hu, huz⟩
    have hz' : z ∈ G.neighborFinset u ∧ z ≠ v := by
      simpa [T, outerNeighbors] using huz
    simp [hz'.2]
  calc
    (∑ u ∈ G.neighborFinset v, (outerNeighbors G u v).card) = #(S.biUnion T) := by
      simp only [S, T]
      exact (Finset.card_biUnion hdisj).symm
    _ ≤ #(Finset.univ.erase v) := Finset.card_le_card hsubset
    _ = Fintype.card V - 1 := by simp

theorem degree_window_bound (v : V) (m : ℕ) (hm : 2 ≤ m)
    (hmin : ∀ u, m ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G) :
    (m - 1) * G.degree v ≤ Fintype.card V - 1 := by
  classical
  have hsum := sum_outerNeighbors_card_le G v hC4
  have hlower : ∀ u ∈ G.neighborFinset v, m - 1 ≤ (outerNeighbors G u v).card := by
    intro u hu
    have huv : v ∈ G.neighborFinset u := by
      rw [G.mem_neighborFinset]
      exact G.symm (G.mem_neighborFinset.mp hu)
    have hcard : (outerNeighbors G u v).card = G.degree u - 1 := by
      simp [outerNeighbors, G.card_neighborFinset_eq_degree, huv]
    rw [hcard]
    omega
  calc
    (m - 1) * G.degree v = ∑ u ∈ G.neighborFinset v, (m - 1) := by
      simp [G.card_neighborFinset_eq_degree, Nat.mul_comm]
    _ ≤ ∑ u ∈ G.neighborFinset v, (outerNeighbors G u v).card :=
      Finset.sum_le_sum fun u hu => hlower u hu
    _ ≤ Fintype.card V - 1 := hsum

theorem degree_le_eight_of_card_eq_42 (v : V)
    (hcard : Fintype.card V = 42)
    (hmin : ∀ u, 6 ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G) :
    G.degree v ≤ 8 := by
  have h := degree_window_bound G v 6 (by omega) hmin hC4
  omega

theorem neighbor_degree_excess_le_one_of_degree_eight (v : V)
    (hcard : Fintype.card V = 42)
    (hmin : ∀ u, 6 ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G)
    (hv : G.degree v = 8) :
    (∑ u ∈ G.neighborFinset v, (G.degree u - 6)) ≤ 1 := by
  classical
  let S := G.neighborFinset v
  have houter := sum_outerNeighbors_card_le G v hC4
  have houterDegree : (∑ u ∈ S, (G.degree u - 1)) ≤ 41 := by
    have hcards : ∀ u ∈ S, (outerNeighbors G u v).card = G.degree u - 1 := by
      intro u hu
      have huv : v ∈ G.neighborFinset u := by
        rw [G.mem_neighborFinset]
        exact G.symm (G.mem_neighborFinset.mp hu)
      simp [outerNeighbors, G.card_neighborFinset_eq_degree, huv]
    simpa [S, hcard, hcards] using houter
  have hdegreeSum : (∑ u ∈ S, G.degree u) ≤ 49 := by
    have hidentity :
        (∑ u ∈ S, G.degree u) = (∑ u ∈ S, (G.degree u - 1)) + S.card := by
      rw [← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      omega
    rw [hidentity, G.card_neighborFinset_eq_degree, hv] at houterDegree
    omega
  have hexcessIdentity :
      (∑ u ∈ S, G.degree u) = (∑ u ∈ S, (G.degree u - 6)) + S.card * 6 := by
    rw [← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    omega
  rw [hexcessIdentity, G.card_neighborFinset_eq_degree, hv] at hdegreeSum
  omega

theorem neighbor_degree_le_seven_of_degree_eight (v : V)
    (hcard : Fintype.card V = 42)
    (hmin : ∀ u, 6 ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G)
    (hv : G.degree v = 8)
    {u : V} (hu : u ∈ G.neighborFinset v) :
    G.degree u ≤ 7 := by
  have hsum := neighbor_degree_excess_le_one_of_degree_eight G v hcard hmin hC4 hv
  have hsingle : G.degree u - 6 ≤ ∑ w ∈ G.neighborFinset v, (G.degree w - 6) := by
    exact Finset.single_le_sum (fun w hw => Nat.zero_le _) hu
  omega

#print axioms degree_window_bound
#print axioms neighbor_degree_excess_le_one_of_degree_eight
#print axioms neighbor_degree_le_seven_of_degree_eight

end C4DegreeBounds
