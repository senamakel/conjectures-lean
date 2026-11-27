import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Implications.C4VertexExtension
import Implications.C4Extremal42

/-!
# Degree constraints in finite C4-free graphs

In a C4-free graph, the neighborhoods of the neighbors of a vertex, with that
vertex removed, are pairwise disjoint.  This gives a general degree window
from any lower bound on all degrees.  At order 42, a degree-eight vertex has
neighbor degree excess at most one above the all-six baseline.  Also, the
subgraph induced on any vertex neighborhood has maximum degree at most one.
-/

namespace C4DegreeBounds

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def outerNeighbors (u v : V) : Finset V := (G.neighborFinset u).erase v

/-- Neighbors of `u` which are also neighbors of the center `v`. -/
private def innerNeighbors (u v : V) : Finset V :=
  (G.neighborFinset u).filter fun w => w ∈ G.neighborFinset v

private def externalNeighbors (u v : V) : Finset V :=
  outerNeighbors G u v \ innerNeighbors G u v

theorem outerNeighbors_disjoint {v u w : V}
    (hC4 : C4VertexExtension.C4Free G)
    (hu : u ∈ G.neighborFinset v) (hw : w ∈ G.neighborFinset v) (huw : u ≠ w) :
    Disjoint (outerNeighbors G u v) (outerNeighbors G w v) := by
  rw [Finset.disjoint_left]
  intro z hzu hzw
  have hzu' : z ≠ v ∧ G.Adj u z := by
    change z ∈ (G.neighborFinset u).erase v at hzu
    rcases Finset.mem_erase.mp hzu with ⟨hzv, hzu⟩
    exact ⟨hzv, by simpa using hzu⟩
  have hzw' : z ≠ v ∧ G.Adj w z := by
    change z ∈ (G.neighborFinset w).erase v at hzw
    rcases Finset.mem_erase.mp hzw with ⟨hzv, hzw⟩
    exact ⟨hzv, by simpa using hzw⟩
  have huv : G.Adj u v := G.symm.symm v u (by simpa using hu)
  have hwv : G.Adj w v := G.symm.symm v w (by simpa using hw)
  have hnot := hC4 (x := u) (y := w) (z := v) (w := z) huw hzw'.1.symm huv hwv
  exact hnot ⟨hzu'.2, hzw'.2⟩

/-- The C4 condition forces the graph induced on the neighborhood of a vertex
to have maximum degree at most one: each neighbor has at most one neighbor
inside that neighborhood. -/
theorem innerNeighbors_card_le_one {v u : V}
    (hC4 : C4VertexExtension.C4Free G)
    (hu : u ∈ G.neighborFinset v) :
    (innerNeighbors G u v).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro w hw z hz
  have hw' : w ∈ G.neighborFinset u ∧ w ∈ G.neighborFinset v :=
    Finset.mem_filter.mp hw
  have hz' : z ∈ G.neighborFinset u ∧ z ∈ G.neighborFinset v :=
    Finset.mem_filter.mp hz
  by_contra hwz
  have hwu : G.Adj u w := by simpa using hw'.1
  have hvw : G.Adj v w := by
    simpa using hw'.2
  have hzu : G.Adj u z := by simpa using hz'.1
  have hvz : G.Adj v z := by
    simpa using hz'.2
  have hvu : v ≠ u := G.ne_of_adj (by simpa using hu)
  have hnot := hC4 (x := v) (y := u) (z := w) (w := z) hvu hwz hvw hwu
  exact hnot ⟨hvz, hzu⟩

/-- For a degree-eight vertex in a 42-vertex C4-free graph of minimum degree
six, the total number of edges induced by its neighborhood, counted by their
endpoint, is at least seven. -/
theorem sum_innerNeighbors_card_ge_seven (v : V)
    (hcard : Fintype.card V = 42)
    (hmin : ∀ u, 6 ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G)
    (hv : G.degree v = 8) :
    7 ≤ ∑ u ∈ G.neighborFinset v, (innerNeighbors G u v).card := by
  classical
  let S := G.neighborFinset v
  let T := fun u => externalNeighbors G u v
  have hScard : S.card = 8 := by
    simpa [S, G.card_neighborFinset_eq_degree] using hv
  have hSsub : S ⊆ Finset.univ.erase v := by
    intro z hz
    have hzv : z ≠ v := G.ne_of_adj (G.symm.symm v z (by simpa using hz))
    exact Finset.mem_erase.mpr ⟨hzv, Finset.mem_univ _⟩
  have hdisj : (S : Set V).PairwiseDisjoint T := by
    intro u hu w hw huw
    apply Finset.disjoint_left.mpr
    intro z hzu hzw
    have hzu' : z ∈ outerNeighbors G u v := (Finset.mem_sdiff.mp hzu).1
    have hzw' : z ∈ outerNeighbors G w v := (Finset.mem_sdiff.mp hzw).1
    exact (Finset.disjoint_left.mp (outerNeighbors_disjoint G hC4 hu hw huw)) hzu' hzw'
  let U := S.biUnion T
  have hUsub : U ⊆ Finset.univ.erase v \ S := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨u, hu, huz⟩
    have huzOuter : z ∈ outerNeighbors G u v := (Finset.mem_sdiff.mp huz).1
    have hzv : z ≠ v := (Finset.mem_erase.mp huzOuter).1
    have hzS : z ∉ S := by
      intro hzS
      have hzu : z ∈ innerNeighbors G u v := by
        apply Finset.mem_filter.mpr
        exact ⟨by
          have := (Finset.mem_erase.mp huzOuter).2
          simpa using this, hzS⟩
      exact (Finset.mem_sdiff.mp huz).2 hzu
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hzv, Finset.mem_univ _⟩, hzS⟩
  have hUcard : U.card ≤ 33 := by
    have hcardU := Finset.card_le_card hUsub
    have hcomp : (Finset.univ.erase v \ S).card = 33 := by
      rw [Finset.card_sdiff_of_subset hSsub]
      simp [hcard, hScard]
    omega
  have hexternal : (∑ u ∈ S, (T u).card) ≤ 33 := by
    have hsum : (∑ u ∈ S, (T u).card) = U.card := by
      dsimp [U]
      exact (Finset.card_biUnion hdisj).symm
    omega
  have htotalLower : 40 ≤ ∑ u ∈ S, (outerNeighbors G u v).card := by
    have hterm : ∀ u ∈ S, 5 ≤ (outerNeighbors G u v).card := by
      intro u hu
      have huv : v ∈ G.neighborFinset u := by
        have huv' : G.Adj v u := by simpa [S] using hu
        simpa using G.symm.symm v u huv'
      have hcardOuter : (outerNeighbors G u v).card = G.degree u - 1 := by
        change #((G.neighborFinset u).erase v) = G.degree u - 1
        rw [Finset.card_erase_of_mem huv, G.card_neighborFinset_eq_degree]
      rw [hcardOuter]
      have := hmin u
      omega
    have := Finset.sum_le_sum (s := S) (fun u hu => hterm u hu)
    rw [Finset.sum_const, nsmul_eq_mul, hScard] at this
    norm_num at this ⊢
    exact this
  have hpartition :
      (∑ u ∈ S, (outerNeighbors G u v).card) =
        (∑ u ∈ S, (T u).card) +
          (∑ u ∈ S, (innerNeighbors G u v).card) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [T, externalNeighbors]
    have hsub : innerNeighbors G u v ⊆ outerNeighbors G u v := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨hzu, hzv⟩
      have hz_ne_v : z ≠ v := by
        intro hz
        subst z
        have : G.Adj v v := by simpa using hzv
        exact G.loopless.irrefl v this
      exact Finset.mem_erase.mpr ⟨hz_ne_v, by simpa using hzu⟩
    exact (Finset.card_sdiff_add_card_eq_card hsub).symm
  omega

theorem sum_outerNeighbors_card_le (v : V)
    (hC4 : C4VertexExtension.C4Free G) :
    (∑ u ∈ G.neighborFinset v, (outerNeighbors G u v).card) ≤ Fintype.card V - 1 := by
  classical
  let S := G.neighborFinset v
  let T := fun u => outerNeighbors G u v
  have hdisj : (S : Set V).PairwiseDisjoint T := by
    intro u hu w hw huw
    exact outerNeighbors_disjoint G hC4 hu hw huw
  have hsubset : S.biUnion T ⊆ Finset.univ.erase v := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨u, hu, huz⟩
    change z ∈ (G.neighborFinset u).erase v at huz
    have hzv : z ≠ v := (Finset.mem_erase.mp huz).1
    exact Finset.mem_erase.mpr ⟨hzv, Finset.mem_univ z⟩
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
      have huv' : G.Adj v u := by simpa using hu
      simpa using G.symm.symm v u huv'
    have hcard : (outerNeighbors G u v).card = G.degree u - 1 := by
      change #((G.neighborFinset u).erase v) = G.degree u - 1
      rw [Finset.card_erase_of_mem huv, G.card_neighborFinset_eq_degree]
    rw [hcard]
    have hmu := hmin u
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
      change u ∈ G.neighborFinset v at hu
      have huv : v ∈ G.neighborFinset u := by
        have huv' : G.Adj v u := by simpa using hu
        simpa using G.symm.symm v u huv'
      change #((G.neighborFinset u).erase v) = G.degree u - 1
      rw [Finset.card_erase_of_mem huv, G.card_neighborFinset_eq_degree]
    calc
      (∑ u ∈ S, (G.degree u - 1)) = ∑ u ∈ S, (outerNeighbors G u v).card := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (hcards u hu).symm
      _ ≤ 41 := by simpa [S, hcard] using houter
  have hdegreeSum : (∑ u ∈ S, G.degree u) ≤ 49 := by
    have hidentity :
        (∑ u ∈ S, G.degree u) = (∑ u ∈ S, (G.degree u - 1)) + S.card := by
      calc
        (∑ u ∈ S, G.degree u) = ∑ u ∈ S, ((G.degree u - 1) + 1) := by
          apply Finset.sum_congr rfl
          intro u hu
          have hmu := hmin u
          omega
        _ = (∑ u ∈ S, (G.degree u - 1)) + S.card := by simp [Finset.sum_add_distrib]
    have hScard : S.card = 8 := by simpa [S, G.card_neighborFinset_eq_degree] using hv
    calc
      (∑ u ∈ S, G.degree u) = (∑ u ∈ S, (G.degree u - 1)) + 8 := by
        rw [hidentity, hScard]
      _ ≤ 41 + 8 := by omega
      _ = 49 := by omega
  have hexcessIdentity :
      (∑ u ∈ S, G.degree u) = (∑ u ∈ S, (G.degree u - 6)) + S.card * 6 := by
    calc
      (∑ u ∈ S, G.degree u) = ∑ u ∈ S, ((G.degree u - 6) + 6) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hmu := hmin u
        omega
      _ = (∑ u ∈ S, (G.degree u - 6)) + S.card * 6 := by simp [Finset.sum_add_distrib, Nat.mul_comm]
  have hScard : S.card = 8 := by simpa [S, G.card_neighborFinset_eq_degree] using hv
  calc
    (∑ u ∈ S, (G.degree u - 6)) ≤ 1 := by
      have hrew : (∑ u ∈ S, G.degree u) = (∑ u ∈ S, (G.degree u - 6)) + 8 * 6 := by
        rw [hexcessIdentity, hScard]
      have hbound : (∑ u ∈ S, (G.degree u - 6)) + 8 * 6 ≤ 49 := by
        rw [← hrew]
        exact hdegreeSum
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
    exact Finset.single_le_sum (f := fun w => G.degree w - 6)
      (fun w hw => Nat.zero_le _) hu
  omega

/-- Every neighbor of a degree-eight vertex has degree six or seven; together
with the excess bound, at most one of the neighbors can have degree seven. -/
theorem neighbor_degree_eq_six_or_seven_of_degree_eight (v : V)
    (hcard : Fintype.card V = 42)
    (hmin : ∀ u, 6 ≤ G.degree u)
    (hC4 : C4VertexExtension.C4Free G)
    (hv : G.degree v = 8)
    {u : V} (hu : u ∈ G.neighborFinset v) :
    G.degree u = 6 ∨ G.degree u = 7 := by
  have hlow := hmin u
  have hhigh := neighbor_degree_le_seven_of_degree_eight G v hcard hmin hC4 hv hu
  omega

/-- Under the 41-vertex deletion bound, a 42-vertex graph with 138 edges has
minimum degree six. If it is C4-free, the generic degree window also gives
maximum degree eight. -/
theorem degree_window_of_extremal_42 (G : SimpleGraph (Fin 42))
    [DecidableRel G.Adj]
    (hDel : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (he : G.edgeFinset.card = 138)
    (hC4 : C4VertexExtension.C4Free G) :
    ∀ v, 6 ≤ G.degree v ∧ G.degree v ≤ 8 := by
  intro v
  have hminAll : ∀ u, 6 ≤ G.degree u := by
    intro u
    have hd := C4Extremal42.inducedDeletionCount_eq G u
    have h := hDel u
    rw [hd] at h
    rw [he] at h
    omega
  have hmax := degree_le_eight_of_card_eq_42 G v (by simp) hminAll hC4
  exact ⟨hminAll v, hmax⟩

#print axioms degree_window_bound
#print axioms innerNeighbors_card_le_one
#print axioms neighbor_degree_excess_le_one_of_degree_eight
#print axioms neighbor_degree_le_seven_of_degree_eight
#print axioms degree_window_of_extremal_42

end C4DegreeBounds
