import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Implications.C4VertexExtension
import Implications.C4DegreeBounds

/-!
# A degree-eight cap from C4 codegree moments

In a 42-vertex C4-free graph with all degrees at least six, let `k` be the
number of degree-eight vertices and let `a x` count their neighbors at an
outside vertex `x`.  The graph argument gives `∑ a = 8k` and
`∑ (a² - a) ≤ k(k - 1)`: each ordered pair of distinct degree-eight vertices
has at most one common neighbor.  Cauchy–Schwarz then rules out `k ≥ 8`.

This module formalizes the moment-to-cap reduction.  Its hypotheses are the
two codegree-counting conclusions, so it can be checked independently of the
graph-theoretic bridge that supplies them.
-/

namespace C4DegreeEightCap

private theorem twice_union_card_add_square_bound {V : Type*} [Fintype V]
    [DecidableEq V] (S : Finset V) (f : V → Finset V)
    (hcard : ∀ u ∈ S, (f u).card = 8)
    (hinter : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (f u ∩ f v).card ≤ 1) :
    16 * S.card ≤ 2 * (S.biUnion f).card + S.card * (S.card - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hcarda := hcard a (Finset.mem_insert_self ..)
    have hcardS : ∀ u ∈ S, (f u).card = 8 := by
      intro u hu
      exact hcard u (Finset.mem_insert_of_mem hu)
    have hinterS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (f u ∩ f v).card ≤ 1 := by
      intro u hu v hv huv
      exact hinter u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv
    have hintera : ∀ v ∈ S, (f a ∩ f v).card ≤ 1 := by
      intro v hv
      exact hinter a (Finset.mem_insert_self ..) v (Finset.mem_insert_of_mem hv)
        (by intro h; subst v; exact ha hv)
    let U := S.biUnion f
    have hsub : f a ∩ U ⊆ S.biUnion (fun v => f a ∩ f v) := by
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxa, hxU⟩
      rcases Finset.mem_biUnion.mp hxU with ⟨v, hv, hxv⟩
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_inter.mpr ⟨hxa, hxv⟩⟩
    have hinterCard : (f a ∩ U).card ≤ S.card := by
      calc
        (f a ∩ U).card ≤ (S.biUnion fun v => f a ∩ f v).card := Finset.card_le_card hsub
        _ ≤ ∑ v ∈ S, (f a ∩ f v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum fun v hv => hintera v hv
        _ = S.card := by simp
    have hUnion : (insert a S).biUnion f = f a ∪ U := by
      simp [U, Finset.biUnion_insert, ha]
    have hUnionCard := Finset.card_union_add_card_inter (f a) U
    rw [hUnion] at hUnionCard
    have hcardInsert : (insert a S).card = S.card + 1 := by simp [ha]
    rw [hcardInsert]
    have hprev := ih hcardS hinterS
    nlinarith [hcarda, hinterCard, hUnionCard]

/-- A C4-free graph cannot have eight degree-eight vertices when all degrees
are at least six and the graph has 42 vertices. -/
theorem degree_eight_count_le_seven (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hmin : ∀ v, 6 ≤ G.degree v)
    (hC4 : C4VertexExtension.C4Free G) :
    (Finset.univ.filter fun v => G.degree v = 8).card ≤ 7 := by
  classical
  let D := Finset.univ.filter fun v => G.degree v = 8
  by_contra hnot
  have hD : 8 ≤ D.card := by omega
  obtain ⟨S, hSD, hS⟩ := Finset.exists_subset_card_eq hD
  have hSdeg : ∀ u ∈ S, G.degree u = 8 := by
    intro u hu
    exact (Finset.mem_filter.mp (hSD hu)).2
  have hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
    intro u hu v hv huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hux : G.Adj u x := by simpa using (Finset.mem_inter.mp hx).1
    have hvx : G.Adj v x := by simpa using (Finset.mem_inter.mp hx).2
    have huy : G.Adj u y := by simpa using (Finset.mem_inter.mp hy).1
    have hvy : G.Adj v y := by simpa using (Finset.mem_inter.mp hy).2
    exact hC4 huv hxy hux hvx ⟨huy, hvy⟩
  have hUnionLower := twice_union_card_add_square_bound S G.neighborFinset hSdeg hpair
  have hUnionSize : 36 ≤ (S.biUnion G.neighborFinset).card := by
    rw [hS] at hUnionLower
    norm_num at hUnionLower ⊢
    omega
  have hnotD : S.biUnion G.neighborFinset ⊆ Finset.univ \ D := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨u, hu, hux⟩
    have huD := hSD hu
    have huDeg := (Finset.mem_filter.mp huD).2
    have huxAdj : G.Adj u x := by simpa using hux
    have hxnot : x ∉ D := by
      intro hxD
      have hxDeg := (Finset.mem_filter.mp hxD).2
      have hdegreeBound := C4DegreeBounds.neighbor_degree_le_seven_of_degree_eight
        G x (by simp) hmin hC4 hxDeg (G.mem_neighborFinset x u).mpr (G.symm.symm u x huxAdj)
      omega
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxnot⟩
  have hUnionUpper : (S.biUnion G.neighborFinset).card ≤ 42 - D.card := by
    calc
      _ ≤ (Finset.univ \ D).card := Finset.card_le_card hnotD
      _ = 42 - D.card := by simp [D]
  omega

/-- The first and second codegree moments for degree-eight vertices in a
42-vertex C4-free graph force their count to be at most seven.

Here `n` is the number of vertices outside the degree-eight set and `a x` is
the number of degree-eight neighbors of outside vertex `x`. -/
theorem count_le_seven_of_codegree_moments
    (k n : ℕ) (a : Fin n → ℝ)
    (hk : 0 < k)
    (hsize : n + k = 42)
    (hfirst : Finset.univ.sum a = 8 * (k : ℝ))
    (hsecond : Finset.univ.sum (fun x => a x ^ 2 - a x) ≤
      (k : ℝ) * ((k : ℝ) - 1)) :
    k ≤ 7 := by
  have hsumSq : Finset.univ.sum (fun x => a x ^ 2) ≤
      (k : ℝ) * ((k : ℝ) + 7) := by
    have hsecond' := hsecond
    rw [Finset.sum_sub_distrib] at hsecond'
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hfirst] at hcs
  have hcs' : (8 * (k : ℝ)) ^ 2 ≤ (n : ℝ) * ((k : ℝ) * ((k : ℝ) + 7)) := by
    exact hcs.trans (mul_le_mul_of_nonneg_left hsumSq (Nat.cast_nonneg n))
  have hcancel : (k : ℝ) * (64 * (k : ℝ)) ≤
      (k : ℝ) * ((n : ℝ) * ((k : ℝ) + 7)) := by
    nlinarith [hcs']
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hlinear : 64 * (k : ℝ) ≤ (n : ℝ) * ((k : ℝ) + 7) := by
    by_contra hnot
    have hpos : 0 < 64 * (k : ℝ) - (n : ℝ) * ((k : ℝ) + 7) := by linarith
    have hmul := mul_pos hkpos hpos
    nlinarith
  have hkn : (n : ℝ) + (k : ℝ) = 42 := by exact_mod_cast hsize
  have hk8 : ¬ 8 ≤ k := by
    intro hk8
    have hk8' : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk8
    nlinarith
  omega

end C4DegreeEightCap

#print axioms C4DegreeEightCap.count_le_seven_of_codegree_moments
