import Implications.C4PolarityOrderSeven
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Lex

/-! Lexicographic normalization of polarity deletion candidates. -/

namespace C4PolarityCanonical

open C4PolarityOrderSeven Implications.C4PolarityDeletion

/-- The deletion indicator string in the order used by the SAT encoder. -/
def deletionBits (D : Finset (Fin 57)) : List Bool :=
  (List.finRange 57).map fun i => decide (i ∈ D)

/-- The graph condition whose witnesses are normalized by symmetry. -/
def Candidate (D : Finset (Fin 57)) : Prop :=
  D.card = 15 ∧ 138 ≤ inducedEdgeCount graph (Finset.univ \ D)

private theorem complement_image_bijOn (D : Finset (Fin 57)) (e : graph ≃g graph) :
    Set.BijOn e (↑(Finset.univ \ D) : Set (Fin 57))
      (↑(Finset.univ \ D.image e) : Set (Fin 57)) := by
  refine ⟨?_, e.injective.injOn, ?_⟩
  · intro x hx
    have hnot := (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro himage
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp himage
    exact hnot ((e.injective hxy) ▸ hy)
  · intro y hy
    have hnot := (Finset.mem_sdiff.mp hy).2
    refine ⟨e.symm y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩,
      e.apply_symm_apply y⟩
    intro hpre
    exact hnot (Finset.mem_image.mpr ⟨e.symm y, hpre, e.apply_symm_apply y⟩)

/-- Deleting the image of a set under a graph automorphism preserves the candidate
conditions. -/
theorem candidate_image (D : Finset (Fin 57)) (e : graph ≃g graph)
    (hD : Candidate D) : Candidate (D.image e) := by
  obtain ⟨hcard, he⟩ := hD
  refine ⟨(Finset.card_image_of_injective D e.injective).trans hcard, ?_⟩
  have hEq := (e.induce (complement_image_bijOn D e)).card_edgeFinset_eq
  change inducedEdgeCount graph (Finset.univ \ D) =
    inducedEdgeCount graph (Finset.univ \ D.image e) at hEq
  exact he.trans (le_of_eq hEq)

/-- The symmetry constraints admit a lexicographically maximal candidate whenever
any candidate exists. The theorem holds for every graph automorphism, so it
also holds for the subset used by the encoder. -/
theorem exists_lex_max_candidate (h : ∃ D, Candidate D) :
    ∃ D, Candidate D ∧ ∀ e : graph ≃g graph, deletionBits (D.image e) ≤ deletionBits D := by
  classical
  let candidates := Finset.univ.filter Candidate
  obtain ⟨D, hD⟩ := h
  have hne : candidates.Nonempty := ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image candidates deletionBits hne
  have hMc := (Finset.mem_filter.mp hM).2
  exact ⟨M, hMc, fun e =>
    hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, candidate_image M e hMc⟩)⟩

/-- Reading the bits at the forward image of each index, as the encoder does,
is equivalent to taking the indicator string of the inverse image. -/
theorem deletionBits_image_symm (D : Finset (Fin 57)) (e : graph ≃g graph) :
    deletionBits (D.image e.symm) = (List.finRange 57).map (fun i => decide (e i ∈ D)) := by
  unfold deletionBits
  apply List.map_congr_left
  intro i _
  have hm : i ∈ D.image e.symm ↔ e i ∈ D := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have h := congrArg e hji
      rw [e.apply_symm_apply] at h
      exact h ▸ hj
    · intro hi
      exact Finset.mem_image.mpr ⟨e i, hi, e.symm_apply_apply i⟩
  simp [hm]

/-- Any 138-edge candidate yields a 15-point deletion set of score at least
34 whose indicator string meets every graph-automorphism lexicographic constraint. -/
theorem exists_canonical_deletion_score (h : ∃ D, Candidate D) :
    ∃ D : Finset (Fin 57), Candidate D ∧
      34 ≤ inducedEdgeCount graph D + (D ∩ absolute).card ∧
      ∀ e : graph ≃g graph,
        (List.finRange 57).map (fun i => decide (e i ∈ D)) ≤ deletionBits D := by
  obtain ⟨D, ⟨hD, hE⟩, hmax⟩ := exists_lex_max_candidate h
  refine ⟨D, ⟨hD, hE⟩, ?_, ?_⟩
  · rw [retained_edge_count D hD] at hE
    omega
  · intro e
    rw [← deletionBits_image_symm]
    exact hmax e.symm

#print axioms exists_canonical_deletion_score
#print axioms exists_lex_max_candidate

end C4PolarityCanonical
