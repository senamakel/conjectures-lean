import Implications.C4PolarityEncoderInputs
import Implications.C4VertexExtension
import Mathlib.Tactic

/-!
# The 41-vertex input for the polarity deletion encoding

The exact extremal result `ex(41, C4) = 132` is Yancun Yan,
*The Turán number ex(41; C4) equals 132*, Zenodo version 1.0,
published 2026-10-15, DOI <https://doi.org/10.5281/zenodo.23334622>
(concept DOI <https://doi.org/10.5281/zenodo.23334621>). Its upper bound uses
counting and SAT certificates checked by LRAT. The theorem below keeps this
published result as an explicit input; this file proves the transport from
that general bound to each induced 41-vertex survivor graph.
-/

namespace Implications.C4PolaritySurvivorBound

open Implications.C4PolarityEncoderInputs

/-- The cited ex(41, C4) upper bound, stated for arbitrary finite Lean graphs.
This is an explicit tier-H input until Yan's supplementary LRAT certificate is
formalized or imported into Lean. -/
def Ex41C4Bound : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj],
    Fintype.card α = 41 →
      C4VertexExtension.C4Free G → G.edgeSet.ncard ≤ 132

theorem c4Free_induce {α : Type*} (G : SimpleGraph α)
    (hG : C4VertexExtension.C4Free G) (s : Set α) :
    C4VertexExtension.C4Free (G.induce s) := by
  intro x y z w hxy hzw hxz hyz htwo
  apply hG (x := x.val) (y := y.val) (z := z.val) (w := w.val)
  · intro hval
    exact hxy (Subtype.ext hval)
  · intro hval
    exact hzw (Subtype.ext hval)
  · simpa only [SimpleGraph.induce_adj] using hxz
  · simpa only [SimpleGraph.induce_adj] using hyz
  · simpa only [SimpleGraph.induce_adj] using htwo

/-- Assuming the published general 41-vertex C4-free edge bound, every
one-vertex deletion from the 42-vertex survivor graph has at most 132 edges.
The outer theorem is conditional precisely on `Ex41C4Bound`; no literature
statement is silently treated as a Lean axiom. -/
theorem survivorDeletionBound_of_ex41C4Bound
    (hEx41 : Ex41C4Bound) (D : Finset (Fin 57))
    (hCand : C4PolarityCanonical.Candidate D) :
    SurvivorDeletionBound D := by
  classical
  intro v
  let R : Finset (Fin 57) := Finset.univ \ D
  let H := C4PolarityOrderSeven.graph.induce (R : Set (Fin 57))
  let K := H.induce ({v}ᶜ : Set {i // i ∈ R})
  have hRcard : R.card = 42 := by
    change (Finset.univ \ D).card = 42
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
    simp [hCand.1]
  have hHcard : Fintype.card {i // i ∈ R} = 42 := by
    simpa only [Fintype.card_coe] using hRcard
  have hKcard : Fintype.card {i : {i // i ∈ R} // i ∈ ({v}ᶜ : Set {i // i ∈ R})} = 41 := by
    change Fintype.card {i : {i // i ∈ R} // i ≠ v} = 41
    have hcard := Fintype.card_subtype_compl (p := fun i : {i // i ∈ R} => i = v)
    simpa [hHcard] using hcard
  have hHfree := c4Free_induce C4PolarityOrderSeven.graph
    C4PolarityOrderSeven.c4_free (R : Set (Fin 57))
  have hKfree := c4Free_induce H hHfree ({v}ᶜ : Set {i // i ∈ R})
  exact hEx41 (α := {i : {i // i ∈ R} // i ∈ ({v}ᶜ : Set {i // i ∈ R})})
    K hKcard hKfree

#print axioms survivorDeletionBound_of_ex41C4Bound

end Implications.C4PolaritySurvivorBound
