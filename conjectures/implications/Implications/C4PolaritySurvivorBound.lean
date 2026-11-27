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
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj],
    Fintype.card α = 41 →
      C4VertexExtension.C4Free G → G.edgeSet.ncard ≤ 132

private theorem c4Free_induce {α : Type*} (G : SimpleGraph α)
    (hG : C4VertexExtension.C4Free G) (s : Set α) :
    C4VertexExtension.C4Free (G.induce s) := by
  intro x y z w hxy hzw hxz hyz htwo
  apply hG (x := x.val) (y := y.val) (z := z.val) (w := w.val)
  · exact congrArg Subtype.val hxy
  · exact congrArg Subtype.val hzw
  · exact (SimpleGraph.induce_adj.mp hxz).2
  · exact (SimpleGraph.induce_adj.mp hyz).2
  · intro h
    apply htwo
    exact ⟨(SimpleGraph.induce_adj.mpr ⟨by
      intro hval
      exact h.1 (Subtype.ext hval), h.1⟩),
      (SimpleGraph.induce_adj.mpr ⟨by
        intro hval
        exact h.2 (Subtype.ext hval), h.2⟩)⟩

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
    simp [R, hCand.1]
  have hHcard : Fintype.card {i // i ∈ R} = 42 := by
    simpa [R] using hRcard
  have hKcard : Fintype.card {i : {i // i ∈ R} // i ∈ ({v}ᶜ : Set {i // i ∈ R})} = 41 := by
    rw [Fintype.card_subtype_compl]
    simp [hHcard]
  exact hEx41 K hKcard (c4Free_induce _
    (c4Free_induce _ C4PolarityOrderSeven.c4_free _) _)

#print axioms survivorDeletionBound_of_ex41C4Bound

end Implications.C4PolaritySurvivorBound
