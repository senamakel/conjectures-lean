import Mathlib.Combinatorics.SimpleGraph.Basic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-!
# Adding a vertex to a C4-free graph

An added vertex whose neighborhood contains no pair with a common old neighbor
preserves C4-freeness. Conversely, any such common neighbor creates a 4-cycle
through the added vertex.
-/

namespace C4VertexExtension

/-- A graph has no pair of vertices with two distinct common neighbors.
This is the common-neighbor formulation of being C4-free. -/
def C4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃x y z w⦄, x ≠ y → z ≠ w → G.Adj x z → G.Adj y z →
    ¬ (G.Adj x w ∧ G.Adj y w)

/-- The graph obtained by adjoining one new vertex, adjacent precisely to `s`. -/
def addVertex {V : Type*} (G : SimpleGraph V) (s : Set V) : SimpleGraph (Option V) :=
  { Adj := fun a b => match a, b with
      | some x, some y => G.Adj x y
      | none, some x => x ∈ s
      | some x, none => x ∈ s
      | none, none => False
    symm := by
      constructor
      intro a b hab
      cases a <;> cases b <;> simp_all <;> try exact G.symm.symm _ _ hab
    loopless := by
      constructor
      intro a ha
      cases a <;> simp_all <;> try exact G.loopless.irrefl ha }

@[simp] theorem addVertex_adj_some_some {V : Type*} (G : SimpleGraph V) (s : Set V)
    (x y : V) : (addVertex G s).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

@[simp] theorem addVertex_adj_none_some {V : Type*} (G : SimpleGraph V) (s : Set V)
    (x : V) : (addVertex G s).Adj none (some x) ↔ x ∈ s := Iff.rfl

/-- Exact criterion for the one-vertex extension to remain C4-free. -/
theorem addVertex_c4Free_iff {V : Type*} (G : SimpleGraph V) (s : Set V) :
    C4Free (addVertex G s) ↔
      C4Free G ∧ ∀ ⦃x y z : V⦄, x ≠ y → x ∈ s → y ∈ s →
        ¬ (G.Adj x z ∧ G.Adj y z) := by
  constructor
  · intro h
    constructor
    · intro x y z w hxy hzw hxz hyz
      exact h (x := some x) (y := some y) (z := some z) (w := some w)
        (by simpa using hxy) (by simpa using hzw) hxz hyz
    · intro x y z hxy hsx hsy hcommon
      have hnew : (addVertex G s).Adj none (some x) := by simp [hsx]
      have hnew' : (addVertex G s).Adj none (some y) := by simp [hsy]
      have hold : (addVertex G s).Adj (some x) (some z) := by simpa using hcommon.1
      have hold' : (addVertex G s).Adj (some y) (some z) := by simpa using hcommon.2
      have hnot := h (x := some x) (y := some y) (z := none) (w := some z)
        (by simpa using hxy) (by simp) hnew hnew'
      exact hnot ⟨hold, hold'⟩
  · rintro ⟨hG, hS⟩ x y z w hxy hzw hxz hyz htwo
    cases x with
    | none =>
      cases y with
      | none => exact hxy rfl
      | some y =>
        cases z with
        | none => simp [addVertex] at hxz
        | some z =>
          cases w with
          | none => simp [addVertex] at htwo
          | some w =>
            simp only [addVertex] at *
            exact (hS (x := z) (y := w) (z := y)
              (fun he => hzw (congrArg some he)) hxz htwo.1)
              ⟨G.symm.symm y z hyz, G.symm.symm y w htwo.2⟩
    | some x =>
      cases y with
      | none =>
        cases z with
        | none => simp [addVertex] at hyz
        | some z =>
          cases w with
          | none => simp [addVertex] at htwo
          | some w =>
            simp only [addVertex] at *
            exact (hS (x := z) (y := w) (z := x)
              (fun he => hzw (congrArg some he)) hyz htwo.2)
              ⟨G.symm.symm x z hxz, G.symm.symm x w htwo.1⟩
      | some y =>
        cases z with
        | none =>
          cases w with
          | none => exact hzw rfl
          | some w =>
            simp only [addVertex] at *
            exact (hS (x := x) (y := y) (z := w)
              (fun he => hxy (congrArg some he)) hxz hyz) htwo
        | some z =>
          cases w with
          | none =>
            simp only [addVertex] at *
            exact (hS (x := x) (y := y) (z := z)
              (fun he => hxy (congrArg some he)) htwo.1 htwo.2) ⟨hxz, hyz⟩
          | some w =>
            simp only [addVertex] at *
            exact (hG (x := x) (y := y) (z := z) (w := w)
              (fun he => hxy (congrArg some he))
              (fun he => hzw (congrArg some he)) hxz hyz) htwo

#print axioms addVertex_c4Free_iff

end C4VertexExtension
