import Mathlib.Combinatorics.SimpleGraph.Basic

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
      intro a b h
      cases a <;> cases b <;> simp_all [G.symm]
    loopless := by
      intro a h
      cases a with
      | none => exact h
      | some x => exact G.loopless h }

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
      exact h hxy hzw hxz hyz
    · intro x y z hxy hx hsx hsy hcommon
      have hnew : (addVertex G s).Adj none (some x) := by simp [hsx]
      have hnew' : (addVertex G s).Adj none (some y) := by simp [hsy]
      have hold : (addVertex G s).Adj (some z) (some x) := by simpa using hcommon.1.symm
      have hold' : (addVertex G s).Adj (some z) (some y) := by simpa using hcommon.2.symm
      have := h (x := some x) (y := some y) (z := none) (w := some z)
        (by simpa using hxy) (by simp) hnew hnew'
      exact this ⟨by simpa using hold, by simpa using hold'⟩
  · rintro ⟨hG, hS⟩ x y z w hxy hzw hxz hyz htwo
    cases x <;> cases y <;> cases z <;> cases w <;>
      simp_all [addVertex, C4Free] <;>
      try exact hG hxy hzw hxz hyz htwo
      try exact hS hxy ‹_› ‹_› ⟨by assumption, by assumption⟩

#print axioms addVertex_c4Free_iff

end C4VertexExtension
