import Mathlib

/-!
# Berge–Fulkerson conjecture ⇒ Fan–Raspaud conjecture

Both statements are copied word for word from formal-conjectures (commit `9097e2f`),
`FormalConjectures/Wikipedia/BergeFulkersonConjecture.lean`:

* `BergeFulkersonConjecture.berge_fulkerson_conjecture` (research open), stated here as the
  `Prop` `BergeFulkersonConjectureStatement`;
* `BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud` (research open),
  stated here as the `Prop` `FanRaspaudConjectureStatement`.

The helper definitions `IsCubic` and `IsPerfectMatchingCover` come from the same file, and
`SimpleGraph.IsBridgeless` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cycle.lean`
(all copied verbatim; Apache-2.0, © 2026 The Formal Conjectures Authors).

The deduction is the folklore one noted in the formal-conjectures docstring ("This would follow
from the Berge–Fulkerson conjecture"; Fan–Raspaud 1994). In a Berge–Fulkerson cover every edge
of `G` lies in exactly two of the six perfect matchings, so no edge lies in three of them: any
three of the six, here `M 0`, `M 1`, `M 2`, have no common edge. An element of `Sym2 V` that is
not an edge of `G` lies in no subgraph's edge set.
-/

open SimpleGraph Finset

namespace Implications.Graph.BergeFulkerson

/-- Verbatim from formal-conjectures `9097e2f`,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Cycle.lean`, `SimpleGraph.IsBridgeless`:
`G` is bridgeless if none of its edges is a bridge. -/
def IsBridgeless {V : Type*} (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Verbatim from formal-conjectures `9097e2f`, `BergeFulkersonConjecture.IsCubic`:
a graph is **cubic** if every vertex has degree `3`. -/
def IsCubic (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3

open Classical in
/-- Verbatim from formal-conjectures `9097e2f`, `BergeFulkersonConjecture.IsPerfectMatchingCover`:
a family of `k` perfect matchings of `G` **covers every edge exactly `m` times** if each
member is a perfect matching and every edge of `G` lies in exactly `m` of them. -/
def IsPerfectMatchingCover (G : SimpleGraph V) (k m : ℕ) (M : Fin k → G.Subgraph) : Prop :=
  (∀ i, (M i).IsPerfectMatching) ∧
    ∀ e ∈ G.edgeSet, (univ.filter fun i => e ∈ (M i).edgeSet).card = m

/-- **The Berge–Fulkerson conjecture (Fulkerson 1971)**, verbatim from formal-conjectures
`9097e2f`, `BergeFulkersonConjecture.berge_fulkerson_conjecture`: every bridgeless cubic graph has
six perfect matchings such that every edge lies in exactly two of them. -/
def BergeFulkersonConjectureStatement : Prop :=
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCubic G → IsBridgeless G →
      ∃ M : Fin 6 → G.Subgraph, IsPerfectMatchingCover G 6 2 M

/-- **The Fan–Raspaud conjecture (1994)**, verbatim from formal-conjectures `9097e2f`,
`BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud`: every bridgeless
cubic graph has three perfect matchings with no edge common to all three. -/
def FanRaspaudConjectureStatement : Prop :=
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCubic G → IsBridgeless G →
      ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet)

/-- In a family of perfect matchings covering every edge exactly twice, no edge lies in three
members with distinct indices. -/
theorem not_mem_three_of_isPerfectMatchingCover_two {G : SimpleGraph V} {k : ℕ}
    {M : Fin k → G.Subgraph} (hM : IsPerfectMatchingCover G k 2 M) {i j l : Fin k}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (e : Sym2 V) :
    ¬ (e ∈ (M i).edgeSet ∧ e ∈ (M j).edgeSet ∧ e ∈ (M l).edgeSet) := by
  classical
  rintro ⟨hi, hj, hl⟩
  have he : e ∈ G.edgeSet := (M i).edgeSet_subset hi
  have hcard := hM.2 e he
  have hsub : ({i, j, l} : Finset (Fin k)) ⊆ univ.filter fun t => e ∈ (M t).edgeSet := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> simpa
  have h3 : ({i, j, l} : Finset (Fin k)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hil]),
      Finset.card_pair hjl]
  have := Finset.card_le_card hsub
  -- The filter in `hcard` may carry a different (classical) decidability instance.
  have hcard' : (univ.filter fun t => e ∈ (M t).edgeSet).card = 2 := by
    convert hcard
  omega

/-- **Berge–Fulkerson ⇒ Fan–Raspaud.** -/
theorem fanRaspaud_of_bergeFulkerson (h : BergeFulkersonConjectureStatement) :
    FanRaspaudConjectureStatement := by
  intro V _ _ G _ hcubic hbridgeless
  obtain ⟨M, hM⟩ := h G hcubic hbridgeless
  refine ⟨fun i => M (Fin.castLE (by norm_num) i), fun i => hM.1 _, fun e => ?_⟩
  exact not_mem_three_of_isPerfectMatchingCover_two hM (i := 0) (j := 1) (l := 2)
    (by decide) (by decide) (by decide) e

end Implications.Graph.BergeFulkerson
