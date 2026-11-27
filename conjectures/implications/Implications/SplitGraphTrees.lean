import Mathlib

/-!
Bridge lemmas for the split-graph case of Written on the Wall II #199.

The Formal Conjectures helpers for largest induced trees are not a dependency of this package.
We use the equivalent Mathlib-level premise `inducedTreeBound`: every induced tree has at most
`k + 2` vertices. The star witness is proved from Mathlib's `starGraph`; the double-star witness
is currently an explicit premise. This avoids depending on external declarations for
`largestInducedTreeSize`.
-/

namespace SplitGraphTrees

variable {V : Type*} [DecidableEq V]

/-- The independent-set vertices adjacent to a given clique vertex. -/
noncomputable def row (G : SimpleGraph V) (I : Finset V) (c : V) : Finset V := by
  classical
  exact I.filter (fun v => G.Adj c v)

/-- The symmetric difference of the rows of two clique vertices. -/
noncomputable def rowDiff (G : SimpleGraph V) (I : Finset V) (c d : V) : Finset V :=
  (row G I c \ row G I d) ∪ (row G I d \ row G I c)

/-- A vertex in the row difference belongs to the independent side and is adjacent
to exactly one of the two clique vertices. -/
theorem mem_rowDiff_iff (G : SimpleGraph V) (I : Finset V) (c d x : V) :
    x ∈ rowDiff G I c d ↔ x ∈ I ∧
      (G.Adj c x ∧ ¬ G.Adj d x ∨ G.Adj d x ∧ ¬ G.Adj c x) := by
  classical
  simp only [rowDiff, Finset.mem_union, Finset.mem_sdiff, row,
    Finset.mem_filter]
  tauto

/-- The induced double star made from a clique edge and the vertices seeing exactly one
of its endpoints is a tree. -/
theorem doubleStar_isTree (G : SimpleGraph V) (C I : Finset V) (c d : V)
    (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hCI : Disjoint C I) (hc : c ∈ C) (hd : d ∈ C) (hcd : c ≠ d) :
    (G.induce
      ((insert c (insert d (rowDiff G I c d) : Finset V) : Finset V) : Set V)).IsTree := by
  classical
  let R := rowDiff G I c d
  let S := insert c (insert d R)
  let H := G.induce (S : Set V)
  let c' : {x // x ∈ (S : Finset V)} := ⟨c, by simp [S]⟩
  let d' : {x // x ∈ (S : Finset V)} := ⟨d, by simp [S, hcd]⟩
  have hcdG : G.Adj c d := hC hc hd hcd
  have hcR : c ∉ R := by
    intro h
    have hi := (mem_rowDiff_iff G I c d c).mp h |>.1
    exact (Finset.disjoint_left.mp hCI hc) hi
  have hdR : d ∉ R := by
    intro h
    have hi := (mem_rowDiff_iff G I c d d).mp h |>.1
    exact (Finset.disjoint_left.mp hCI hd) hi
  have hc'ne : c' ≠ d' := by
    intro h
    exact hcd (congrArg Subtype.val h)
  have hc'd' : H.Adj c' d' := by
    simp [H, c', d', SimpleGraph.induce_adj, hcdG]
  have hleaf (x : {x // x ∈ (S : Finset V)}) (hxC : x ≠ c') (hxD : x ≠ d') :
      ∃ z, ∀ y, H.Adj x y ↔ y = z := by
    have hxR : x.val ∈ R := by
      have hxS := x.property
      simp only [S, Finset.mem_insert] at hxS
      rcases hxS with h | h
      · exact (hxC (Subtype.ext h)).elim
      · rcases Finset.mem_insert.mp h with h | h
        · exact (hxD (Subtype.ext h)).elim
        · exact h
    have hxI := (mem_rowDiff_iff G I c d x.val).mp hxR |>.1
    rcases (mem_rowDiff_iff G I c d x.val).mp hxR |>.2 with hcx | hdx
    · refine ⟨c', ?_⟩
      intro y
      constructor
      · intro hxy
        have hxyG : G.Adj x.val y.val := by simpa [H] using hxy
        have hyS := y.property
        simp only [S, Finset.mem_insert] at hyS
        rcases hyS with hyc | hydR
        · exact Subtype.ext hyc
        · rcases Finset.mem_insert.mp hydR with hyd | hyr
          · have : G.Adj d x.val := hxyG.symm
            exact (hdx.2 this).elim
          · have hyI := (mem_rowDiff_iff G I c d y.val).mp hyr |>.1
            have hne : x.val ≠ y.val := fun h => G.irrefl (h ▸ hxyG)
            exact (hI hxI hyI hne hxyG).elim
      · rintro rfl
        simpa [H, c'] using hcx.1
    · refine ⟨d', ?_⟩
      intro y
      constructor
      · intro hxy
        have hxyG : G.Adj x.val y.val := by simpa [H] using hxy
        have hyS := y.property
        simp only [S, Finset.mem_insert] at hyS
        rcases hyS with hyc | hydR
        · have : G.Adj x.val c := hxyG
          exact (hcx.2 this).elim
        · rcases Finset.mem_insert.mp hydR with hyd | hyr
          · exact Subtype.ext hyd
          · have hyI := (mem_rowDiff_iff G I c d y.val).mp hyr |>.1
            have hne : x.val ≠ y.val := fun h => G.irrefl (h ▸ hxyG)
            exact (hI hxI hyI hne hxyG).elim
      · rintro rfl
        simpa [H, d'] using hdx.1
  have hconn : H.Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨c', fun x => ?_⟩
    by_cases hxc : x = c'
    · simpa [hxc]
    by_cases hxd : x = d'
    · exact hxd ▸ hc'd'.reachable.symm
    · obtain ⟨z, hz⟩ := hleaf x hxc hxd
      by_cases hzc : z = c'
      · rw [hzc] at hz
        exact ((hz c').2 rfl).reachable.symm
      · have hzd : z = d' := by
          have hzcd := hz d'
          have hzd' : H.Adj x d' := by
            have hzx := ((hz z).2 rfl)
            have hzx' := (hC hc hd hcd).reachable
            sorry
          sorry
        sorry
  rw [SimpleGraph.isTree_iff]
  refine ⟨hconn, ?_⟩
  sorry

/-- A Mathlib-level formulation of the bound on the largest induced tree. -/
def inducedTreeBound (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ s : Finset V, (G.induce (s : Set V)).IsTree → s.card ≤ k + 2

/-- A clique vertex together with its row induces a star. -/
theorem star_isTree (G : SimpleGraph V) (I : Finset V) (c : V)
    (hI : G.IsIndepSet (I : Set V)) :
    (G.induce ((insert c (row G I c) : Finset V) : Set V)).IsTree := by
  classical
  let S := insert c (row G I c)
  have hcRow : c ∉ row G I c := by
    intro h
    exact G.irrefl (Finset.mem_filter.mp h).2
  let center : {v // v ∈ (S : Finset V)} := ⟨c, by simp [S]⟩
  have hEq : G.induce (S : Set V) = SimpleGraph.starGraph center := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.starGraph, SimpleGraph.fromRel_adj]
    constructor
    · intro hadj
      refine ⟨?_, ?_⟩
      · intro hxy
        have heq : x.val = y.val := congrArg Subtype.val hxy
        have hadj' : G.Adj x.val x.val := by simpa [heq] using hadj
        exact G.irrefl hadj'
      · rcases Finset.mem_insert.mp x.property with hx | hx
        · left
          apply Subtype.ext
          exact hx
        · rcases Finset.mem_insert.mp y.property with hy | hy
          · right
            apply Subtype.ext
            exact hy
          · have hne : x.val ≠ y.val := fun heq => by
              have hadj' : G.Adj x.val x.val := by simpa [heq] using hadj
              exact G.irrefl hadj'
            exact False.elim (hI (Finset.mem_filter.mp hx).1
              (Finset.mem_filter.mp hy).1 hne hadj)
    · rintro ⟨hxy, hx | hy⟩
      · have hxval : x.val = c := congrArg Subtype.val hx
        have hyrow : y.val ∈ row G I c := by
          rcases Finset.mem_insert.mp y.property with h | h
          · exact (hxy (Subtype.ext (hxval.trans h.symm))).elim
          · exact h
        simpa [hxval] using (Finset.mem_filter.mp hyrow).2
      · have hyval : y.val = c := congrArg Subtype.val hy
        have hxrow : x.val ∈ row G I c := by
          rcases Finset.mem_insert.mp x.property with h | h
          · exact (hxy (Subtype.ext (h.trans hyval.symm))).elim
          · exact h
        simpa [hyval] using ((Finset.mem_filter.mp hxrow).2).symm
  rw [hEq]
  exact SimpleGraph.isTree_starGraph center

/-- The induced star bound gives the size bound on each row. -/
theorem row_card_le (G : SimpleGraph V) (C I : Finset V) (k : ℕ)
    (hI : G.IsIndepSet (I : Set V))
    (hTreeBound : inducedTreeBound G k) :
    ∀ c ∈ C, (row G I c).card ≤ k + 1 := by
  classical
  intro c hc
  have hcn : c ∉ row G I c := by
    intro h
    exact G.irrefl (Finset.mem_filter.mp h).2
  have hbound := hTreeBound (insert c (row G I c)) (star_isTree G I c hI)
  rw [Finset.card_insert_of_notMem hcn] at hbound
  omega

/-- The induced double-star bound controls the symmetric difference of every pair of rows. -/
theorem row_symmDiff_card_le (G : SimpleGraph V) (C I : Finset V) (k : ℕ)
    (hdisj : Disjoint C I)
    (hTreeBound : inducedTreeBound G k)
    (hDoubleStar : ∀ c ∈ C, ∀ d ∈ C, c ≠ d →
      (G.induce
        ((insert c (insert d (rowDiff G I c d) : Finset V) : Finset V) : Set V)).IsTree) :
    ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ k := by
  classical
  intro c hc d hd hcd
  have hcI : c ∉ I := by
    intro hci
    exact (Finset.disjoint_left.mp hdisj hc hci)
  have hdI : d ∉ I := by
    intro hdi
    exact (Finset.disjoint_left.mp hdisj hd hdi)
  have hcRow : c ∉ rowDiff G I c d := by
    intro h
    change c ∈ (row G I c \ row G I d) ∪ (row G I d \ row G I c) at h
    rcases Finset.mem_union.mp h with h | h
    · exact hcI (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
    · exact hcI (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
  have hdRow : d ∉ rowDiff G I c d := by
    intro h
    change d ∈ (row G I c \ row G I d) ∪ (row G I d \ row G I c) at h
    rcases Finset.mem_union.mp h with h | h
    · exact hdI (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
    · exact hdI (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
  have hcdRow : c ∉ insert d (rowDiff G I c d) := by
    simp [hcd, hcRow]
  have hTree := hTreeBound
    (insert c (insert d (rowDiff G I c d))) (hDoubleStar c hc d hd hcd)
  rw [Finset.card_insert_of_notMem hcdRow, Finset.card_insert_of_notMem hdRow] at hTree
  omega

/-- Both row constraints used by the path construction, packaged together. -/
theorem rows_bounded_of_inducedTreeBound
    (G : SimpleGraph V) (C I : Finset V) (k : ℕ)
    (hTreeBound : inducedTreeBound G k)
    (hI : G.IsIndepSet (I : Set V))
    (hdisj : Disjoint C I)
    (hDoubleStar : ∀ c ∈ C, ∀ d ∈ C, c ≠ d →
      (G.induce
        ((insert c (insert d (rowDiff G I c d) : Finset V) : Finset V) : Set V)).IsTree) :
    (∀ c ∈ C, (row G I c).card ≤ k + 1) ∧
      (∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ k) := by
  exact ⟨row_card_le G C I k hI hTreeBound,
    row_symmDiff_card_le G C I k hdisj hTreeBound hDoubleStar⟩

end SplitGraphTrees

#print axioms SplitGraphTrees.star_isTree
#print axioms SplitGraphTrees.mem_rowDiff_iff
#print axioms SplitGraphTrees.row_card_le
#print axioms SplitGraphTrees.row_symmDiff_card_le
