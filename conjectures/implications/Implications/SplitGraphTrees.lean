import Mathlib

/-!
Bridge lemmas for the split-graph case of Written on the Wall II #199.

The Formal Conjectures helpers for largest induced trees are not a dependency of this package.
We use the equivalent Mathlib-level premise `inducedTreeBound`: every induced tree has at most
`k + 2` vertices. The star and double-star trees are given explicitly as hypotheses here, so the
resulting row bounds are independent of any external definition of `largestInducedTreeSize`.
-/

namespace SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The independent-set vertices adjacent to a given clique vertex. -/
noncomputable def row (G : SimpleGraph V) (I : Finset V) (c : V) : Finset V := by
  classical
  exact I.filter (fun v => G.Adj c v)

/-- The symmetric difference of the rows of two clique vertices. -/
noncomputable def rowDiff (G : SimpleGraph V) (I : Finset V) (c d : V) : Finset V :=
  (row G I c \ row G I d) ∪ (row G I d \ row G I c)

/-- A Mathlib-level formulation of the bound on the largest induced tree. -/
def inducedTreeBound (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ s : Finset V, (G.induce (s : Set V)).IsTree → s.card ≤ k + 2

/-- Extending an induced tree by a vertex with a unique neighbor preserves being a tree. -/
private theorem induce_insert_of_unique_adj (G : SimpleGraph V) (s : Finset V)
    (z a : V) (hT : (G.induce (s : Set V)).IsTree)
    (hz : z ∉ s) (ha : a ∈ s) (hza : G.Adj z a)
    (huniq : ∀ ⦃b⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset V) : Set V)).IsTree := by
  classical
  refine ⟨?_, ?_⟩
  · have hsconn := hT.connected.preconnected
    have hzconn : (G.induce ({z} : Set V)).Preconnected := .of_subsingleton
    have hconn := SimpleGraph.connected_induce_union (v := z) (w := a)
      (s := ({z} : Set V)) (t := (s : Set V)) hzconn hsconn (by simp)
      (by simpa using ha) hza
    rw [Finset.coe_insert]
    simpa only [Set.singleton_union] using hconn
  · intro v cyc hcyc
    let e : G.induce ((insert z s : Finset V) : Set V) ↪g G :=
      SimpleGraph.Embedding.induce _
    let q : G.Walk (e v) (e v) := cyc.map e.toHom
    have hq : q.IsCycle := by
      dsimp [q]
      exact (Walk.isCycle_map_iff_of_injective e.injective).2 hcyc
    have hq_mem (w : V) (hw : w ∈ q.support) : w ∈ insert z s := by
      dsimp [q] at hw
      rw [Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      exact w'.property
    by_cases hzq : z ∈ q.support
    · let r : G.Walk z z := q.rotate z hzq
      have hr : r.IsCycle := by simpa [r] using hq.rotate hzq
      have hrsnd : r.snd ∈ q.support := by
        apply (q.mem_support_rotate_iff z hzq).mp
        simpa [r] using r.getVert_mem_support 1
      have hrpen : r.penultimate ∈ q.support := by
        apply (q.mem_support_rotate_iff z hzq).mp
        simpa [r] using r.getVert_mem_support (r.length - 1)
      have hadjSnd : G.Adj z r.snd := r.adj_snd hr.not_nil
      have hadjPen : G.Adj z r.penultimate := (r.adj_penultimate hr.not_nil).symm
      have hSnd : r.snd ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrsnd) with heq | hmem
        · exact (hadjSnd.ne heq.symm).elim
        · exact hmem
      have hPen : r.penultimate ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrpen) with heq | hmem
        · exact (hadjPen.ne heq.symm).elim
        · exact hmem
      exact hr.snd_ne_penultimate
        ((huniq hSnd hadjSnd).trans (huniq hPen hadjPen).symm)
    · have hqs : ∀ w ∈ q.support, w ∈ (s : Set V) := by
        intro w hw
        rcases Finset.mem_insert.mp (hq_mem w hw) with heq | hmem
        · subst w
          exact (hzq hw).elim
        · simpa using hmem
      let qi := q.induce (s : Set V) hqs
      have hqi : qi.IsCycle := by
        apply (Walk.isCycle_map_iff_of_injective
          (f := (SimpleGraph.Embedding.induce (G := G) (s : Set V)).toHom)
          (SimpleGraph.Embedding.induce (G := G) (s : Set V)).injective).mp
        rw [show qi.map (SimpleGraph.Embedding.induce (G := G) (s : Set V)).toHom = q by
          dsimp [qi]
          exact Walk.map_induce q hqs]
        exact hq
      exact hT.isAcyclic qi hqi

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

/-- Two adjacent clique vertices and the symmetric-difference leaves induce a double-star tree. -/
theorem doubleStar_isTree (G : SimpleGraph V) (C I : Finset V) (c d : V)
    (hC : ∀ ⦃x y⦄, x ∈ C → y ∈ C → x ≠ y → G.Adj x y)
    (hI : G.IsIndepSet (I : Set V)) (hdisj : Disjoint C I)
    (hc : c ∈ C) (hd : d ∈ C) (hcd : c ≠ d) :
    (G.induce
      ((insert c (insert d (rowDiff G I c d) : Finset V) : Finset V) : Set V)).IsTree := by
  classical
  let leaves := rowDiff G I c d
  have hcI : c ∉ I := fun h => Finset.disjoint_left.mp hdisj hc h
  have hdI : d ∉ I := fun h => Finset.disjoint_left.mp hdisj hd h
  have hLeavesI : ∀ z ∈ leaves, z ∈ I := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
  have hBase : (G.induce ((insert c ({d} : Finset V) : Finset V) : Set V)).IsTree := by
    have hOne := star_isTree G (∅ : Finset V) d (by simp [SimpleGraph.IsIndepSet])
    have hOne' : (G.induce (({d} : Finset V) : Set V)).IsTree := by
      simpa [row, Finset.filter_empty] using hOne
    exact induce_insert_of_unique_adj G {d} c d hOne' (by simp [hcd]) (by simp)
      (hC hc hd hcd) (by intro b hb; simpa using hb)
  have hBuild : ∀ L : Finset V, L ⊆ leaves →
      (G.induce ((insert c (insert d L : Finset V) : Finset V) : Set V)).IsTree := by
    intro L hL
    induction L using Finset.induction_on with
    | empty => simpa using hBase
    | @insert z L hz ih =>
      have hL' : L ⊆ leaves := Finset.subset_trans (Finset.subset_insert z L) hL
      have hT := ih hL'
      have hzLeaves : z ∈ leaves := hL (Finset.mem_insert_self z L)
      have hzI := hLeavesI z hzLeaves
      have hcz : G.Adj c z ∨ G.Adj d z := by
        rcases Finset.mem_union.mp hzLeaves with h | h
        · exact Or.inl (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
        · exact Or.inr (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
      have hcdNot : ¬ (G.Adj c z ∧ G.Adj d z) := by
        intro hh
        rcases Finset.mem_union.mp hzLeaves with h | h
        · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1, hh.2⟩)
        · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1, hh.1⟩)
      by_cases hcz : G.Adj c z
      · have hdz : ¬ G.Adj d z := fun hdz => hcdNot ⟨hcz, hdz⟩
        have hzNot : z ∉ insert c (insert d L) := by
          intro hmem
          rcases Finset.mem_insert.mp hmem with heq | hmem
          · exact hcI (heq ▸ hzI)
          · rcases Finset.mem_insert.mp hmem with heq | hmem
            · exact hdI (heq ▸ hzI)
            · exact hz (Finset.mem_insert_of_mem hmem)
        have huniq : ∀ ⦃b⦄, b ∈ insert c (insert d L) → G.Adj z b → b = c := by
          intro b hb hadj
          rcases Finset.mem_insert.mp hb with heq | hb
          · exact heq
          · rcases Finset.mem_insert.mp hb with heq | hbL
            · exact (hdz (by simpa [heq] using hadj.symm)).elim
            · have hbI := hLeavesI b (hL (Finset.mem_insert_of_mem hbL))
              have hne : z ≠ b := fun heq => hz (heq ▸ Finset.mem_insert_of_mem hbL)
              exact (hI hzI hbI hne hadj).elim
        have hnext := induce_insert_of_unique_adj G (insert c (insert d L)) z c hT
          hzNot (by simp) hcz.symm huniq
        have hset : insert z (insert c (insert d L)) = insert c (insert d (insert z L)) := by
          ext x
          simp [or_assoc, or_left_comm, or_comm]
        rw [hset]
        exact hnext
      · have hdz : G.Adj d z := hcz.resolve_left hcz
        have hczNot : ¬ G.Adj c z := hcz
        have hzNot : z ∉ insert c (insert d L) := by
          intro hmem
          rcases Finset.mem_insert.mp hmem with heq | hmem
          · exact hcI (heq ▸ hzI)
          · rcases Finset.mem_insert.mp hmem with heq | hmem
            · exact hdI (heq ▸ hzI)
            · exact hz (Finset.mem_insert_of_mem hmem)
        have huniq : ∀ ⦃b⦄, b ∈ insert c (insert d L) → G.Adj z b → b = d := by
          intro b hb hadj
          rcases Finset.mem_insert.mp hb with heq | hb
          · exact (hczNot (by simpa [heq] using hadj.symm)).elim
          · rcases Finset.mem_insert.mp hb with heq | hbL
            · exact heq
            · have hbI := hLeavesI b (hL (Finset.mem_insert_of_mem hbL))
              have hne : z ≠ b := fun heq => hz (heq ▸ Finset.mem_insert_of_mem hbL)
              exact (hI hzI hbI hne hadj).elim
        have hnext := induce_insert_of_unique_adj G (insert c (insert d L)) z d hT
          hzNot (by simp) hdz.symm huniq
        have hset : insert z (insert c (insert d L)) = insert c (insert d (insert z L)) := by
          ext x
          simp [or_assoc, or_left_comm, or_comm]
        rw [hset]
        exact hnext
  exact hBuild leaves (Finset.Subset.rfl)

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

#print axioms SplitGraphTrees.row_card_le
#print axioms SplitGraphTrees.row_symmDiff_card_le
