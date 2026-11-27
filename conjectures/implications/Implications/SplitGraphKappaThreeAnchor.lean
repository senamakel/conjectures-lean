import Implications.SplitGraphKappaThreeHall
import Implications.SplitGraphSmallRowsThree

/-! A size-four anchor gives disjoint attachment groups for all other vertices
of the independent side. -/

namespace SplitGraphKappaThreeAnchor

variable {V : Type*} [DecidableEq V]

open SplitGraphTrees

/-- Outside a full anchor row, different independent vertices cannot share
a clique neighbor. -/
theorem outside_attachments_pairwise_disjoint [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I : Finset V) (a : V) (ha : a ∈ C)
    (hanchor : (row G I a).card = 4)
    (hTree : inducedTreeBound G 3) (hC : G.IsClique (C : Set V))
    (hI : G.IsIndepSet (I : Set V)) (hCI : Disjoint C I) :
    ((I \ row G I a : Finset V) : Set V).PairwiseDisjoint
      (fun i => C.filter fun c => G.Adj c i) := by
  classical
  have ⟨hrow, hdiff⟩ := rows_bounded_of_inducedTreeBound G C I 3 hTree hC hI hCI
  have hEq (c : V) : SplitGraphKappaThreeHall.row I G.Adj c = row G I c := by
    ext x
    simp [SplitGraphKappaThreeHall.row, row]
  have hOut := SplitGraphKappaThreeHall.outside_anchor_le_one_of_rowDiff C I G.Adj a
    (by rw [hEq]; exact hanchor) (by intro c hc; rw [hEq]; exact hrow c hc) (by
      intro c hc hca
      rw [SplitGraphKappaThreeHall.rowDiff, hEq, hEq]
      exact hdiff c hc a ha hca)
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro c hci hcj
  have ⟨hc, hAdjI⟩ := Finset.mem_filter.mp hci
  have hAdjJ := (Finset.mem_filter.mp hcj).2
  have ⟨hiI, hiA⟩ := Finset.mem_sdiff.mp hi
  have ⟨hjI, hjA⟩ := Finset.mem_sdiff.mp hj
  have hiRow : i ∈ SplitGraphKappaThreeHall.row I G.Adj c \ SplitGraphKappaThreeHall.row I G.Adj a := by
    rw [hEq, hEq]
    exact Finset.mem_sdiff.mpr ⟨by simp [row, hiI, hAdjI], hiA⟩
  have hjRow : j ∈ SplitGraphKappaThreeHall.row I G.Adj c \ SplitGraphKappaThreeHall.row I G.Adj a := by
    rw [hEq, hEq]
    exact Finset.mem_sdiff.mpr ⟨by simp [row, hjI, hAdjJ], hjA⟩
  exact hij (Finset.card_le_one.mp (hOut c hc) i hiRow j hjRow)

/-- The independent vertices outside a size-four anchor can all be put on one
path with clique endpoints. One reserved clique vertex in each outside
attachment group can be avoided. -/
theorem outside_anchor_path_avoiding_reserve [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I reserved : Finset V) (a : V) (ha : a ∈ C)
    (hanchor : (row G I a).card = 4)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hcard : 4 ≤ Fintype.card V)
    (hconn : ∀ D : Finset V, D.card < 3 → (G.induce {x | x ∉ D}).Connected)
    (hTree : inducedTreeBound G 3)
    (hreserve : ∀ k ∈ I \ row G I a,
      ((C.filter fun c => G.Adj c k) ∩ reserved).card ≤ 1) :
    ∃ path : List V, path.Nodup ∧ path.IsChain G.Adj ∧
      (∀ x, x ∈ path.head? → x ∈ C) ∧ (∀ x, x ∈ path.getLast? → x ∈ C) ∧
      (∀ x ∈ I, x ∈ path ↔ x ∉ row G I a) ∧ (∀ x ∈ path, x ∈ C → x ∉ reserved) := by
  classical
  let O := I \ row G I a
  let attach := fun k => C.filter fun c => G.Adj c k
  have hdis := outside_attachments_pairwise_disjoint G C I a ha hanchor hTree hC hI hCI
  have hdegree := SplitGraphBoundedDeletions.attachment_count_of_bounded_deletion_connected
    G C I 3 hI hpartition hcard hconn
  have hpair (k : O) : ∃ l ∈ attach k.val \ reserved, ∃ r ∈ attach k.val \ reserved, l ≠ r := by
    have hcount := Finset.card_sdiff_add_card_inter (attach k.val) reserved
    have hlo := hdegree k.val (Finset.mem_sdiff.mp k.property).1
    change 3 ≤ (attach k.val).card at hlo
    have hhi := hreserve k.val k.property
    change ((attach k.val) ∩ reserved).card ≤ 1 at hhi
    exact Finset.one_lt_card.mp (by omega)
  choose l hl r hr hne using hpair
  let left : V → V := fun k => if hk : k ∈ O then l ⟨k, hk⟩ else k
  let right : V → V := fun k => if hk : k ∈ O then r ⟨k, hk⟩ else k
  have hleft (k : V) (hk : k ∈ O) : left k ∈ attach k \ reserved := by
    simpa [left, hk] using hl ⟨k, hk⟩
  have hright (k : V) (hk : k ∈ O) : right k ∈ attach k \ reserved := by
    simpa [right, hk] using hr ⟨k, hk⟩
  have hleftC k hk := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hleft k hk)).1).1
  have hrightC k hk := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hright k hk)).1).1
  have hunique : ∀ x ∈ C, ∀ k ∈ O, ∀ q ∈ O,
      (left k = x ∨ right k = x) → (left q = x ∨ right q = x) → k = q := by
    intro x _ k hk q hq hxk hxq
    have hmk : x ∈ attach k := by
      rcases hxk with h | h
      · exact h ▸ (Finset.mem_sdiff.mp (hleft k hk)).1
      · exact h ▸ (Finset.mem_sdiff.mp (hright k hk)).1
    have hmq : x ∈ attach q := by
      rcases hxq with h | h
      · exact h ▸ (Finset.mem_sdiff.mp (hleft q hq)).1
      · exact h ▸ (Finset.mem_sdiff.mp (hright q hq)).1
    by_contra hne
    exact (Finset.disjoint_left.mp (hdis hk hq hne)) hmk hmq
  obtain ⟨hnd, hchain, hhead, hlast, hmem⟩ :=
    SplitGraphSmallRowsBlocks.ordinary_blocks_nodup_chain_ends G C I O hC hCI
      Finset.sdiff_subset left right hleftC hrightC
      (fun k hk => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hleft k hk)).1).2)
      (fun k hk => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hright k hk)).1).2)
      (fun k hk => by simpa [left, right, hk] using hne ⟨k, hk⟩) hunique
  refine ⟨_, hnd, hchain, hhead, hlast, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hpath
      obtain ⟨k, hk, h | rfl | h⟩ := (hmem x).mp hpath
      · exact ((Finset.disjoint_left.mp hCI) (h.symm ▸ hleftC k hk) hx).elim
      · exact (Finset.mem_sdiff.mp hk).2
      · exact ((Finset.disjoint_left.mp hCI) (h.symm ▸ hrightC k hk) hx).elim
    · intro hnot
      exact (hmem x).mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hnot⟩, Or.inr (Or.inl rfl)⟩
  · intro x hx hxC
    obtain ⟨k, hk, h | rfl | h⟩ := (hmem x).mp hx
    · exact h.symm ▸ (Finset.mem_sdiff.mp (hleft k hk)).2
    · exact ((Finset.disjoint_left.mp hCI) hxC (Finset.mem_sdiff.mp hk).1).elim
    · exact h.symm ▸ (Finset.mem_sdiff.mp (hright k hk)).2

/-- A clique-ended path through the four anchor vertices extends to a
Hamiltonian path if it uses at most one vertex of each outside attachment
group. The unused clique vertices are appended at the end. -/
theorem hamiltonian_of_anchor_prefix [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I : Finset V) (a : V) (ha : a ∈ C)
    (hanchor : (row G I a).card = 4)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hcard : 4 ≤ Fintype.card V)
    (hconn : ∀ D : Finset V, D.card < 3 → (G.induce {x | x ∉ D}).Connected)
    (hTree : inducedTreeBound G 3) (pref : List V)
    (hpref : pref.Nodup) (hprefChain : pref.IsChain G.Adj)
    (hlast : ∀ x, x ∈ pref.getLast? → x ∈ C)
    (hcore : ∀ x ∈ I, x ∈ pref ↔ x ∈ row G I a)
    (hreserve : ∀ k ∈ I \ row G I a,
      ((C.filter fun c => G.Adj c k) ∩ pref.toFinset).card ≤ 1) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  obtain ⟨rest, hrest, hchain, hhead, hlastRest, houtside, havoid⟩ :=
    outside_anchor_path_avoiding_reserve G C I pref.toFinset a ha hanchor hpartition
      hCI hC hI hcard hconn hTree hreserve
  let T := C.filter fun x => x ∉ pref ++ rest
  let tail := T.toList
  have hpr : ∀ x ∈ pref, x ∉ rest := by
    intro x hp hr
    have hmem := Finset.mem_univ x
    rw [hpartition] at hmem
    rcases Finset.mem_union.mp hmem with hxC | hxI
    · exact havoid x hr hxC (by simpa using hp)
    · exact ((houtside x hxI).mp hr) ((hcore x hxI).mp hp)
  have htailSub : ∀ x ∈ tail, x ∈ C := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).1
  have htailNo : ∀ x ∈ pref ++ rest, x ∉ tail := by
    intro x hx ht
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp ht)).2 hx
  have hcover : ∀ x, x ∈ pref ++ rest ∨ x ∈ tail := by
    intro x
    by_cases hmem : x ∈ pref ++ rest
    · exact Or.inl hmem
    · have hx := Finset.mem_univ x
      rw [hpartition] at hx
      rcases Finset.mem_union.mp hx with hxC | hxI
      · exact Or.inr (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hxC, hmem⟩))
      · by_cases hxA : x ∈ row G I a
        · exact (hmem (List.mem_append_left _ ((hcore x hxI).mpr hxA))).elim
        · exact (hmem (List.mem_append_right _ ((houtside x hxI).mpr hxA))).elim
  have hne : pref ++ rest ++ tail ≠ [] := by
    intro hnil
    rcases hcover a with h | h
    · have := List.mem_append_left tail h
      simpa [hnil] using this
    · have := List.mem_append_right (pref ++ rest) h
      simpa [hnil] using this
  exact SplitGraphSmallRowsThree.hamiltonian_of_prefix_and_remaining_chain G C hC
    pref rest tail hpref hprefChain hlast hrest hchain hhead hlastRest hpr
    (Finset.nodup_toList _) htailSub htailNo hcover hne

#print axioms outside_attachments_pairwise_disjoint
#print axioms outside_anchor_path_avoiding_reserve

end SplitGraphKappaThreeAnchor

#print axioms SplitGraphKappaThreeAnchor.hamiltonian_of_anchor_prefix
