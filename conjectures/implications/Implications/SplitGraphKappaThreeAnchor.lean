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

private theorem outside_path_of_disjoint_attachments
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I O reserved : Finset V)
    (hOsub : O ⊆ I) (hCI : Disjoint C I) (hC : G.IsClique (C : Set V))
    (hdis : (O : Set V).PairwiseDisjoint (fun k => C.filter fun c => G.Adj c k))
    (hreserve : ∀ k ∈ O, 2 ≤ ((C.filter fun c => G.Adj c k) \ reserved).card) :
    ∃ path : List V, path.Nodup ∧ path.IsChain G.Adj ∧
      (∀ x, x ∈ path.head? → x ∈ C) ∧ (∀ x, x ∈ path.getLast? → x ∈ C) ∧
      (∀ x ∈ I, x ∈ path ↔ x ∈ O) ∧ (∀ x ∈ path, x ∈ C → x ∉ reserved) := by
  classical
  let attach := fun k => C.filter fun c => G.Adj c k
  have hpair (k : O) : ∃ l ∈ attach k.val \ reserved, ∃ r ∈ attach k.val \ reserved, l ≠ r :=
    Finset.one_lt_card.mp (hreserve k.val k.property)
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
      hOsub left right hleftC hrightC
      (fun k hk => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hleft k hk)).1).2)
      (fun k hk => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hright k hk)).1).2)
      (fun k hk => by simpa [left, right, hk] using hne ⟨k, hk⟩) hunique
  refine ⟨_, hnd, hchain, hhead, hlast, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hpath
      obtain ⟨k, hk, h | rfl | h⟩ := (hmem x).mp hpath
      · exact ((Finset.disjoint_left.mp hCI) (h.symm ▸ hleftC k hk) hx).elim
      · exact hk
      · exact ((Finset.disjoint_left.mp hCI) (h.symm ▸ hrightC k hk) hx).elim
    · intro hxO
      exact (hmem x).mpr ⟨x, hxO, Or.inr (Or.inl rfl)⟩
  · intro x hx hxC
    obtain ⟨k, hk, h | rfl | h⟩ := (hmem x).mp hx
    · exact h.symm ▸ (Finset.mem_sdiff.mp (hleft k hk)).2
    · exact ((Finset.disjoint_left.mp hCI) hxC (hOsub hk)).elim
    · exact h.symm ▸ (Finset.mem_sdiff.mp (hright k hk)).2

private theorem two_available_of_one_reserved {A reserved : Finset V}
    (hA : 3 ≤ A.card) (hreserved : (A ∩ reserved).card ≤ 1) : 2 ≤ (A \ reserved).card := by
  have hc := Finset.card_sdiff_add_card_inter A reserved
  omega

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
  have hdegree := SplitGraphBoundedDeletions.attachment_count_of_bounded_deletion_connected
    G C I 3 hI hpartition hcard hconn
  obtain ⟨path, hn, hc, hh, hl, hm, hr⟩ :=
    outside_path_of_disjoint_attachments G C I (I \ row G I a) reserved
      Finset.sdiff_subset hCI hC
      (outside_attachments_pairwise_disjoint G C I a ha hanchor hTree hC hI hCI) (by
        intro k hk
        exact two_available_of_one_reserved (hdegree k (Finset.mem_sdiff.mp hk).1) (hreserve k hk))
  refine ⟨path, hn, hc, hh, hl, ?_, hr⟩
  intro x hx
  simpa [Finset.mem_sdiff, hx] using hm x hx

private theorem hamiltonian_of_prefix_and_disjoint_attachments [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I K : Finset V)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V))
    (hdis : ((I \ K : Finset V) : Set V).PairwiseDisjoint
      (fun k => C.filter fun c => G.Adj c k))
    (pref : List V) (hpref : pref.Nodup) (hprefChain : pref.IsChain G.Adj)
    (hlast : ∀ x, x ∈ pref.getLast? → x ∈ C)
    (hcore : ∀ x ∈ I, x ∈ pref ↔ x ∈ K)
    (hreserve : ∀ k ∈ I \ K,
      2 ≤ ((C.filter fun c => G.Adj c k) \ pref.toFinset).card) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  obtain ⟨rest, hrest, hchain, hhead, hlastRest, houtside, havoid⟩ :=
    outside_path_of_disjoint_attachments G C I (I \ K) pref.toFinset
      Finset.sdiff_subset hCI hC hdis hreserve
  let T := C.filter fun x => x ∉ pref ++ rest
  let tail := T.toList
  have hpr : ∀ x ∈ pref, x ∉ rest := by
    intro x hp hr
    have hmem := Finset.mem_univ x
    rw [hpartition] at hmem
    rcases Finset.mem_union.mp hmem with hxC | hxI
    · exact havoid x hr hxC (by simpa using hp)
    · exact ((Finset.mem_sdiff.mp ((houtside x hxI).mp hr)).2) ((hcore x hxI).mp hp)
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
      · by_cases hxA : x ∈ K
        · exact (hmem (List.mem_append_left _ ((hcore x hxI).mpr hxA))).elim
        · exact (hmem (List.mem_append_right _ ((houtside x hxI).mpr (Finset.mem_sdiff.mpr ⟨hxI, hxA⟩)))).elim
  have hne : pref ++ rest ++ tail ≠ [] := by
    intro hnil
    let a : V := Classical.choice inferInstance
    rcases hcover a with h | h
    · have := List.mem_append_left tail h
      simpa [hnil] using this
    · have := List.mem_append_right (pref ++ rest) h
      simpa [hnil] using this
  exact SplitGraphSmallRowsThree.hamiltonian_of_prefix_and_remaining_chain G C hC
    pref rest tail hpref hprefChain hlast hrest hchain hhead hlastRest hpr
    (Finset.nodup_toList _) htailSub htailNo hcover hne

/-- A prefix may absorb outside vertices as well as the anchor. Each
unabsorbed vertex needs two clique attachments outside the prefix. -/
theorem hamiltonian_of_enlarged_anchor_prefix [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I K : Finset V) (a : V) (ha : a ∈ C)
    (hanchor : (row G I a).card = 4) (hAK : row G I a ⊆ K)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hTree : inducedTreeBound G 3) (pref : List V)
    (hpref : pref.Nodup) (hprefChain : pref.IsChain G.Adj)
    (hlast : ∀ x, x ∈ pref.getLast? → x ∈ C)
    (hcore : ∀ x ∈ I, x ∈ pref ↔ x ∈ K)
    (hreserve : ∀ k ∈ I \ K,
      2 ≤ ((C.filter fun c => G.Adj c k) \ pref.toFinset).card) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  letI : Nonempty V := ⟨a⟩
  have hOsub : I \ K ⊆ I \ row G I a := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun h => (Finset.mem_sdiff.mp hx).2 (hAK h)⟩
  have hDis := outside_attachments_pairwise_disjoint G C I a ha hanchor hTree hC hI hCI
  apply hamiltonian_of_prefix_and_disjoint_attachments G C I K hpartition hCI hC
    (fun _ hi _ hj hij => hDis (hOsub hi) (hOsub hj) hij) pref hpref hprefChain hlast hcore hreserve

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
  have hdegree := SplitGraphBoundedDeletions.attachment_count_of_bounded_deletion_connected
    G C I 3 hI hpartition hcard hconn
  apply hamiltonian_of_enlarged_anchor_prefix G C I (row G I a) a ha hanchor
    (fun _ hx => hx) hpartition hCI hC hI hTree pref hpref hprefChain hlast hcore
  intro k hk
  exact two_available_of_one_reserved (hdegree k (Finset.mem_sdiff.mp hk).1) (hreserve k hk)

private theorem attachment_groups_disjoint_of_small_outside_rows
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I K : Finset V)
    (hout : ∀ c ∈ C, (row G I c \ K).card ≤ 1) :
    ((I \ K : Finset V) : Set V).PairwiseDisjoint (fun k => C.filter fun c => G.Adj c k) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro c hci hcj
  have ⟨hc, hAdjI⟩ := Finset.mem_filter.mp hci
  have hAdjJ := (Finset.mem_filter.mp hcj).2
  have ⟨hiI, hiK⟩ := Finset.mem_sdiff.mp hi
  have ⟨hjI, hjK⟩ := Finset.mem_sdiff.mp hj
  have hiRow : i ∈ row G I c \ K := by simp [row, hiI, hAdjI, hiK]
  have hjRow : j ∈ row G I c \ K := by simp [row, hjI, hAdjJ, hjK]
  exact hij (Finset.card_le_one.mp (hout c hc) i hiRow j hjRow)

/-- Connectivity three suffices for a Hamiltonian path in the split-graph
case when each clique vertex has at most two independent neighbors and
the induced-tree bound at connectivity three holds. -/
theorem hamiltonian_of_at_most_two_independent_neighbors [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I : Finset V)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hcard : 4 ≤ Fintype.card V)
    (hconn : ∀ D : Finset V, D.card < 3 → (G.induce {x | x ∉ D}).Connected)
    (hTree : inducedTreeBound G 3)
    (hrows : ∀ c ∈ C, (row G I c).card ≤ 2) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hdegree := SplitGraphBoundedDeletions.attachment_count_of_bounded_deletion_connected
    G C I 3 hI hpartition hcard hconn
  by_cases hfull : ∃ c ∈ C, (row G I c).card = 2
  · obtain ⟨c, hc, hK⟩ := hfull
    let K := row G I c
    have hKa : 1 < K.card := by rw [show K.card = 2 from hK]; decide
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hKa
    have hKset : K = {a, b} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      · simp [hab, show K.card = 2 from hK]
    have haData : a ∈ I ∧ G.Adj c a := by simpa [K, row] using ha
    have hbData : b ∈ I ∧ G.Adj c b := by simpa [K, row] using hb
    let NB := C.filter fun v => G.Adj v b
    have hcNB : c ∈ NB := Finset.mem_filter.mpr ⟨hc, hbData.2⟩
    have hNB : (NB.erase c).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hcNB]
      have hlo := hdegree b hbData.1
      change 3 ≤ NB.card at hlo
      omega
    obtain ⟨d, hd⟩ := hNB
    have hdc := (Finset.mem_erase.mp hd).1
    have ⟨hdC, hdb⟩ := Finset.mem_filter.mp (Finset.mem_erase.mp hd).2
    have houtside : ∀ u ∈ C, (row G I u \ K).card ≤ 1 := by
      intro u hu
      by_cases heq : u = c
      · subst u
        simp [K]
      · let R := row G I u
        have hint := Finset.card_sdiff_add_card_inter R K
        have hint' := Finset.card_sdiff_add_card_inter K R
        rw [Finset.inter_comm K R] at hint'
        have hdist := row_symmDiff_card_le G C I 3 hC hI hCI hTree u hu c hc heq
        have hdis : Disjoint (R \ K) (K \ R) := by
          apply Finset.disjoint_left.mpr
          intro x hx hy
          exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
        change ((R \ K) ∪ (K \ R)).card ≤ 3 at hdist
        rw [Finset.card_union_of_disjoint hdis] at hdist
        have hR : R.card ≤ 2 := hrows u hu
        have h2 : K.card = 2 := hK
        change (R \ K).card ≤ 1
        omega
    let pref : List V := [a, c, b, d]
    have hca : c ≠ a := fun h => (Finset.disjoint_left.mp hCI) (h ▸ hc) haData.1
    have hcb : c ≠ b := fun h => (Finset.disjoint_left.mp hCI) (h ▸ hc) hbData.1
    have hda : d ≠ a := fun h => (Finset.disjoint_left.mp hCI) (h ▸ hdC) haData.1
    have hdb' : d ≠ b := fun h => (Finset.disjoint_left.mp hCI) (h ▸ hdC) hbData.1
    have hpref : pref.Nodup := by
      simp [pref, hab, hca.symm, hda.symm, hcb, hdc.symm, hdb'.symm]
    have hchain : pref.IsChain G.Adj := by
      simp [pref, haData.2.symm, hbData.2, hdb.symm]
    have hlast : ∀ x, x ∈ pref.getLast? → x ∈ C := by
      intro x hx
      have hxd : d = x := by simpa [pref] using hx
      exact hxd ▸ hdC
    have hcore : ∀ x ∈ I, x ∈ pref ↔ x ∈ K := by
      intro x hx
      have hxc : x ≠ c := fun h => (Finset.disjoint_left.mp hCI) hc (h ▸ hx)
      have hxd : x ≠ d := fun h => (Finset.disjoint_left.mp hCI) hdC (h ▸ hx)
      simp [pref, hKset, hxc, hxd]
    apply hamiltonian_of_prefix_and_disjoint_attachments G C I K hpartition hCI hC
      (attachment_groups_disjoint_of_small_outside_rows G C I K houtside) pref hpref hchain hlast hcore
    intro k hk
    have hki := (Finset.mem_sdiff.mp hk).1
    apply two_available_of_one_reserved (hdegree k hki)
    have hsub : (C.filter (fun x => G.Adj x k) ∩ pref.toFinset) ⊆ {d} := by
      intro x hx
      obtain ⟨hxN, hxPref⟩ := Finset.mem_inter.mp hx
      have ⟨hxC, hxAdj⟩ := Finset.mem_filter.mp hxN
      have hm : x ∈ pref := List.mem_toFinset.mp hxPref
      simp only [pref, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact ((Finset.disjoint_left.mp hCI) hxC haData.1).elim
      · have hmem : k ∈ K := by simp [K, row, hki, hxAdj]
        exact ((Finset.mem_sdiff.mp hk).2 hmem).elim
      · exact ((Finset.disjoint_left.mp hCI) hxC hbData.1).elim
      · simp
    exact (Finset.card_le_card hsub).trans (by simp)
  · have hout : ∀ c ∈ C, (row G I c \ (∅ : Finset V)).card ≤ 1 := by
      intro c hc
      rw [Finset.sdiff_empty]
      have hr := hrows c hc
      have hn : (row G I c).card ≠ 2 := fun he => hfull ⟨c, hc, he⟩
      omega
    apply hamiltonian_of_prefix_and_disjoint_attachments G C I ∅ hpartition hCI hC
      (attachment_groups_disjoint_of_small_outside_rows G C I ∅ hout) []
    · simp
    · simp
    · simp
    · simp
    · intro k hk
      have hkI := (Finset.mem_sdiff.mp hk).1
      have hlow := hdegree k hkI
      simp only [List.toFinset_nil, Finset.sdiff_empty]
      omega

#print axioms outside_attachments_pairwise_disjoint
#print axioms outside_anchor_path_avoiding_reserve

end SplitGraphKappaThreeAnchor

#print axioms SplitGraphKappaThreeAnchor.hamiltonian_of_anchor_prefix

#print axioms SplitGraphKappaThreeAnchor.hamiltonian_of_enlarged_anchor_prefix
#print axioms SplitGraphKappaThreeAnchor.hamiltonian_of_at_most_two_independent_neighbors

namespace SplitGraphKappaThreeAnchor

variable {V : Type*} [DecidableEq V]

open SplitGraphTrees

/-- With at most three independent neighbors per clique vertex, a common
pair of independent neighbors can serve as the endpoints of a Hamiltonian
path. All other independent vertices occupy disjoint clique-ended blocks. -/
theorem hamiltonian_of_common_pair [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I : Finset V) (a b : V)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) (hCne : C.Nonempty)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V))
    (hrow : ∀ c ∈ C, (row G I c).card ≤ 3)
    (hcommon : ∀ c ∈ C, G.Adj c a ∧ G.Adj c b)
    (hdegree : ∀ k ∈ I \ {a, b}, 2 ≤ (C.filter fun c => G.Adj c k).card) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  let K : Finset V := {a, b}
  let O := I \ K
  have hdis : (O : Set V).PairwiseDisjoint (fun k => C.filter fun c => G.Adj c k) := by
    intro k hk l hl hkl
    apply Finset.disjoint_left.mpr
    intro c hck hcl
    have ⟨hc, hck'⟩ := Finset.mem_filter.mp hck
    have hcl' := (Finset.mem_filter.mp hcl).2
    have hKsub : K ⊆ row G I c := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [row, ha, (hcommon c hc).1]
      · have hxb := Finset.mem_singleton.mp hx
        subst x
        simp [row, hb, (hcommon c hc).2]
    have hcap : ((row G I c) \ K).card ≤ 1 := by
      have hc' := Finset.card_sdiff_add_card_inter (row G I c) K
      rw [Finset.inter_eq_right.mpr hKsub, show K.card = 2 by simp [K, hab]] at hc'
      have := hrow c hc
      omega
    have hmem (x : V) (hx : x ∈ O) (hadj : G.Adj c x) :
        x ∈ row G I c \ K := by
      obtain ⟨hxI, hxK⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨by simp [row, hxI, hadj], hxK⟩
    exact hkl (Finset.card_le_one.mp hcap k (hmem k hk hck') l (hmem l hl hcl'))
  obtain ⟨blocks, hbn, hbc, hbh, hbl, hbm, _⟩ :=
    outside_path_of_disjoint_attachments G C I O ∅ Finset.sdiff_subset hCI hC hdis (by
      intro k hk
      simpa using hdegree k hk)
  let tail := (C.filter fun x => x ∉ blocks).toList
  let core := blocks ++ tail
  have htailN : tail.Nodup := Finset.nodup_toList _
  have htail (x : V) : x ∈ tail ↔ x ∈ C ∧ x ∉ blocks := by simp [tail]
  have hcoreN : core.Nodup := by
    exact List.nodup_append'.mpr ⟨hbn, htailN, fun x hx ht => ((htail x).mp ht).2 hx⟩
  have hcoreC : core.IsChain G.Adj := by
    apply List.isChain_append.mpr
    refine ⟨hbc, (htailN.pairwise_of_forall_ne fun x hx y hy hn =>
      hC ((htail x).mp hx).1 ((htail y).mp hy).1 hn).isChain, ?_⟩
    intro x hx y hy
    obtain ⟨hyC, hyn⟩ := (htail y).mp (List.mem_of_mem_head? hy)
    exact hC (hbl x hx) hyC (fun hxy => hyn (hxy ▸ List.mem_of_mem_getLast? hx))
  have hhead (x : V) (hx : x ∈ core.head?) : x ∈ C := by
    change x ∈ (blocks ++ tail).head? at hx
    by_cases h : blocks = []
    · exact ((htail x).mp (List.mem_of_mem_head? (by simpa [h] using hx))).1
    · rw [List.head?_append_of_ne_nil blocks h] at hx
      exact hbh x hx
  have hlast (x : V) (hx : x ∈ core.getLast?) : x ∈ C := by
    change x ∈ (blocks ++ tail).getLast? at hx
    by_cases h : tail = []
    · exact hbl x (by simpa [h] using hx)
    · rw [List.getLast?_append_of_ne_nil blocks h] at hx
      exact ((htail x).mp (List.mem_of_mem_getLast? hx)).1
  have hcoreCover (x : V) (hx : x ∈ C ∨ x ∈ O) : x ∈ core := by
    apply List.mem_append.mpr
    rcases hx with hx | hx
    · by_cases h : x ∈ blocks
      · exact Or.inl h
      · exact Or.inr ((htail x).mpr ⟨hx, h⟩)
    · exact Or.inl ((hbm x (Finset.mem_sdiff.mp hx).1).mpr hx)
  have hcoreNe : core ≠ [] := by
    obtain ⟨c, hc⟩ := hCne
    intro h
    simpa [h] using hcoreCover c (Or.inl hc)
  have hnotCore (x : V) (hx : x ∈ I) (hxK : x ∈ K) : x ∉ core := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (Finset.mem_sdiff.mp ((hbm x hx).mp hm)).2 hxK
    · exact (Finset.disjoint_left.mp hCI) ((htail x).mp hm).1 hx
  have hna : a ∉ core := hnotCore a ha (by simp [K])
  have hnb : b ∉ core := hnotCore b hb (by simp [K])
  apply SplitGraphSmallRowsThree.hamiltonian_of_list G (a :: (core ++ [b])) (by simp)
  · simp only [List.nodup_cons, List.mem_append, List.mem_singleton, not_or, hab, not_false_eq_true,
      hna, and_self, true_and]
    exact List.nodup_append'.mpr ⟨hcoreN, by simp, fun x hx hbmem =>
      hnb ((List.mem_singleton.mp hbmem) ▸ hx)⟩
  · rw [List.isChain_cons, List.head?_append_of_ne_nil core hcoreNe]
    refine ⟨fun x hx => (hcommon x (hhead x hx)).1.symm, List.isChain_append.mpr ⟨hcoreC, by simp, ?_⟩⟩
    intro x hx y hy
    have hyb : b = y := by simpa using hy
    exact hyb ▸ (hcommon x (hlast x hx)).2
  · intro x
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    have hx := Finset.mem_univ x
    rw [hpartition] at hx
    have hCore := hcoreCover x (by
      rcases Finset.mem_union.mp hx with hxC | hxI
      · exact Or.inl hxC
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxI, by simp [K, hxa, hxb]⟩))
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hCore)

#print axioms hamiltonian_of_common_pair

end SplitGraphKappaThreeAnchor
