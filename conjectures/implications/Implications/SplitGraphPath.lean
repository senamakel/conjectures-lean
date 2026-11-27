import Implications.SplitGraphTrees

/-!
Small combinatorial consequences of the row bounds used for split graphs.

The first lemma isolates the connectivity-one incidence restriction: every independent
vertex has a clique neighbour, every clique row has size at most two, and distinct rows
differ in at most one place. In that situation there are at most two independent vertices.
-/

namespace SplitGraphPath

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma subset_of_card_eq_two_of_symmDiff_le_one {s t : Finset V}
    (hs : s.card ≤ 2) (ht : t.card = 2)
    (hd : ((s \ t) ∪ (t \ s)).card ≤ 1) : s ⊆ t := by
  classical
  intro x hx
  by_contra hxt
  have hxs : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
  have hxs' := Finset.mem_sdiff.mp hxs
  by_cases hts : t ⊆ s
  · have hxt' : x ∉ t := hxt
    have hxnot : x ∉ t := hxt'
    have hcard : (insert x t).card = 3 := by
      rw [Finset.card_insert_of_notMem hxnot, ht]
    have hsub : insert x t ⊆ s := Finset.insert_subset_iff.mpr ⟨hx, hts⟩
    have : (insert x t).card ≤ s.card := Finset.card_le_card hsub
    omega
  · obtain ⟨y, hyt, hys⟩ := Finset.not_subset.mp hts
    have hysdiff : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hyt, hys⟩
    have hxy : x ≠ y := by
      intro heq
      subst y
      exact hys hxs'.1
    have hxy' : y ∉ s \ t := by
      intro hy
      exact hys (Finset.mem_sdiff.mp hy).1
    have hpair : ({x, y} : Finset V) ⊆ (s \ t) ∪ (t \ s) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ hxs
      · exact Finset.mem_union_right _ hysdiff
    have hpaircard : ({x, y} : Finset V).card = 2 := by simp [hxy]
    have := Finset.card_le_card hpair
    omega

private lemma eq_of_card_eq_one_of_symmDiff_le_one {s t : Finset V}
    (hs : s.card = 1) (ht : t.card = 1)
    (hd : ((s \ t) ∪ (t \ s)).card ≤ 1) : s = t := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxt
    have hxs : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
    by_cases hts : t ⊆ s
    · have hst : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
      exact hxt (hst ▸ hx)
    · obtain ⟨y, hyt, hys⟩ := Finset.not_subset.mp hts
      have hysdiff : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hyt, hys⟩
      have hxy : x ≠ y := by
        intro heq
        subst y
        exact hys (Finset.mem_sdiff.mp hxs).1
      have hpair : ({x, y} : Finset V) ⊆ (s \ t) ∪ (t \ s) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_left _ hxs
        · exact Finset.mem_union_right _ hysdiff
      have hpaircard : ({x, y} : Finset V).card = 2 := by simp [hxy]
      have := Finset.card_le_card hpair
      omega
  · intro hx
    by_contra hxt
    have hxt' : x ∈ t \ s := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
    by_cases hst : s ⊆ t
    · have hts : s = t := Finset.eq_of_subset_of_card_le hst (by omega)
      exact hxt (hts ▸ hx)
    · obtain ⟨y, hys, hyt⟩ := Finset.not_subset.mp hst
      have hysdiff : y ∈ s \ t := Finset.mem_sdiff.mpr ⟨hys, hyt⟩
      have hxy : x ≠ y := by
        intro heq
        subst y
        exact hyt (Finset.mem_sdiff.mp hxt').1
      have hpair : ({x, y} : Finset V) ⊆ (s \ t) ∪ (t \ s) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_right _ hxt'
        · exact Finset.mem_union_left _ hysdiff
      have hpaircard : ({x, y} : Finset V).card = 2 := by simp [hxy]
      have := Finset.card_le_card hpair
      omega

/-- In the connectivity-one row regime, the independent side has at most two vertices. -/
theorem independent_card_le_two_of_row_bounds
    (G : SimpleGraph V) (C I : Finset V)
    (hrow : ∀ c ∈ C, (row G I c).card ≤ 2)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ 1)
    (hcover : ∀ i ∈ I, ∃ c ∈ C, G.Adj c i) : I.card ≤ 2 := by
  classical
  by_cases htwo : ∃ c ∈ C, (row G I c).card = 2
  · obtain ⟨c₀, hc₀, hcard₀⟩ := htwo
    have hsub : ∀ c ∈ C, row G I c ⊆ row G I c₀ := by
      intro c hc
      by_cases hcc : c = c₀
      · subst c
        exact Finset.Subset.rfl
      · apply subset_of_card_eq_two_of_symmDiff_le_one (hrow c hc) hcard₀
        simpa [rowDiff, hcc, Finset.union_comm] using hdiff c hc c₀ hc₀ hcc
    have hI : I ⊆ row G I c₀ := by
      intro i hi
      obtain ⟨c, hc, hci⟩ := hcover i hi
      exact hsub c hc (Finset.mem_filter.mpr ⟨hi, hci⟩)
    exact (Finset.card_le_card hI).trans (by omega)
  · have hsmall : ∀ c ∈ C, (row G I c).card ≤ 1 := by
      intro c hc
      have hle := hrow c hc
      by_contra h
      have : (row G I c).card = 2 := by omega
      exact htwo ⟨c, hc, this⟩
    by_cases hempty : I = ∅
    · simp [hempty]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨c₀, hc₀, hci₀⟩ := hcover i hi
      have hc₀row : (row G I c₀).card = 1 := by
        have hmem : i ∈ row G I c₀ := Finset.mem_filter.mpr ⟨hi, hci₀⟩
        have : 0 < (row G I c₀).card := Finset.card_pos.mpr ⟨i, hmem⟩
        have := hsmall c₀ hc₀
        omega
      have hsame : ∀ c ∈ C, (row G I c).Nonempty → row G I c = row G I c₀ := by
        intro c hc
        intro hnonempty
        by_cases hcc : c = c₀
        · simpa [hcc]
        · have hone : (row G I c).card = 1 := by
            have hpos : 0 < (row G I c).card := Finset.card_pos.mpr hnonempty
            have hle := hsmall c hc
            omega
          exact eq_of_card_eq_one_of_symmDiff_le_one hone hc₀row (by
            simpa [rowDiff, hcc, Finset.union_comm] using hdiff c hc c₀ hc₀ hcc)
      have hI : I ⊆ row G I c₀ := by
        intro j hj
        obtain ⟨c, hc, hcj⟩ := hcover j hj
        have hmem : j ∈ row G I c := Finset.mem_filter.mpr ⟨hj, hcj⟩
        rw [← hsame c hc ⟨j, hmem⟩]
        exact hmem
      exact (Finset.card_le_card hI).trans (by omega)

/-- If an ordering of the clique has distinct adjacent endpoints for the two independent
vertices, it gives a Hamiltonian path. The ordering can be filled by `C.toList` with the
two endpoint vertices moved to the ends. -/
theorem hamiltonian_of_clique_order_with_two_endpoints
    (G : SimpleGraph V) (C : Finset V) (i j a b : V) (l : List V)
    (hC : G.IsClique (C : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ {i, j})
    (hi : i ∉ C) (hj : j ∉ C) (hij : i ≠ j)
    (hl_nodup : l.Nodup) (hl_finset : l.toFinset = C)
    (hl_head : l.head? = some a) (hl_last : l.getLast? = some b)
    (hia : G.Adj i a) (hbj : G.Adj b j) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let q := i :: (l ++ [j])
  have hne : q ≠ [] := by simp [q]
  have hchain_l : l.IsChain G.Adj := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro x y l₁ l₂ heq
    have hx : x ∈ l := by rw [heq]; simp
    have hy : y ∈ l := by rw [heq]; simp
    have hxy : x ≠ y := by
      intro h
      subst y
      have hcount := (List.nodup_iff_count_le_one.mp hl_nodup) x
      rw [heq] at hcount
      simp [List.count_append, List.count_cons] at hcount
      omega
    apply hC
    · exact (by simpa [hl_finset] using (List.mem_toFinset.mpr hx))
    · exact (by simpa [hl_finset] using (List.mem_toFinset.mpr hy))
    · exact hxy
  have hchain : q.IsChain G.Adj := by
    dsimp [q]
    rw [List.isChain_cons, List.isChain_append]
    refine ⟨?_, hchain_l, ?_⟩
    · simp [hl_head, hia]
    · simp [hl_last, hbj]
  let p := SimpleGraph.Walk.ofSupport q hne hchain
  have hlj : (l ++ [j]).Nodup := by
    rw [List.nodup_append']
    refine ⟨hl_nodup, by simp, ?_⟩
    intro x hx hy
    simp at hy
    subst x
    apply hj
    exact (by simpa [hl_finset] using (List.mem_toFinset.mpr hx))
  have hnodup : q.Nodup := by
    dsimp [q]
    rw [List.nodup_cons]
    refine ⟨?_, hlj⟩
    intro h
    rcases List.mem_append.mp h with hlmem | hjmem
    · exact hi (by simpa [hl_finset] using (List.mem_toFinset.mpr hlmem))
    · simp at hjmem
      exact hij hjmem
  have hpath : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport hne hchain] using hnodup
  have hcover : ∀ v : V, v ∈ p.support := by
    intro v
    rw [SimpleGraph.Walk.support_ofSupport hne hchain]
    dsimp [q]
    have hv : v ∈ C ∪ {i, j} := by
      have : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [hpartition] at this
      exact this
    rcases Finset.mem_union.mp hv with hvC | hvij
    · have hvl : v ∈ l := by
        exact List.mem_toFinset.mp (by simpa [hl_finset] using hvC)
      simp [hvl]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hvij
      rcases hvij with rfl | rfl <;> simp
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem hcover⟩

/-- In a split partition, distinct clique neighbours of the two independent vertices
are enough: erase them from the clique and put them at opposite ends of its ordering. -/
theorem hamiltonian_of_split_partition_two_endpoints
    (G : SimpleGraph V) (C : Finset V) (i j a b : V)
    (hC : G.IsClique (C : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ {i, j})
    (hi : i ∉ C) (hj : j ∉ C) (hij : i ≠ j)
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b)
    (hia : G.Adj i a) (hbj : G.Adj b j) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let M := (C.erase a).erase b
  let l := a :: (M.toList ++ [b])
  have haM : a ∉ M := by simp [M]
  have hbM : b ∉ M := by simp [M, hab]
  have htail_nodup : (M.toList ++ [b]).Nodup := by
    rw [List.nodup_append']
    refine ⟨M.nodup_toList, by simp, ?_⟩
    intro x hx hy
    simp at hy
    subst x
    exact hbM (by simpa using (List.mem_toFinset.mpr hx))
  have hl_nodup : l.Nodup := by
    simp [l, haM, htail_nodup, hab]
  have hl_finset : l.toFinset = C := by
    ext x
    simp [l, M, ha, hb, Finset.mem_erase]
    constructor
    · rintro (hxa | hxb | ⟨_, hx⟩)
      · exact hxa ▸ ha
      · exact hxb ▸ hb
      · exact hx
    · intro hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr (Or.inl hxb)
        · exact Or.inr (Or.inr ⟨hxa, hx⟩)
  have hl_head : l.head? = some a := by simp [l]
  have hl_last : l.getLast? = some b := by
    change ((a :: M.toList) ++ [b]).getLast? = some b
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  exact hamiltonian_of_clique_order_with_two_endpoints G C i j a b l
    hC hpartition hi hj hij hl_nodup hl_finset hl_head hl_last hia hbj

/-- If each independent vertex is covered by a clique row, a row of size two
and pairwise row differences of size at most one provide distinct attachments. -/
theorem exists_distinct_row_attachments
    (G : SimpleGraph V) (C I : Finset V)
    (hrow : ∀ c ∈ C, (row G I c).card ≤ 2)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ 1)
    (hcover : ∀ i ∈ I, ∃ c ∈ C, G.Adj c i)
    (hI : I.card = 2) (hC : 2 ≤ C.card) :
    ∃ i j a b, i ∈ I ∧ j ∈ I ∧ i ≠ j ∧ a ∈ C ∧ b ∈ C ∧ a ≠ b ∧
      G.Adj a i ∧ G.Adj b j := by
  classical
  obtain ⟨i, j, hij, hIeq⟩ := Finset.card_eq_two.mp hI
  obtain ⟨a, ha, hai⟩ := hcover i (by simp [hIeq])
  obtain ⟨b, hb, hbj⟩ := hcover j (by simp [hIeq])
  by_cases hab : a ≠ b
  · exact ⟨i, j, a, b, by simp [hIeq], by simp [hIeq], hij, ha, hb, hab, hai, hbj⟩
  · have hab' : a = b := by simpa using hab
    subst b
    have hthird : ∃ d ∈ C, d ≠ a := by
      by_contra hn
      push_neg at hn
      have hsub : C ⊆ {a} := by
        intro x hx
        simp only [Finset.mem_singleton]
        exact hn x hx
      have := Finset.card_le_card hsub
      simp at this
      omega
    obtain ⟨d, hd, hda⟩ := hthird
    have hia : i ∈ row G I a := Finset.mem_filter.mpr ⟨by simp [hIeq], hai⟩
    have hja : j ∈ row G I a := Finset.mem_filter.mpr ⟨by simp [hIeq], hbj⟩
    have hrowd : (row G I d).Nonempty := by
      by_contra hn
      have hempty : row G I d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hiDiff : i ∈ rowDiff G I a d := by
        apply Finset.mem_union_left
        exact Finset.mem_sdiff.mpr ⟨hia, by simp [hempty]⟩
      have hjDiff : j ∈ rowDiff G I a d := by
        apply Finset.mem_union_left
        exact Finset.mem_sdiff.mpr ⟨hja, by simp [hempty]⟩
      have hsub : ({i, j} : Finset V) ⊆ rowDiff G I a d := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hiDiff
        · exact hjDiff
      have := Finset.card_le_card hsub
      have hle : 2 ≤ (rowDiff G I a d).card := by simpa [hij] using this
      have hbound := hdiff a ha d hd hda.symm
      omega
    obtain ⟨x, hx⟩ := hrowd
    have hxI : x = i ∨ x = j := by
      have hx' := (Finset.mem_filter.mp hx).1
      have hx'' : x ∈ ({i, j} : Finset V) := by simpa [hIeq] using hx'
      simpa using hx''
    rcases hxI with hxi | hxj
    · refine ⟨i, j, d, a, by simp [hIeq], by simp [hIeq], hij, hd, ha, hda, ?_, hbj⟩
      simpa [hxi] using (Finset.mem_filter.mp hx).2
    · refine ⟨j, i, d, a, by simp [hIeq], by simp [hIeq], hij.symm, hd, ha, hda, ?_, hai⟩
      simpa [hxj] using (Finset.mem_filter.mp hx).2

private theorem hamiltonian_of_list
    (G : SimpleGraph V) (l : List V) (hne : l ≠ []) (hnodup : l.Nodup)
    (hchain : l.IsChain G.Adj) (hcover : ∀ v : V, v ∈ l) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let p := SimpleGraph.Walk.ofSupport l hne hchain
  have hpath : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport hne hchain] using hnodup
  have hvertices : ∀ v : V, v ∈ p.support := by
    intro v
    rw [SimpleGraph.Walk.support_ofSupport hne hchain]
    exact hcover v
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem hvertices⟩

private theorem clique_order_chain (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique (C : Set V)) (l : List V)
    (hnodup : l.Nodup) (hfin : l.toFinset = C) : l.IsChain G.Adj := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y l₁ l₂ heq
  have hx : x ∈ l := by rw [heq]; simp
  have hy : y ∈ l := by rw [heq]; simp
  have hxy : x ≠ y := by
    intro h
    subst y
    have hcount := (List.nodup_iff_count_le_one.mp hnodup) x
    rw [heq] at hcount
    simp [List.count_append] at hcount
    omega
  apply hC
  · exact (by simpa [hfin] using (List.mem_toFinset.mpr hx))
  · exact (by simpa [hfin] using (List.mem_toFinset.mpr hy))
  · exact hxy

/-- A connectivity-one split partition is traceable: the row conditions first
bound the independent side by two, and the remaining cases give an explicit
Hamiltonian walk through the clique. -/
theorem hamiltonian_of_split_partition_row_bounds
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hrow : ∀ c ∈ C, (row G I c).card ≤ 2)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ 1)
    (hcover : ∀ i ∈ I, ∃ c ∈ C, G.Adj c i)
    (hCne : C.Nonempty) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  have hIcard := independent_card_le_two_of_row_bounds G C I hrow hdiff hcover
  by_cases htwo : I.card = 2
  · by_cases hCtwo : 2 ≤ C.card
    · obtain ⟨i, j, a, b, hi, hj, hij, ha, hb, hab, hia, hbj⟩ :=
        exists_distinct_row_attachments G C I hrow hdiff hcover htwo hCtwo
      have hiC : i ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hi
      have hjC : j ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hj
      have hIeq : I = {i, j} := by
        apply Finset.eq_of_subset_of_card_le (by simp [hi, hj])
        simp [hij, htwo]
      have hpart : (Finset.univ : Finset V) = C ∪ {i, j} := by
        simpa [hIeq, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hpartition
      exact hamiltonian_of_split_partition_two_endpoints G C i j a b hC
        hpart hiC hjC hij ha hb hab hia hbj
    · have hCone : C.card = 1 := by omega
      obtain ⟨c, hCeq⟩ := Finset.card_eq_one.mp hCone
      have hc : c ∈ C := by simpa [hCeq]
      obtain ⟨i, j, hij, hIeq⟩ := Finset.card_eq_two.mp htwo
      have hci : G.Adj c i := by
        obtain ⟨d, hd, hdi⟩ := hcover i (by simp [hIeq])
        have : d = c := by simpa [hCeq] using hd
        simpa [this] using hdi
      have hcj : G.Adj c j := by
        obtain ⟨d, hd, hdj⟩ := hcover j (by simp [hIeq])
        have : d = c := by simpa [hCeq] using hd
        simpa [this] using hdj
      have hiC : i ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hi
      have hjC : j ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hj
      have hnodup : ([i, c, j] : List V).Nodup := by
        simp [hiC, hjC, hCeq, hij]
      have hchain : ([i, c, j] : List V).IsChain G.Adj := by
        simp [List.isChain_cons, hci.symm, hcj]
      apply hamiltonian_of_list G [i, c, j] (by simp) hnodup hchain
      intro v
      have hv : v ∈ C ∪ I := by simpa [hpartition] using (Finset.mem_univ v)
      rcases Finset.mem_union.mp hv with hvC | hvI
      · have : v = c := by simpa [hCeq] using hvC
        simp [this]
      · have : v = i ∨ v = j := by simpa [hIeq] using hvI
        rcases this with rfl | rfl <;> simp
  · by_cases hone : I.card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
      obtain ⟨c, hc, hci⟩ := hcover i (by simp [hi])
      let m := C.erase c
      let l := c :: m.toList
      have hmnodup : m.toList.Nodup := m.nodup_toList
      have hcnot : c ∉ m := by simp [m]
      have hiC : i ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hi
      have hlnodup : l.Nodup := by simp [l, hcnot, hmnodup]
      have hlfin : l.toFinset = C := by
        ext x
        simp [l, m, Finset.insert_erase hc]
      have hlchain : l.IsChain G.Adj := clique_order_chain G C hC l hlnodup hlfin
      have hchain : (i :: l).IsChain G.Adj := by
        simp [List.isChain_cons, l, hci.symm, hlchain]
      have hiNotL : i ∉ l := by
        intro hil
        apply hiC
        simpa [hlfin] using (List.mem_toFinset.mpr hil)
      have hnodup : (i :: l).Nodup := by simp [hiNotL, hlnodup]
      apply hamiltonian_of_list G (i :: l) (by simp) hnodup hchain
      intro v
      have hv : v ∈ C ∪ I := by simpa [hpartition] using (Finset.mem_univ v)
      rcases Finset.mem_union.mp hv with hvC | hvI
      · have hvl : v ∈ l := by simpa [hlfin] using hvC
        simp [hvl]
      · have : v = i := by simpa [hi] using hvI
        simp [this]
  · have hempty : I = ∅ := Finset.card_eq_zero.mp (by omega)
    let l := C.toList
    have hnodup : l.Nodup := C.nodup_toList
    have hfin : l.toFinset = C := C.toList_toFinset
    have hchain : l.IsChain G.Adj := clique_order_chain G C hC l hnodup hfin
    have hne : l ≠ [] := by
      intro he
      have : C = ∅ := by simpa [l] using congrArg List.toFinset he
      exact hCne.ne_empty this
    apply hamiltonian_of_list G l hne hnodup hchain
    intro v
    have hv : v ∈ C ∪ I := by simpa [hpartition] using (Finset.mem_univ v)
    simpa [l, hempty, hfin] using (Finset.mem_union.mp hv).resolve_right (by simp [hempty])

end SplitGraphPath

#print axioms SplitGraphPath.independent_card_le_two_of_row_bounds
#print axioms SplitGraphPath.hamiltonian_of_clique_order_with_two_endpoints
#print axioms SplitGraphPath.hamiltonian_of_split_partition_two_endpoints
