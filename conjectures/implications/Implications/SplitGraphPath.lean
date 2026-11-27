import Implications.SplitGraphTrees
import Implications.SplitGraphComponents

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

/-- A list of distinct clique vertices is an adjacency chain. -/
private theorem clique_subset_list_chain (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique (C : Set V)) (l : List V) (hnodup : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ C) : l.IsChain G.Adj := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y l₁ l₂ heq
  have hx : x ∈ l := by rw [heq]; simp
  have hy : y ∈ l := by rw [heq]; simp
  have hxy : x ≠ y := by
    intro h
    subst y
    have hcount := (List.nodup_iff_count_le_one.mp hnodup) x
    rw [heq] at hcount
    simp [List.count_append, List.count_cons] at hcount
    omega
  exact hC (hsub x hx) (hsub y hy) hxy

/-- The two-outsider triple-row path. The list `rest` contains the unused clique
vertices, which are appended after the second outsider's clique neighbour. -/
theorem hamiltonian_of_split_partition_two_outsiders
    (G : SimpleGraph V) (C I : Finset V)
    (a b c z w t x y r s : V) (rest : List V)
    (hC : G.IsClique (C : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hI : I = {a, b, c, z, w})
    (hct : G.Adj c t) (hta : G.Adj t a) (hax : G.Adj a x)
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hyb : G.Adj y b)
    (hbr : G.Adj b r) (hrw : G.Adj r w) (hws : G.Adj w s)
    (hsC : s ∈ C)
    (hbaseNodup : ([c, t, a, x, z, y, b, r, w, s] : List V).Nodup)
    (hrestNodup : rest.Nodup)
    (hrestC : ∀ v ∈ rest, v ∈ C)
    (hbaseRest : ∀ v ∈ ([c, t, a, x, z, y, b, r, w, s] : List V), v ∉ rest)
    (hcoverC : ∀ v ∈ C, v = t ∨ v = x ∨ v = y ∨ v = r ∨ v = s ∨ v ∈ rest) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let base : List V := [c, t, a, x, z, y, b, r, w, s]
  let l := base ++ rest
  have hnodup : l.Nodup := by
    rw [List.nodup_append']
    exact ⟨hbaseNodup, hrestNodup, hbaseRest⟩
  have hbaseChain : base.IsChain G.Adj := by
    simp [base, List.isChain_cons, hct, hta, hax, hxz, hzy, hyb, hbr, hrw, hws]
  have hrestChain : rest.IsChain G.Adj := clique_subset_list_chain G C hC rest hrestNodup hrestC
  have hchain : l.IsChain G.Adj := by
    rw [List.isChain_append]
    refine ⟨hbaseChain, hrestChain, ?_⟩
    intro u hu v hv
    simp [base] at hu
    subst u
    have hvMem : v ∈ rest := List.mem_of_mem_head? hv
    exact hC hsC (hrestC v hvMem) (by
      intro h
      subst v
      exact hbaseRest s (by simp [base]) hvMem)
  have hcover : ∀ v : V, v ∈ l := by
    intro v
    have hv : v ∈ C ∨ v ∈ I := by
      have : v ∈ C ∪ I := by simpa [hpartition] using (Finset.mem_univ v)
      exact Finset.mem_union.mp this
    rcases hv with hvC | hvI
    · rcases hcoverC v hvC with rfl | rfl | rfl | rfl | rfl | hvrest
      · simp [l, base]
      · simp [l, base]
      · simp [l, base]
      · simp [l, base]
      · simp [l, base]
      · exact List.mem_append_right _ hvrest
    · have hv' : v = a ∨ v = b ∨ v = c ∨ v = z ∨ v = w := by
        simpa [hI, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc] using hvI
      rcases hv' with rfl | rfl | rfl | rfl | rfl <;> simp [l, base]
  exact hamiltonian_of_list G l (by simp [l, base]) hnodup hchain hcover

/-- The exact-two-outsider triple-row case follows from row size and
symmetric-difference bounds plus two clique neighbours per outsider. -/
theorem hamiltonian_of_split_partition_two_outsiders_of_rows
    (G : SimpleGraph V) (C I : Finset V) (t z w : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (ht : t ∈ C) (hA : (row G I t).card = 3)
    (hI : I = row G I t ∪ {z, w}) (hzw : z ≠ w)
    (hzA : z ∉ row G I t) (hwA : w ∉ row G I t)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let A := row G I t
  have hzI : z ∈ I := by rw [hI]; simp
  have hwI : w ∈ I := by rw [hI]; simp
  obtain ⟨x, hxC, y, hyC, hxy, hxzG, hyzG⟩ := hdeg z hzI
  obtain ⟨r, hrC, s, hsC, hrs, hrwG, hswG⟩ := hdeg w hwI
  have hRsize : ∀ B ∈ C.image (row G I), B.card ≤ 3 := by
    intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact hrow q hq
  have hRdiff : ∀ B ∈ C.image (row G I), ∀ D ∈ C.image (row G I),
      (B \ D ∪ D \ B).card ≤ 2 := by
    intro B hB D hD
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hD
    by_cases hqd : q = d
    · subst d
      simp [rowDiff]
    · simpa [rowDiff] using hdiff q hq d hd hqd
  have hAR : A ∈ C.image (row G I) := Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hxR : row G I x ∈ C.image (row G I) := Finset.mem_image.mpr ⟨x, hxC, rfl⟩
  have hrR : row G I r ∈ C.image (row G I) := Finset.mem_image.mpr ⟨r, hrC, rfl⟩
  have hzRow : z ∈ row G I x \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hzI, hxzG⟩, hzA⟩
  have hwRow : w ∈ row G I r \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hwI, hrwG⟩, hwA⟩
  obtain ⟨P, hPA, hPcard, hcommon⟩ :=
    SplitGraphComponents.tripleRow_common_outside_pair A (C.image (row G I))
      hA hAR hRsize hRdiff hxR hrR hzRow hwRow hzw
  obtain ⟨a, b, hab, hPeq⟩ := Finset.card_eq_two.mp hPcard
  have haA : a ∈ A := by rw [hPeq] at hPA; exact hPA (by simp)
  have hbA : b ∈ A := by rw [hPeq] at hPA; exact hPA (by simp)
  have hdiffCard : (A \ P).card = 1 := by
    have hcard := Finset.card_sdiff_add_card_inter A P
    rw [Finset.inter_eq_right.mpr hPA, hA, hPcard] at hcard
    omega
  obtain ⟨c, hcDiffEq⟩ := Finset.card_eq_one.mp hdiffCard
  have hcDiff : c ∈ A \ P := by rw [hcDiffEq]; simp
  have hcA : c ∈ A := (Finset.mem_sdiff.mp hcDiff).1
  have hcP : c ∉ P := (Finset.mem_sdiff.mp hcDiff).2
  have hac : a ≠ c := by intro h; subst c; exact hcP (by rw [hPeq]; simp)
  have hbc : b ≠ c := by intro h; subst c; exact hcP (by rw [hPeq]; simp)
  have hcardABC : ({a, b, c} : Finset V).card = 3 := by simp [hab, hac, hbc]
  have hAeq : A = {a, b, c} := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      by_cases hqP : q ∈ P
      · rw [hPeq] at hqP
        have hqAB : q = a ∨ q = b := by simpa using hqP
        rcases hqAB with hqa | hqb
        · simp [hqa]
        · simp [hqb]
      · have hqDiff : q ∈ A \ P := Finset.mem_sdiff.mpr ⟨hq, hqP⟩
        rw [hcDiffEq] at hqDiff
        simp only [Finset.mem_singleton] at hqDiff
        simp [hqDiff]
    · rw [hA]
      exact hcardABC.le
  have hIeq : I = {a, b, c, z, w} := by
    ext q
    rw [hI]
    simp [A, hAeq, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
  have hcomm (q : V) (hq : q ∈ C) (hout : (row G I q \ A).Nonempty) :
      A ∩ row G I q = P :=
    hcommon (row G I q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩) hout
  have hzYRow : z ∈ row G I y \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hzI, hyzG⟩, hzA⟩
  have hwSRow : w ∈ row G I s \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hwI, hswG⟩, hwA⟩
  have hpairRow (q : V) (hq : q ∈ C) (hout : (row G I q \ A).Nonempty) :
      a ∈ row G I q ∧ b ∈ row G I q := by
    have hEq := hcomm q hq hout
    constructor
    · have : a ∈ A ∩ row G I q := by rw [hEq, hPeq]; simp
      exact (Finset.mem_inter.mp this).2
    · have : b ∈ A ∩ row G I q := by rw [hEq, hPeq]; simp
      exact (Finset.mem_inter.mp this).2
  have haxRow := (hpairRow x hxC ⟨z, hzRow⟩).1
  have hbyRow := (hpairRow y hyC ⟨z, hzYRow⟩).2
  have hbrRow := (hpairRow r hrC ⟨w, hwRow⟩).2
  have haPair : a ∈ I ∧ G.Adj t a := by simpa [A, row] using haA
  have hbPair : b ∈ I ∧ G.Adj t b := by simpa [A, row] using hbA
  have hcPair : c ∈ I ∧ G.Adj t c := by simpa [A, row] using hcA
  have haI : a ∈ I := haPair.1
  have hbI : b ∈ I := hbPair.1
  have hcI : c ∈ I := hcPair.1
  have hta : G.Adj t a := by
    have h : a ∈ row G I t := by simpa [A] using haA
    have hm : a ∈ I ∧ G.Adj t a := by simpa [row] using h
    exact hm.2
  have hct : G.Adj c t := by
    have h : c ∈ row G I t := by simpa [A] using hcA
    have hm : c ∈ I ∧ G.Adj t c := by simpa [row] using h
    exact hm.2.symm
  have hax : G.Adj a x := (Finset.mem_filter.mp haxRow).2.symm
  have hxz : G.Adj x z := hxzG
  have hzy : G.Adj z y := hyzG.symm
  have hyb : G.Adj y b := (Finset.mem_filter.mp hbyRow).2
  have hbr : G.Adj b r := (Finset.mem_filter.mp hbrRow).2.symm
  have hrw : G.Adj r w := hrwG
  have hws : G.Adj w s := hswG.symm
  have hci (q : V) (hq : q ∈ C) (i : V) (hi : i ∈ I) : q ≠ i := by
    intro h
    subst i
    exact (Finset.disjoint_left.mp hdisj) hq hi
  have hciRev (q : V) (hq : q ∈ C) (i : V) (hi : i ∈ I) : i ≠ q := (hci q hq i hi).symm
  have htx : t ≠ x := by intro h; subst x; exact hzA (by simp [row, hzI, hxzG])
  have hty : t ≠ y := by intro h; subst y; exact hzA (by simp [row, hzI, hyzG])
  have htr : t ≠ r := by intro h; subst r; exact hwA (by simp [row, hwI, hrwG])
  have hts : t ≠ s := by intro h; subst s; exact hwA (by simp [row, hwI, hswG])
  have hnoShared (q : V) (hq : q ∈ C) (hqz : z ∈ row G I q) (hqw : w ∈ row G I q) : False := by
    have hp := hpairRow q hq ⟨z, Finset.mem_sdiff.mpr ⟨hqz, hzA⟩⟩
    have hsub : ({a, b, z, w} : Finset V) ⊆ row G I q := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact hp.1
      · exact hp.2
      · exact hqz
      · exact hqw
    have haz : a ≠ z := by intro h; exact hzA (h ▸ haA)
    have haw : a ≠ w := by intro h; exact hwA (h ▸ haA)
    have hbz : b ≠ z := by intro h; exact hzA (h ▸ hbA)
    have hbw : b ≠ w := by intro h; exact hwA (h ▸ hbA)
    have hfour : ({a, b, z, w} : Finset V).card = 4 := by simp [hab, hzw, haz, haw, hbz, hbw]
    have hbound := hrow q hq
    have hle := Finset.card_le_card hsub
    omega
  have hxr : x ≠ r := by intro h; subst r; exact hnoShared x hxC (Finset.mem_filter.mpr ⟨hzI, hxzG⟩) (Finset.mem_filter.mpr ⟨hwI, hrwG⟩)
  have hxs : x ≠ s := by intro h; subst s; exact hnoShared x hxC (Finset.mem_filter.mpr ⟨hzI, hxzG⟩) (Finset.mem_filter.mpr ⟨hwI, hswG⟩)
  have hyr : y ≠ r := by intro h; subst r; exact hnoShared y hyC (Finset.mem_filter.mpr ⟨hzI, hyzG⟩) (Finset.mem_filter.mpr ⟨hwI, hrwG⟩)
  have hys : y ≠ s := by intro h; subst s; exact hnoShared y hyC (Finset.mem_filter.mpr ⟨hzI, hyzG⟩) (Finset.mem_filter.mpr ⟨hwI, hswG⟩)
  have hcenterNodup : ([t, x, y, r, s] : List V).Nodup := by
    simp [htx, hty, htr, hts, hxy, hxr, hxs, hyr, hys, hrs]
  have haz : a ≠ z := by intro h; exact hzA (h ▸ haA)
  have haw : a ≠ w := by intro h; exact hwA (h ▸ haA)
  have hbz : b ≠ z := by intro h; exact hzA (h ▸ hbA)
  have hbw : b ≠ w := by intro h; exact hwA (h ▸ hbA)
  have hcz : c ≠ z := by intro h; exact hzA (h ▸ hcA)
  have hcw : c ≠ w := by intro h; exact hwA (h ▸ hcA)
  have hrowNodup : ([a, b, c, z, w] : List V).Nodup := by
    simp [hab, hac, hbc, hzw, haz, haw, hbz, hbw, hcz, hcw]
  let D := C \ {t, x, y, r, s}
  let rest := D.toList
  have hrestNodup : rest.Nodup := D.nodup_toList
  have hrestC : ∀ q ∈ rest, q ∈ C := by
    intro q hq
    have hm : q ∈ rest.toFinset := List.mem_toFinset.mpr hq
    have hqD : q ∈ D := by simpa [rest] using hm
    exact (Finset.mem_sdiff.mp hqD).1
  have hbaseNodup : ([c, t, a, x, z, y, b, r, w, s] : List V).Nodup := by
    let p := [c, t, a]
    let q := [x, z, y]
    let rblock := [b, r, w, s]
    have hp : p.Nodup := by simp [p, hac.symm, hciRev t ht c hcI, hci t ht a haI]
    have hq : q.Nodup := by simp [q, hxy, hci x hxC z hzI, hci y hyC z hzI, hciRev y hyC z hzI]
    have hr : rblock.Nodup := by
      simp [rblock, hciRev r hrC b hbI, hciRev s hsC b hbI,
        hci r hrC w hwI, hci s hsC w hwI, hciRev s hsC w hwI, hbw, hrs]
    have hpq : ∀ v ∈ p, v ∉ q := by
      intro v hv hvq
      simp only [p, q, List.mem_cons, List.not_mem_nil, or_false] at hv hvq
      rcases hv with hvc | hvt | hva
      · rcases hvq with hvx | hvz | hvy
        · exact hciRev x hxC c hcI (hvc.symm.trans hvx)
        · exact hcz (hvc.symm.trans hvz)
        · exact hciRev y hyC c hcI (hvc.symm.trans hvy)
      · rcases hvq with hvx | hvz | hvy
        · exact htx (hvt.symm.trans hvx)
        · exact hciRev t ht z hzI (hvt.symm.trans hvz)
        · exact hty (hvt.symm.trans hvy)
      · rcases hvq with hvx | hvz | hvy
        · exact hciRev x hxC a haI (hva.symm.trans hvx)
        · exact haz (hva.symm.trans hvz)
        · exact hciRev y hyC a haI (hva.symm.trans hvy)
    have hpr : ∀ v ∈ p, v ∉ rblock := by
      intro v hv hvr
      simp only [p, rblock, List.mem_cons, List.not_mem_nil, or_false] at hv hvr
      rcases hv with hvc | hvt | hva
      · rcases hvr with hvb | hvr | hvw | hvs
        · exact hbc.symm (hvc.symm.trans hvb)
        · exact hciRev r hrC c hcI (hvc.symm.trans hvr)
        · exact hcw (hvc.symm.trans hvw)
        · exact hciRev s hsC c hcI (hvc.symm.trans hvs)
      · rcases hvr with hvb | hvr | hvw | hvs
        · exact hci t ht b hbI (hvt.symm.trans hvb)
        · exact htr (hvt.symm.trans hvr)
        · exact hci t ht w hwI (hvt.symm.trans hvw)
        · exact hts (hvt.symm.trans hvs)
      · rcases hvr with hvb | hvr | hvw | hvs
        · exact hab (hva.symm.trans hvb)
        · exact hciRev r hrC a haI (hva.symm.trans hvr)
        · exact haw (hva.symm.trans hvw)
        · exact hciRev s hsC a haI (hva.symm.trans hvs)
    have hqr : ∀ v ∈ q, v ∉ rblock := by
      intro v hv hvr
      simp only [q, rblock, List.mem_cons, List.not_mem_nil, or_false] at hv hvr
      rcases hv with hvx | hvz | hvy
      · rcases hvr with hvb | hvr | hvw | hvs
        · exact hci x hxC b hbI (hvx.symm.trans hvb)
        · exact hxr (hvx.symm.trans hvr)
        · exact hci x hxC w hwI (hvx.symm.trans hvw)
        · exact hxs (hvx.symm.trans hvs)
      · rcases hvr with hvb | hvr | hvw | hvs
        · exact hbz (hvz.symm.trans hvb)
        · exact hciRev r hrC z hzI (hvz.symm.trans hvr)
        · exact hzw (hvz.symm.trans hvw)
        · exact hciRev s hsC z hzI (hvz.symm.trans hvs)
      · rcases hvr with hvb | hvr | hvw | hvs
        · exact hci y hyC b hbI (hvy.symm.trans hvb)
        · exact hyr (hvy.symm.trans hvr)
        · exact hci y hyC w hwI (hvy.symm.trans hvw)
        · exact hys (hvy.symm.trans hvs)
    have hqrNodup : (q ++ rblock).Nodup := by
      rw [List.nodup_append']
      exact ⟨hq, hr, hqr⟩
    have hpqrNodup : (p ++ (q ++ rblock)).Nodup := by
      rw [List.nodup_append']
      refine ⟨hp, hqrNodup, ?_⟩
      intro v hv hvrest
      rcases List.mem_append.mp hvrest with hvq | hvr
      · exact hpq v hv hvq
      · exact hpr v hv hvr
    simpa [p, q, rblock, List.append_assoc] using hpqrNodup
  have hbaseRest : ∀ q ∈ ([c, t, a, x, z, y, b, r, w, s] : List V), q ∉ rest := by
    intro q hq hrest
    have hqD : q ∈ D := by
      have hm : q ∈ rest.toFinset := List.mem_toFinset.mpr hrest
      simpa [rest] using hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hqc | hqt | hqa | hqx | hqz | hqy | hqb | hqr | hqw | hqs
    · have hqC : c ∈ C := by simpa [hqc] using (Finset.mem_sdiff.mp hqD).1
      exact hci c hqC c hcI rfl
    · exact (Finset.mem_sdiff.mp hqD).2 (by simp [hqt])
    · have hqC : a ∈ C := by simpa [hqa] using (Finset.mem_sdiff.mp hqD).1
      exact hci a hqC a haI rfl
    · exact (Finset.mem_sdiff.mp hqD).2 (by simp [hqx])
    · have hqC : z ∈ C := by simpa [hqz] using (Finset.mem_sdiff.mp hqD).1
      exact hci z hqC z hzI rfl
    · exact (Finset.mem_sdiff.mp hqD).2 (by simp [hqy])
    · have hqC : b ∈ C := by simpa [hqb] using (Finset.mem_sdiff.mp hqD).1
      exact hci b hqC b hbI rfl
    · exact (Finset.mem_sdiff.mp hqD).2 (by simp [hqr])
    · have hqC : w ∈ C := by simpa [hqw] using (Finset.mem_sdiff.mp hqD).1
      exact hci w hqC w hwI rfl
    · exact (Finset.mem_sdiff.mp hqD).2 (by simp [hqs])
  have hcoverC : ∀ q ∈ C, q = t ∨ q = x ∨ q = y ∨ q = r ∨ q = s ∨ q ∈ rest := by
    intro q hq
    by_cases hqt : q = t
    · exact Or.inl hqt
    · by_cases hqx : q = x
      · exact Or.inr (Or.inl hqx)
      · by_cases hqy : q = y
        · exact Or.inr (Or.inr (Or.inl hqy))
        · by_cases hqr : q = r
          · exact Or.inr (Or.inr (Or.inr (Or.inl hqr)))
          · by_cases hqs : q = s
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hqs))))
            · right; right; right; right; right
              have hm : q ∈ rest.toFinset := by
                have hqD : q ∈ D := Finset.mem_sdiff.mpr ⟨hq, by simp [hqt, hqx, hqy, hqr, hqs]⟩
                simpa [rest] using hqD
              exact List.mem_toFinset.mp hm
  exact hamiltonian_of_split_partition_two_outsiders G C I a b c z w t x y r s rest
    hC hpartition hIeq hct hta hax hxz hzy hyb hbr hrw hws hsC
    hbaseNodup hrestNodup hrestC hbaseRest hcoverC

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
        apply (Finset.eq_of_subset_of_card_le (s := {i, j}) (t := I) ?_ ?_).symm
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hi
          · exact hj
        · simpa [htwo, hij]
      have hpart : (Finset.univ : Finset V) = C ∪ {i, j} := by
        simpa [hIeq, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hpartition
      exact hamiltonian_of_split_partition_two_endpoints G C i j a b hC
        hpart hiC hjC hij ha hb hab hia.symm hbj
    · have hCpos : 0 < C.card := Finset.card_pos.mpr hCne
      have hCone : C.card = 1 := by omega
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
        exact (Finset.disjoint_left.mp hdisj) hmem (by simp [hIeq])
      have hjC : j ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem (by simp [hIeq])
      have hnodup : ([i, c, j] : List V).Nodup := by
        have hic : i ≠ c := by
          intro heq
          subst i
          exact hiC hc
        have hcj' : c ≠ j := by
          intro heq
          subst j
          exact hjC hc
        simp [hic, hcj', hij]
      have hchain : ([i, c, j] : List V).IsChain G.Adj := by
        simp [List.isChain_cons, hci.symm, hcj]
      apply hamiltonian_of_list G [i, c, j] (by simp) hnodup hchain
      intro v
      have hv : v ∈ C ∪ I := by rw [← hpartition]; exact Finset.mem_univ v
      rcases Finset.mem_union.mp hv with hvC | hvI
      · have : v = c := by simpa [hCeq] using hvC
        simp [this]
      · have : v = i ∨ v = j := by simpa [hIeq] using hvI
        rcases this with rfl | rfl <;> simp
  · by_cases hone : I.card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
      obtain ⟨c, hc, hci⟩ := hcover i (by simp [hi])
      have hiMem : i ∈ I := by simp [hi]
      let m := C.erase c
      let l := c :: m.toList
      have hmnodup : m.toList.Nodup := m.nodup_toList
      have hcnot : c ∉ m := by simp [m]
      have hiC : i ∉ C := by
        intro hmem
        exact (Finset.disjoint_left.mp hdisj) hmem hiMem
      have hlnodup : l.Nodup := by simp [l, hcnot, hmnodup]
      have hlfin : l.toFinset = C := by
        ext x
        simp [l, m, Finset.insert_erase hc]
      have hlchain : l.IsChain G.Adj := clique_order_chain G C hC l hlnodup hlfin
      have hchain : (i :: l).IsChain G.Adj := by
        simp [List.isChain_cons, l, hci.symm, hlchain]
      have hiNotL : i ∉ l := by
        intro hil
        exact hiC (by simpa [hlfin] using (List.mem_toFinset.mpr hil))
      have hnodup : (i :: l).Nodup := by simp [hiNotL, hlnodup]
      apply hamiltonian_of_list G (i :: l) (by simp) hnodup hchain
      intro v
      have hv : v ∈ C ∪ I := by rw [← hpartition]; exact Finset.mem_univ v
      rcases Finset.mem_union.mp hv with hvC | hvI
      · have hvl : v ∈ l := List.mem_toFinset.mp (by simpa [hlfin] using hvC)
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
      have hv : v ∈ C ∪ I := by rw [← hpartition]; exact Finset.mem_univ v
      have hvC : v ∈ C := by
        rcases Finset.mem_union.mp hv with hvC | hvI
        · exact hvC
        · simpa [hempty] using hvI
      exact List.mem_toFinset.mp (by simpa [l, hfin] using hvC)

/-- In a connected split graph, the first step of a path from an independent
vertex to the nonempty clique lies in the clique. -/
private theorem clique_neighbor_of_connected
    (G : SimpleGraph V) (C I : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hconn : G.Connected) (hCne : C.Nonempty) :
    ∀ i ∈ I, ∃ c ∈ C, G.Adj c i := by
  classical
  intro i hi
  obtain ⟨c, hc⟩ := hCne
  have hic : i ≠ c := by
    intro heq
    subst c
    exact (Finset.disjoint_left.mp hdisj) hc hi
  obtain ⟨p, hp⟩ := (hconn.preconnected i c).exists_isPath
  have hnil : ¬ p.Nil := p.not_nil_of_ne hic
  have hadj := p.adj_snd hnil
  have hsndI : p.snd ∉ I := by
    intro hsnd
    by_cases hsame : p.snd = i
    · have hloop : G.Adj i i := by simpa [hsame] using hadj
      exact G.irrefl hloop
    · exact (hI hi hsnd (fun h => hsame h.symm) hadj).elim
  have hsndUniv : p.snd ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [hpartition] at hsndUniv
  have hsndC : p.snd ∈ C := (Finset.mem_union.mp hsndUniv).resolve_right hsndI
  exact ⟨p.snd, hsndC, hadj.symm⟩

/-- A connected split graph with induced-tree bound three has a Hamiltonian path. -/
theorem hamiltonian_of_split_partition_of_inducedTreeBound
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hTreeBound : inducedTreeBound G 1)
    (hconn : G.Connected)
    (hCne : C.Nonempty) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  have hcover := clique_neighbor_of_connected G C I hI hdisj hpartition hconn hCne
  obtain ⟨hrow, hdiff⟩ := rows_bounded_of_inducedTreeBound G C I 1 hTreeBound hC hI hdisj
  exact hamiltonian_of_split_partition_row_bounds G C I hC hI hdisj hpartition
    (by simpa using hrow) (by simpa using hdiff) hcover hCne

end SplitGraphPath

#print axioms SplitGraphPath.independent_card_le_two_of_row_bounds
#print axioms SplitGraphPath.hamiltonian_of_clique_order_with_two_endpoints
#print axioms SplitGraphPath.hamiltonian_of_split_partition_two_endpoints
#print axioms SplitGraphPath.exists_distinct_row_attachments
#print axioms SplitGraphPath.hamiltonian_of_split_partition_two_outsiders
#print axioms SplitGraphPath.hamiltonian_of_split_partition_row_bounds
#print axioms SplitGraphPath.hamiltonian_of_split_partition_of_inducedTreeBound
