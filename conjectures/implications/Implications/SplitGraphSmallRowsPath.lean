import Implications.SplitGraphSmallRows

namespace SplitGraphSmallRowsPath

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem hamiltonian_of_list
    (G : SimpleGraph V) (l : List V) (hne : l ≠ []) (hnodup : l.Nodup)
    (hchain : l.IsChain G.Adj) (hcover : ∀ v : V, v ∈ l) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
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

/-- A split graph with selected degree-two neighborhoods and no clique vertex
selected twice has a Hamiltonian path, by concatenating the length-two blocks. -/
theorem hamiltonian_of_split_partition_selected_rows_le_one
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (left right : V → V)
    (hleftC : ∀ i ∈ I, left i ∈ C) (hrightC : ∀ i ∈ I, right i ∈ C)
    (hleftAdj : ∀ i ∈ I, G.Adj (left i) i)
    (hrightAdj : ∀ i ∈ I, G.Adj (right i) i)
    (hneq : ∀ i ∈ I, left i ≠ right i)
    (hrows : ∀ c ∈ C, (I.filter (fun i => left i = c ∨ right i = c)).card ≤ 1)
    (huniv : (Finset.univ : Finset V).Nonempty) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let selected (c : V) := I.filter (fun i => left i = c ∨ right i = c)
  let block (i : V) : List V := [left i, i, right i]
  let base : List V := I.toList.flatMap block
  let used : Finset V := I.biUnion (fun i => {left i, right i})
  let unused : Finset V := C \ used
  let pathList : List V := base ++ unused.toList

  have hleft_ne (i : V) (hi : i ∈ I) : left i ≠ i := by
    intro h
    have hiC : i ∈ C := by simpa [h] using hleftC i hi
    exact (Finset.disjoint_left.mp hdisj) hiC hi
  have hright_ne (i : V) (hi : i ∈ I) : right i ≠ i := by
    intro h
    have hiC : i ∈ C := by simpa [h] using hrightC i hi
    exact (Finset.disjoint_left.mp hdisj) hiC hi

  have hendpoint_eq (i j x : V) (hi : i ∈ I) (hj : j ∈ I)
      (hix : x = left i ∨ x = right i) (hjx : x = left j ∨ x = right j) : i = j := by
    have hxC : x ∈ C := by
      rcases hix with h | h
      · simpa [h] using hleftC i hi
      · simpa [h] using hrightC i hi
    have hiSel : i ∈ selected x := by
      apply Finset.mem_filter.mpr
      refine ⟨hi, ?_⟩
      rcases hix with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hjSel : j ∈ selected x := by
      apply Finset.mem_filter.mpr
      refine ⟨hj, ?_⟩
      rcases hjx with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    by_contra hij
    have hpair : ({i, j} : Finset V) ⊆ selected x := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hiSel
      · exact hjSel
    have htwo : ({i, j} : Finset V).card = 2 := by simp [hij]
    have hle := Finset.card_le_card hpair
    change ({i, j} : Finset V).card ≤ (I.filter (fun k => left k = x ∨ right k = x)).card at hle
    have hrowsx := hrows x hxC
    change (I.filter (fun k => left k = x ∨ right k = x)).card ≤ 1 at hrowsx
    rw [htwo] at hle
    omega

  have hcross_endpoints (i j : V) (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
      left i ≠ left j ∧ left i ≠ right j ∧ right i ≠ left j ∧ right i ≠ right j := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hij (hendpoint_eq i j (left i) hi hj (Or.inl rfl) (Or.inl h))
    · intro h
      exact hij (hendpoint_eq i j (left i) hi hj (Or.inl rfl) (Or.inr h))
    · intro h
      exact hij (hendpoint_eq i j (right i) hi hj (Or.inr rfl) (Or.inl h))
    · intro h
      exact hij (hendpoint_eq i j (right i) hi hj (Or.inr rfl) (Or.inr h))

  have hblock_nodup (i : V) (hi : i ∈ I) : (block i).Nodup := by
    simp [block, hleft_ne i hi, hneq i hi, (hright_ne i hi).symm]

  have hblocks_disjoint (i j : V) (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
      List.Disjoint (block i) (block j) := by
    rw [List.disjoint_left]
    intro x hx hy
    simp only [block, List.mem_cons, List.not_mem_nil] at hx hy
    simp only [or_false] at hx hy
    rcases hx with hxL | hxI | hxR <;> rcases hy with hyL | hyI | hyR
    · exact (hcross_endpoints i j hi hj hij).1 (hxL.symm.trans hyL)
    · have hxC : x ∈ C := hxL.symm ▸ hleftC i hi
      have hxInI : x ∈ I := hyI.symm ▸ hj
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · exact (hcross_endpoints i j hi hj hij).2.1 (hxL.symm.trans hyR)
    · have hxInI : x ∈ I := hxI.symm ▸ hi
      have hxC : x ∈ C := hyL.symm ▸ hleftC j hj
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · exact hij (hxI.symm.trans hyI)
    · have hxInI : x ∈ I := hxI.symm ▸ hi
      have hxC : x ∈ C := hyR.symm ▸ hrightC j hj
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · exact (hcross_endpoints i j hi hj hij).2.2.1 (hxR.symm.trans hyL)
    · have hxC : x ∈ C := hxR.symm ▸ hrightC i hi
      have hxInI : x ∈ I := hyI.symm ▸ hj
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · exact (hcross_endpoints i j hi hj hij).2.2.2 (hxR.symm.trans hyR)

  have pairwise_blocks : ∀ l : List V, l.Nodup →
      (∀ i ∈ l, i ∈ I) → l.Pairwise (fun i j => List.Disjoint (block i) (block j)) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro hnd hmem
      apply List.Pairwise.cons
      · intro j hj
        have hiI := hmem i (by simp)
        have hjI := hmem j (by simp [hj])
        have hij : i ≠ j := by
          intro heq
          subst j
          exact (List.nodup_cons.mp hnd).1 hj
        exact hblocks_disjoint i j hiI hjI hij
      · apply ih
        · exact (List.nodup_cons.mp hnd).2
        · intro j hj
          exact hmem j (by simp [hj])

  have hbase_nodup : base.Nodup := by
    change (I.toList.flatMap block).Nodup
    rw [List.nodup_flatMap]
    refine ⟨?_, pairwise_blocks I.toList I.nodup_toList ?_⟩
    · intro i hi
      exact hblock_nodup i (Finset.mem_toList.mp hi)
    · intro i hi
      exact Finset.mem_toList.mp hi

  have hbase_chain : base.IsChain G.Adj := by
    sorry

  have hused_sub : used ⊆ C := by
    intro c hc
    obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp hc
    have hci' : c = left i ∨ c = right i := by
      simpa using hci
    rcases hci' with h | h
    · simpa [h] using hleftC i hi
    · simpa [h] using hrightC i hi

  have hbase_unused : ∀ c ∈ base, c ∉ unused.toList := by
    intro c hcBase hcUnused
    have hcUn : c ∈ unused := Finset.mem_toList.mp hcUnused
    have hcC : c ∈ C := (Finset.mem_sdiff.mp hcUn).1
    have hcNotUsed : c ∉ used := (Finset.mem_sdiff.mp hcUn).2
    obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hcBase
    have hiI := Finset.mem_toList.mp hi
    simp [block] at hci
    rcases hci with h | h | h
    · have : c ∈ used := Finset.mem_biUnion.mpr ⟨i, hiI, by simp [h]
      ⟩
      exact hcNotUsed this
    · exact (Finset.disjoint_left.mp hdisj) hcC (by simpa [h] using hiI)
    · have : c ∈ used := Finset.mem_biUnion.mpr ⟨i, hiI, by simp [h]
      ⟩
      exact hcNotUsed this

  have hpath_nodup : pathList.Nodup := by
    change (base ++ unused.toList).Nodup
    rw [List.nodup_append']
    exact ⟨hbase_nodup, unused.nodup_toList, hbase_unused⟩

  have hbase_last_C : ∀ c, c ∈ base.getLast? → c ∈ C := by
    sorry

  have hpath_chain : pathList.IsChain G.Adj := by
    change (base ++ unused.toList).IsChain G.Adj
    rw [List.isChain_append]
    refine ⟨hbase_chain, ?_, ?_⟩
    · exact by
        apply clique_list_chain G C hC unused.toList
        exact unused.nodup_toList
        intro c hc
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hc)).1
    · intro x hx y hy
      have hxC := hbase_last_C x hx
      have hyC : y ∈ C := by
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).1
      have hxy : x ≠ y := by
        intro he
        exact hbase_unused x (List.mem_of_mem_getLast? hx) (he ▸ List.mem_of_mem_head? hy)
      exact hC hxC hyC hxy

  have hcover : ∀ v : V, v ∈ pathList := by
    intro v
    have hv : v ∈ C ∨ v ∈ I := by
      have hvU : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [hpartition] at hvU
      exact Finset.mem_union.mp hvU
    rcases hv with hvC | hvI
    · by_cases hvUsed : v ∈ used
      · obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvUsed
        have hiList : i ∈ I.toList := Finset.mem_toList.mpr hi
        have hvmemBlock : v ∈ block i := by
          simp [block] at hvi ⊢
          rcases hvi with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, hiList, hvmemBlock⟩)
      · have hvUnused : v ∈ unused := Finset.mem_sdiff.mpr ⟨hvC, hvUsed⟩
        exact List.mem_append_right _ (Finset.mem_toList.mpr hvUnused)
    · exact List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨v, Finset.mem_toList.mpr hvI, by simp [block]⟩)

  have hne : pathList ≠ [] := by
    intro hnil
    obtain ⟨v⟩ := huniv
    have hvPath := hcover v
    rw [hnil] at hvPath
    simp at hvPath
  exact hamiltonian_of_list G pathList hne hpath_nodup hpath_chain hcover

end SplitGraphSmallRowsPath
