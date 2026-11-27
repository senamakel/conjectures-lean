import Implications.SplitGraphSmallRowsAssembly

/-!
The selected-incidence case with exactly one shared clique vertex. The incidence
hypotheses say every selected clique vertex is used once, except `c`, which is
used by exactly `i` and `j`.
-/
namespace SplitGraphSmallRowsOneShared

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem other_labels_ne
    (I : Finset V) (i j k : V) (hij : i ≠ j)
    (hk : k ∈ I \ {i, j}) : k ≠ i ∧ k ≠ j := by
  have hk' := (Finset.mem_sdiff.mp hk).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  exact ⟨hk'.1, hk'.2⟩

/-- One repeated selected clique vertex can be absorbed into a single block.
The other selected incidences are unique, so the ordinary three-vertex blocks
remain pairwise disjoint and can be concatenated between clique vertices. -/
theorem hamiltonian_of_one_shared_selected_clique_vertex
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (left right : V → V)
    (hleftC : ∀ k ∈ I, left k ∈ C) (hrightC : ∀ k ∈ I, right k ∈ C)
    (hleftAdj : ∀ k ∈ I, G.Adj (left k) k)
    (hrightAdj : ∀ k ∈ I, G.Adj (right k) k)
    (hneq : ∀ k ∈ I, left k ≠ right k)
    (c a b i j : V) (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    (hlefti : left i = a) (hrighti : right i = c)
    (hleftj : left j = c) (hrightj : right j = b)
    (hcenter : ∀ k ∈ I, (left k = c ∨ right k = c) ↔ k = i ∨ k = j)
    (hunique : ∀ x ∈ C, x ≠ c → ∀ k ∈ I, ∀ l ∈ I,
      (left k = x ∨ right k = x) → (left l = x ∨ right l = x) → k = l)
    (huniv : (Finset.univ : Finset V).Nonempty) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let others : Finset V := I \ {i, j}
  let block (k : V) : List V := [left k, k, right k]
  let rest := others.toList.flatMap block
  let base := [a, i, c, j, b] ++ rest
  let used : Finset V := {a, b, c} ∪ others.biUnion (fun k => {left k, right k})
  let tail := (C \ used).toList
  have hiC : i ∈ I := hi
  have hjC : j ∈ I := hj
  have hCabc : a ∈ C ∧ c ∈ C ∧ b ∈ C := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hlefti]; exact hleftC i hi
    · rw [← hrighti]; exact hrightC i hi
    · rw [← hrightj]; exact hrightC j hj
  have hneqac : a ≠ c := by
    intro h
    have : left i = right i := by rw [hlefti, hrighti, h]
    exact hneq i hi this
  have hneqcb : c ≠ b := by
    intro h
    have : left j = right j := by rw [hleftj, hrightj, h]
    exact hneq j hj this
  have hneqab : a ≠ b := by
    intro h
    have haC : a ∈ C := hlefti ▸ hleftC i hi
    have heq := hunique a haC hneqac i hi j hj
      (Or.inl hlefti) (Or.inr (hrightj.trans h.symm))
    exact hij heq
  have hblockNodup (k : V) (hk : k ∈ others) : (block k).Nodup := by
    have hkI := (Finset.mem_sdiff.mp hk).1
    have hleft_ne : left k ≠ k := by
      intro h
      have hkC : k ∈ C := by simpa [h] using hleftC k hkI
      exact (Finset.disjoint_left.mp hdisj) hkC hkI
    have hright_ne : right k ≠ k := by
      intro h
      have hkC : k ∈ C := by simpa [h] using hrightC k hkI
      exact (Finset.disjoint_left.mp hdisj) hkC hkI
    simp [block, hleft_ne, hright_ne.symm, hneq k hkI]
  have hblockChain (k : V) (hk : k ∈ others) : (block k).IsChain G.Adj := by
    have hkI := (Finset.mem_sdiff.mp hk).1
    simp [block, List.isChain_cons, hleftAdj k hkI, (hrightAdj k hkI).symm]
  have hnotC (k : V) (hk : k ∈ others) (e : left k = c ∨ right k = c) : False := by
    have hkI := (Finset.mem_sdiff.mp hk).1
    rcases (hcenter k hkI).mp e with hki | hkj
    · exact (other_labels_ne I i j k hij hk).1 hki
    · exact (other_labels_ne I i j k hij hk).2 hkj
  have hblocksDisjoint : ∀ k ∈ others.toList, ∀ l ∈ others.toList, k ≠ l →
      List.Disjoint (block k) (block l) := by
    intro k hk l hl hkl
    have hkO := Finset.mem_toList.mp hk
    have hlO := Finset.mem_toList.mp hl
    have hkI := (Finset.mem_sdiff.mp hkO).1
    have hlI := (Finset.mem_sdiff.mp hlO).1
    rw [List.disjoint_left]
    intro x hx hy
    simp only [block, List.mem_cons, List.not_mem_nil] at hx hy
    simp only [or_false] at hx hy
    rcases hx with hxL | hxI | hxR <;> rcases hy with hyL | hyI | hyR
    · have hxC : x ∈ C := hxL.symm ▸ hleftC k hkI
      have hxe : x ≠ c := by
        intro h
        exact hnotC k hkO (Or.inl (hxL.symm.trans h))
      have hkl' := hunique x hxC hxe k hkI l hlI (Or.inl hxL.symm) (Or.inl hyL.symm)
      exact hkl hkl'
    · have hxC : x ∈ C := hxL.symm ▸ hleftC k hkI
      have hxInI : x ∈ I := hyI.symm ▸ hlI
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · have hxC : x ∈ C := hxL.symm ▸ hleftC k hkI
      have hxe : x ≠ c := by
        intro h
        exact hnotC k hkO (Or.inl (hxL.symm.trans h))
      have hkl' := hunique x hxC hxe k hkI l hlI (Or.inl hxL.symm) (Or.inr hyR.symm)
      exact hkl hkl'
    · have hxInI : x ∈ I := hxI.symm ▸ hkI
      have hxC : x ∈ C := hyL.symm ▸ hleftC l hlI
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · exact hkl (hxI.symm.trans hyI)
    · have hxInI : x ∈ I := hxI.symm ▸ hkI
      have hxC : x ∈ C := hyR.symm ▸ hrightC l hlI
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · have hxC : x ∈ C := hxR.symm ▸ hrightC k hkI
      have hxe : x ≠ c := by
        intro h
        exact hnotC k hkO (Or.inr (hxR.symm.trans h))
      have hkl' := hunique x hxC hxe k hkI l hlI (Or.inr hxR.symm) (Or.inl hyL.symm)
      exact hkl hkl'
    · have hxC : x ∈ C := hxR.symm ▸ hrightC k hkI
      have hxInI : x ∈ I := hyI.symm ▸ hlI
      exact (Finset.disjoint_left.mp hdisj) hxC hxInI
    · have hxC : x ∈ C := hxR.symm ▸ hrightC k hkI
      have hxe : x ≠ c := by
        intro h
        exact hnotC k hkO (Or.inr (hxR.symm.trans h))
      have hkl' := hunique x hxC hxe k hkI l hlI (Or.inr hxR.symm) (Or.inr hyR.symm)
      exact hkl hkl'

  have hrestNodup : rest.Nodup := by
    change (others.toList.flatMap block).Nodup
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hblockNodup k (Finset.mem_toList.mp hk)
    · have hp : ∀ l, (∀ k ∈ l, k ∈ others) → l.Nodup →
          List.Pairwise (fun k l => List.Disjoint (block k) (block l)) l := by
        intro l
        induction l with
        | nil => simp
        | cons k ks ih =>
          intro hmem hnd
          rw [List.pairwise_cons]
          constructor
          · intro l hl
            have hkO : k ∈ others := hmem k (by simp)
            have hlO : l ∈ others := hmem l (by simp [hl])
            exact hblocksDisjoint k (Finset.mem_toList.mpr hkO)
              l (Finset.mem_toList.mpr hlO) (by
              intro heq
              subst l
              exact (List.nodup_cons.mp hnd).1 hl)
          · apply ih
            · intro l hl
              exact hmem l (by simp [hl])
            · exact (List.nodup_cons.mp hnd).2
      exact hp others.toList (fun k hk => Finset.mem_toList.mp hk) others.nodup_toList

  have hrestChain : rest.IsChain G.Adj := by
    have hchain : ∀ l : List V, l.Nodup → (∀ k ∈ l, k ∈ others) →
        (l.flatMap block).IsChain G.Adj := by
      intro l
      induction l with
      | nil => simp
      | cons k ks ih =>
        intro hnd hmem
        have hkO := hmem k (by simp)
        rw [List.flatMap_cons, List.isChain_append]
        refine ⟨hblockChain k hkO,
          ih (List.nodup_cons.mp hnd).2 (by
            intro x hx
            exact hmem x (by simp [hx])), ?_⟩
        cases ks with
        | nil => simp
        | cons l ls =>
          have hlO := hmem l (by simp)
          have hkl : k ≠ l := by
            intro h
            subst l
            exact (List.nodup_cons.mp hnd).1 (by simp)
          intro x hx y hy
          have hxEq : right k = x := by simpa [block] using hx
          have hyEq : left l = y := by simpa [List.flatMap_cons, block] using hy
          have hxy : x ≠ y := by
            intro h
            have hxL : x ∈ block k := List.mem_of_mem_getLast? hx
            have hxR : x ∈ block l := by
              have hlx : left l = x := hyEq.trans h.symm
              simp [block, hlx]
            have hxNot := List.disjoint_left.mp
              (hblocksDisjoint k (Finset.mem_toList.mpr hkO) l
                (Finset.mem_toList.mpr hlO) hkl) hxL
            exact hxNot hxR
          have hEnds : right k ≠ left l := by
            intro h
            apply hxy
            exact hxEq.symm.trans (h.trans hyEq)
          exact hxEq.symm ▸ hyEq.symm ▸ hC
            (hrightC k (Finset.mem_sdiff.mp hkO).1)
            (hleftC l (Finset.mem_sdiff.mp hlO).1) hEnds
    change (others.toList.flatMap block).IsChain G.Adj
    exact hchain others.toList others.nodup_toList
      (fun k hk => Finset.mem_toList.mp hk)

  have hrestHeadC : ∀ x, x ∈ rest.head? → x ∈ C := by
    intro x hx
    cases hlist : others.toList with
    | nil => simp [rest, hlist] at hx
    | cons k ks =>
      have hkO : k ∈ others := Finset.mem_toList.mp (by simp [hlist])
      have hxEq : left k = x := by simpa [rest, hlist, block] using hx
      exact hxEq ▸ hleftC k (Finset.mem_sdiff.mp hkO).1

  have hrestLastC : ∀ x, x ∈ rest.getLast? → x ∈ C := by
    have hlast : ∀ l : List V, (∀ k ∈ l, k ∈ others) →
        ∀ x, x ∈ (l.flatMap block).getLast? → x ∈ C := by
      intro l
      induction l with
      | nil => simp
      | cons k ks ih =>
        intro hmem x hx
        have hkO := hmem k (by simp)
        by_cases htail : ks.flatMap block = []
        · have hx' : x ∈ (block k).getLast? := by
            simpa [List.flatMap_cons, htail] using hx
          have hxEq : right k = x := by simpa [block] using hx'
          exact hxEq.symm ▸ hrightC k (Finset.mem_sdiff.mp hkO).1
        · have hx' : x ∈ (ks.flatMap block).getLast? := by
            change x ∈ (block k ++ ks.flatMap block).getLast? at hx
            rw [List.getLast?_append_of_ne_nil _ htail] at hx
            simpa [List.flatMap_cons] using hx
          exact ih (by
            intro q hq
            exact hmem q (by simp [hq])) x hx'
    exact hlast others.toList (fun k hk => Finset.mem_toList.mp hk)

  have hspecialDisjoint : ∀ x, x ∈ ([a, i, c, j, b] : List V) → x ∉ rest := by
    intro x hx hxRest
    obtain ⟨k, hkList, hxBlock⟩ := List.mem_flatMap.mp hxRest
    have hkO := Finset.mem_toList.mp hkList
    have hkI := (Finset.mem_sdiff.mp hkO).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [block, List.mem_cons, List.not_mem_nil] at hxBlock
    simp only [or_false] at hxBlock
    rcases hx with haX | hiX | hcX | hjX | hbX
    · have hxC : x ∈ C := haX.symm ▸ hCabc.1
      rcases hxBlock with hL | hK | hR
      · have hxe : x ≠ c := by simpa [haX] using hneqac
        have hki := hunique x hxC hxe k hkI i hi (Or.inl hL.symm)
          (Or.inl (hlefti.trans haX.symm))
        exact (other_labels_ne I i j k hij hkO).1 hki
      · exact (Finset.disjoint_left.mp hdisj) hxC (hK.symm ▸ hkI)
      · have hxe : x ≠ c := by simpa [haX] using hneqac
        have hki := hunique x hxC hxe k hkI i hi (Or.inr hR.symm)
          (Or.inl (hlefti.trans haX.symm))
        exact (other_labels_ne I i j k hij hkO).1 hki
    · rcases hxBlock with hL | hK | hR
      · have hiC : x ∈ C := hL.symm ▸ hleftC k hkI
        exact (Finset.disjoint_left.mp hdisj) hiC (hiX.symm ▸ hi)
      · exact (other_labels_ne I i j k hij hkO).1 (hiX.symm.trans hK).symm
      · have hiC : x ∈ C := hR.symm ▸ hrightC k hkI
        exact (Finset.disjoint_left.mp hdisj) hiC (hiX.symm ▸ hi)
    · have hxC : x ∈ C := hcX.symm ▸ hCabc.2.1
      rcases hxBlock with hL | hK | hR
      · exact hnotC k hkO (Or.inl (hL.symm.trans hcX))
      · exact (Finset.disjoint_left.mp hdisj) hxC (hK.symm ▸ hkI)
      · exact hnotC k hkO (Or.inr (hR.symm.trans hcX))
    · rcases hxBlock with hL | hK | hR
      · have hjC : x ∈ C := hL.symm ▸ hleftC k hkI
        exact (Finset.disjoint_left.mp hdisj) hjC (hjX.symm ▸ hj)
      · exact (other_labels_ne I i j k hij hkO).2 (hjX.symm.trans hK).symm
      · have hjC : x ∈ C := hR.symm ▸ hrightC k hkI
        exact (Finset.disjoint_left.mp hdisj) hjC (hjX.symm ▸ hj)
    · have hxC : x ∈ C := hbX.symm ▸ hCabc.2.2
      rcases hxBlock with hL | hK | hR
      · have hxe : x ≠ c := by
          intro h
          exact hneqcb ((hbX.symm.trans h).symm)
        have hkj := hunique x hxC hxe k hkI j hj (Or.inl hL.symm)
          (Or.inr (hrightj.trans hbX.symm))
        exact (other_labels_ne I i j k hij hkO).2 hkj
      · exact (Finset.disjoint_left.mp hdisj) hxC (hK.symm ▸ hkI)
      · have hxe : x ≠ c := by
          intro h
          exact hneqcb ((hbX.symm.trans h).symm)
        have hkj := hunique x hxC hxe k hkI j hj (Or.inr hR.symm)
          (Or.inr (hrightj.trans hbX.symm))
        exact (other_labels_ne I i j k hij hkO).2 hkj

  have husedC : used ⊆ C := by
    intro x hx
    change x ∈ ({a, b, c} ∪ others.biUnion (fun k => {left k, right k})) at hx
    rw [Finset.mem_union] at hx
    rcases hx with hxSpec | hxRows
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxSpec
      rcases hxSpec with h | h | h
      · exact h ▸ hCabc.1
      · exact h ▸ hCabc.2.2
      · exact h ▸ hCabc.2.1
    · obtain ⟨k, hk, hxPair⟩ := Finset.mem_biUnion.mp hxRows
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with h | h
      · exact h ▸ hleftC k (Finset.mem_sdiff.mp hk).1
      · exact h ▸ hrightC k (Finset.mem_sdiff.mp hk).1

  have htailNodup : tail.Nodup := by exact (C \ used).nodup_toList
  have htailC : ∀ x ∈ tail, x ∈ C := by
    intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1

  have hdisjointTail : ∀ x ∈ base, x ∉ tail := by
    intro x hx hxTail
    have hxC : x ∈ C := htailC x hxTail
    have hxBase : x ∈ [a, i, c, j, b] ∨ x ∈ rest := by
      exact List.mem_append.mp hx
    rcases hxBase with hxSpecial | hxRest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxSpecial
      rcases hxSpecial with haX | hiX | hcX | hjX | hbX
      · have hxUsed : x ∈ used := by simp [used, haX]
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxTail)).2 hxUsed
      · exact (Finset.disjoint_left.mp hdisj) hxC (hiX.symm ▸ hi)
      · have hxUsed : x ∈ used := by simp [used, hcX]
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxTail)).2 hxUsed
      · exact (Finset.disjoint_left.mp hdisj) hxC (hjX.symm ▸ hj)
      · have hxUsed : x ∈ used := by simp [used, hbX]
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxTail)).2 hxUsed
    · obtain ⟨k, hk, hxBlock⟩ := List.mem_flatMap.mp hxRest
      have hkO := Finset.mem_toList.mp hk
      have hkI := (Finset.mem_sdiff.mp hkO).1
      simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hxBlock
      rcases hxBlock with hL | hK | hR
      · have hxUsed : x ∈ used := by
          apply Finset.mem_union.mpr
          exact Or.inr (Finset.mem_biUnion.mpr ⟨k, hkO, by simp [hL]⟩)
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxTail)).2 hxUsed
      · exact (Finset.disjoint_left.mp hdisj) hxC (hK.symm ▸ hkI)
      · have hxUsed : x ∈ used := by
          apply Finset.mem_union.mpr
          exact Or.inr (Finset.mem_biUnion.mpr ⟨k, hkO, by simp [hR]⟩)
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hxTail)).2 hxUsed

  have hcover : ∀ x : V, x ∈ [a, i, c, j, b] ++ rest ∨ x ∈ tail := by
    intro x
    have hx : x ∈ C ∨ x ∈ I := by
      have hxU : x ∈ (Finset.univ : Finset V) := Finset.mem_univ x
      rw [hpartition] at hxU
      exact Finset.mem_union.mp hxU
    rcases hx with hxC | hxI
    · by_cases hxUsed : x ∈ used
      · have hxBase : x ∈ [a, i, c, j, b] ++ rest := by
          simp only [used, Finset.mem_union] at hxUsed
          rcases hxUsed with hxSpec | hxRows
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hxSpec
            rcases hxSpec with h | h | h
            · exact List.mem_append_left _ (by simp [h])
            · exact List.mem_append_left _ (by simp [h])
            · exact List.mem_append_left _ (by simp [h])
          · obtain ⟨k, hk, hxPair⟩ := Finset.mem_biUnion.mp hxRows
            have hkList : k ∈ others.toList := Finset.mem_toList.mpr hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
            rcases hxPair with h | h
            · exact List.mem_append_right _ (List.mem_flatMap.mpr
                ⟨k, hkList, by simp [block, h]⟩)
            · exact List.mem_append_right _ (List.mem_flatMap.mpr
                ⟨k, hkList, by simp [block, h]⟩)
        exact Or.inl hxBase
      · exact Or.inr (Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hxC, hxUsed⟩))
    · by_cases hxi : x = i
      · subst x
        exact Or.inl (List.mem_append_left _ (by simp))
      by_cases hxj : x = j
      · subst x
        exact Or.inl (List.mem_append_left _ (by simp))
      · have hxOther : x ∈ others := by
          simp [others, hxI, hxi, hxj]
        exact Or.inl (List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨x, Finset.mem_toList.mpr hxOther, by simp [block]⟩))

  exact SplitGraphSmallRowsAssembly.hamiltonian_of_shared_block_and_remaining_chain
    G C I hC hdisj a c b i j hCabc.1 hCabc.2.1 hCabc.2.2 hi hj hij
    hneqac hneqcb hneqab (by simpa [hlefti] using hleftAdj i hi)
    (by simpa [hrighti] using hrightAdj i hi)
    (by simpa [hleftj] using hleftAdj j hj)
    (by simpa [hrightj] using hrightAdj j hj)
    rest tail hrestNodup hrestChain hrestHeadC hrestLastC hspecialDisjoint
    htailNodup htailC hdisjointTail hcover (by
      obtain ⟨x⟩ := huniv
      intro hnil
      have hxa : a ∈ ([a, i, c, j, b] ++ rest ++ tail) := by simp
      rw [hnil] at hxa
      simp at hxa)

end SplitGraphSmallRowsOneShared
