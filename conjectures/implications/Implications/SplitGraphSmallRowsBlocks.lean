import Implications.SplitGraphTrees

/-!
Generic path construction for ordinary selected-neighbor blocks in a split graph.
Each independent vertex is expanded to `[left k, k, right k]`; uniqueness of
selected endpoints on the chosen index set makes these blocks disjoint.
-/
namespace SplitGraphSmallRowsBlocks

open SplitGraphTrees

variable {V : Type*} [DecidableEq V]

/-- The length-two block through an independent vertex. -/
def ordinaryBlock (left right : V → V) (k : V) : List V := [left k, k, right k]

private theorem other_labels_ne
    (I : Finset V) (i j k : V) (hij : i ≠ j)
    (hk : k ∈ I \ {i, j}) : k ≠ i ∧ k ≠ j := by
  have hk' := (Finset.mem_sdiff.mp hk).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  exact ⟨hk'.1, hk'.2⟩

/-- Ordinary selected blocks over `O` form a nodup chain with clique endpoints.
The final characterization says exactly which vertices occur in the flattened
blocks; it is useful when combining these blocks with exceptional blocks. -/
theorem ordinary_blocks_nodup_chain_ends
    (G : SimpleGraph V) (C I O : Finset V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I) (hOsub : O ⊆ I)
    (left right : V → V)
    (hleftC : ∀ k ∈ O, left k ∈ C) (hrightC : ∀ k ∈ O, right k ∈ C)
    (hleftAdj : ∀ k ∈ O, G.Adj (left k) k)
    (hrightAdj : ∀ k ∈ O, G.Adj (right k) k)
    (hneq : ∀ k ∈ O, left k ≠ right k)
    (hunique : ∀ x ∈ C, ∀ k ∈ O, ∀ l ∈ O,
      (left k = x ∨ right k = x) → (left l = x ∨ right l = x) → k = l) :
    let blocks := O.toList.flatMap (ordinaryBlock left right)
    blocks.Nodup ∧ blocks.IsChain G.Adj ∧
      (∀ x, x ∈ blocks.head? → x ∈ C) ∧
      (∀ x, x ∈ blocks.getLast? → x ∈ C) ∧
      (∀ x, x ∈ blocks ↔ ∃ k ∈ O,
        x = left k ∨ x = k ∨ x = right k) := by
  classical
  dsimp only
  let block := ordinaryBlock left right
  let blocks := O.toList.flatMap block
  have hblockNodup (k : V) (hk : k ∈ O) : (block k).Nodup := by
    have hkI := hOsub hk
    have hleftNe : left k ≠ k := by
      intro h
      have hkC : k ∈ C := by simpa [h] using hleftC k hk
      exact (Finset.disjoint_left.mp hdisj) hkC hkI
    have hrightNe : right k ≠ k := by
      intro h
      have hkC : k ∈ C := by simpa [h] using hrightC k hk
      exact (Finset.disjoint_left.mp hdisj) hkC hkI
    simp [block, ordinaryBlock, hleftNe, hrightNe.symm, hneq k hk]
  have hblocksDisjoint : ∀ k ∈ O.toList, ∀ l ∈ O.toList, k ≠ l →
      List.Disjoint (block k) (block l) := by
    intro k hk l hl hkl
    have hkO := Finset.mem_toList.mp hk
    have hlO := Finset.mem_toList.mp hl
    rw [List.disjoint_left]
    intro x hx hy
    simp only [block, ordinaryBlock, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with hxL | hxI | hxR <;> rcases hy with hyL | hyI | hyR
    · have hxC : x ∈ C := hxL.symm ▸ hleftC k hkO
      have hkl' := hunique x hxC k hkO l hlO (Or.inl hxL.symm) (Or.inl hyL.symm)
      exact hkl hkl'
    · have hxC : x ∈ C := hxL.symm ▸ hleftC k hkO
      have hxI' : x ∈ I := hyI.symm ▸ hOsub hlO
      exact (Finset.disjoint_left.mp hdisj) hxC hxI'
    · have hxC : x ∈ C := hxL.symm ▸ hleftC k hkO
      have hkl' := hunique x hxC k hkO l hlO (Or.inl hxL.symm) (Or.inr hyR.symm)
      exact hkl hkl'
    · have hxI' : x ∈ I := hxI.symm ▸ hOsub hkO
      have hxC : x ∈ C := hyL.symm ▸ hleftC l hlO
      exact (Finset.disjoint_left.mp hdisj) hxC hxI'
    · exact hkl (hxI.symm.trans hyI)
    · have hxI' : x ∈ I := hxI.symm ▸ hOsub hkO
      have hxC : x ∈ C := hyR.symm ▸ hrightC l hlO
      exact (Finset.disjoint_left.mp hdisj) hxC hxI'
    · have hxC : x ∈ C := hxR.symm ▸ hrightC k hkO
      have hkl' := hunique x hxC k hkO l hlO (Or.inr hxR.symm) (Or.inl hyL.symm)
      exact hkl hkl'
    · have hxC : x ∈ C := hxR.symm ▸ hrightC k hkO
      have hxI' : x ∈ I := hyI.symm ▸ hOsub hlO
      exact (Finset.disjoint_left.mp hdisj) hxC hxI'
    · have hxC : x ∈ C := hxR.symm ▸ hrightC k hkO
      have hkl' := hunique x hxC k hkO l hlO (Or.inr hxR.symm) (Or.inr hyR.symm)
      exact hkl hkl'
  have hnodup : blocks.Nodup := by
    change (O.toList.flatMap block).Nodup
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hblockNodup k (Finset.mem_toList.mp hk)
    · have hpair : ∀ l : List V, (∀ k ∈ l, k ∈ O) → l.Nodup →
          List.Pairwise (fun k l => List.Disjoint (block k) (block l)) l := by
        intro l
        induction l with
        | nil => simp
        | cons k ks ih =>
          intro hmem hnd
          rw [List.pairwise_cons]
          constructor
          · intro l hl
            exact hblocksDisjoint k (Finset.mem_toList.mpr (hmem k (by simp)))
              l (Finset.mem_toList.mpr (hmem l (by simp [hl]))) (by
                intro heq
                subst l
                exact (List.nodup_cons.mp hnd).1 hl)
          · apply ih
            · intro l hl
              exact hmem l (by simp [hl])
            · exact (List.nodup_cons.mp hnd).2
      exact hpair O.toList (fun k hk => Finset.mem_toList.mp hk) O.nodup_toList
  have hchain : blocks.IsChain G.Adj := by
    have hchainList : ∀ l : List V, l.Nodup → (∀ k ∈ l, k ∈ O) →
        (l.flatMap block).IsChain G.Adj := by
      intro l
      induction l with
      | nil => simp
      | cons k ks ih =>
        intro hnd hmem
        have hkO := hmem k (by simp)
        rw [List.flatMap_cons, List.isChain_append]
        refine ⟨?_, ih (List.nodup_cons.mp hnd).2 (by
          intro x hx
          exact hmem x (by simp [hx])), ?_⟩
        · simp [block, ordinaryBlock, List.isChain_cons,
            hleftAdj k hkO, (hrightAdj k hkO).symm]
        · cases ks with
          | nil => simp
          | cons l ls =>
            have hlO := hmem l (by simp)
            have hkl : k ≠ l := by
              intro heq
              subst l
              exact (List.nodup_cons.mp hnd).1 (by simp)
            intro x hx y hy
            have hxEq : right k = x := by simpa [block, ordinaryBlock] using hx
            have hyEq : left l = y := by
              simpa [List.flatMap_cons, block, ordinaryBlock] using hy
            have hxy : x ≠ y := by
              intro heq
              have hxL : x ∈ block k := List.mem_of_mem_getLast? hx
              have hxR : x ∈ block l := by
                have hlx : left l = x := hyEq.trans heq.symm
                simp [block, ordinaryBlock, hlx]
              exact (List.disjoint_left.mp
                (hblocksDisjoint k (Finset.mem_toList.mpr hkO)
                  l (Finset.mem_toList.mpr hlO) hkl) hxL) hxR
            have hEnds : right k ≠ left l := by
              intro h
              exact hxy (hxEq.symm.trans (h.trans hyEq))
            exact hxEq.symm ▸ hyEq.symm ▸
              hC (hrightC k hkO) (hleftC l hlO) hEnds
    exact hchainList O.toList O.nodup_toList (fun k hk => Finset.mem_toList.mp hk)
  have hheadC : ∀ x, x ∈ blocks.head? → x ∈ C := by
    intro x hx
    cases hlist : O.toList with
    | nil => simp [blocks, hlist] at hx
    | cons k ks =>
      have hkO : k ∈ O := Finset.mem_toList.mp (by simp [hlist])
      have hxEq : left k = x := by simpa [blocks, hlist, block, ordinaryBlock] using hx
      exact hxEq ▸ hleftC k hkO
  have hlastC : ∀ x, x ∈ blocks.getLast? → x ∈ C := by
    have hlast : ∀ l : List V, (∀ k ∈ l, k ∈ O) →
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
          have hxEq : right k = x := by simpa [block, ordinaryBlock] using hx'
          exact hxEq.symm ▸ hrightC k hkO
        · have hx' : x ∈ (ks.flatMap block).getLast? := by
            change x ∈ (block k ++ ks.flatMap block).getLast? at hx
            rw [List.getLast?_append_of_ne_nil _ htail] at hx
            simpa [List.flatMap_cons] using hx
          exact ih (by
            intro q hq
            exact hmem q (by simp [hq])) x hx'
    exact hlast O.toList (fun k hk => Finset.mem_toList.mp hk)
  have hmem : ∀ x, x ∈ blocks ↔ ∃ k ∈ O,
      x = left k ∨ x = k ∨ x = right k := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, hkList, hxBlock⟩ := List.mem_flatMap.mp hx
      have hkO := Finset.mem_toList.mp hkList
      simp only [block, ordinaryBlock, List.mem_cons, List.not_mem_nil, or_false] at hxBlock
      rcases hxBlock with h | h | h
      · exact ⟨k, hkO, Or.inl h⟩
      · exact ⟨k, hkO, Or.inr (Or.inl h)⟩
      · exact ⟨k, hkO, Or.inr (Or.inr h)⟩
    · rintro ⟨k, hk, h⟩
      apply List.mem_flatMap.mpr
      refine ⟨k, Finset.mem_toList.mpr hk, ?_⟩
      rcases h with h | h | h
      · simp [block, ordinaryBlock, h]
      · simp [block, ordinaryBlock, h]
      · simp [block, ordinaryBlock, h]
  exact ⟨hnodup, hchain, hheadC, hlastC, hmem⟩

end SplitGraphSmallRowsBlocks
