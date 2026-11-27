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
          have hxe : right k ≠ c := by
            intro h
            exact hnotC k hkO (Or.inr h)
          have hkl' := hunique (right k) (hrightC k (Finset.mem_sdiff.mp hkO).1)
            hxe k (Finset.mem_sdiff.mp hkO).1 l (Finset.mem_sdiff.mp hlO).1
            (Or.inr rfl) (Or.inl (hxEq.trans hyEq))
          have hxy : right k ≠ left l := by
            intro h
            exact hkl (by simpa [h] using hkl')
          exact hxEq ▸ hyEq ▸ hC (hrightC k (Finset.mem_sdiff.mp hkO).1)
            (hleftC l (Finset.mem_sdiff.mp hlO).1) hxy
    change (others.toList.flatMap block).IsChain G.Adj
    exact hchain others.toList others.nodup_toList
      (fun k hk => Finset.mem_toList.mp hk)

end SplitGraphSmallRowsOneShared
