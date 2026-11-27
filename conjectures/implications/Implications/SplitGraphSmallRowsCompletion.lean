import Implications.SplitGraphSmallRowsThree

/-! Complete exceptional split-graph prefixes using ordinary selected blocks. -/

namespace SplitGraphSmallRowsCompletion

open SplitGraphSmallRowsBlocks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty clique-ended prefix can be completed when each independent
vertex outside the prefix has two selected neighbors, those selections have
no repetitions, and neither selected neighbor already occurs in the prefix. -/
theorem hamiltonian_of_selected_prefix
    (G : SimpleGraph V) (C I S : Finset V) (pref : List V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hprefNe : pref ≠ []) (hprefNodup : pref.Nodup) (hprefChain : pref.IsChain G.Adj)
    (hprefLastC : ∀ v, v ∈ pref.getLast? → v ∈ C)
    (hspecial : ∀ i ∈ I, i ∈ pref ↔ i ∈ S)
    (left right : V → V)
    (hleftC : ∀ k ∈ I, left k ∈ C) (hrightC : ∀ k ∈ I, right k ∈ C)
    (hleftAdj : ∀ k ∈ I, G.Adj (left k) k)
    (hrightAdj : ∀ k ∈ I, G.Adj (right k) k)
    (hneq : ∀ k ∈ I, left k ≠ right k)
    (havoid : ∀ k ∈ I \ S, left k ∉ pref ∧ right k ∉ pref)
    (hunique : ∀ x ∈ C, ∀ k ∈ I \ S, ∀ l ∈ I \ S,
      (left k = x ∨ right k = x) → (left l = x ∨ right l = x) → k = l) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let O := I \ S
  have hO : O ⊆ I := Finset.sdiff_subset
  let rest := O.toList.flatMap (ordinaryBlock left right)
  obtain ⟨hnodup,hchain,hhead,hlast,hmem⟩ :=
    ordinary_blocks_nodup_chain_ends G C I O hC hdisj hO left right
      (fun k hk => hleftC k (hO hk)) (fun k hk => hrightC k (hO hk))
      (fun k hk => hleftAdj k (hO hk)) (fun k hk => hrightAdj k (hO hk))
      (fun k hk => hneq k (hO hk)) hunique
  let D := C.filter fun x => x ∉ pref ++ rest
  have hD {x : V} : x ∈ D.toList ↔ x ∈ C ∧ x ∉ pref ++ rest := by simp [D]
  have hsep : ∀ x ∈ pref, x ∉ rest := by
    intro x hx hrest
    obtain ⟨k,hk,hleft | rfl | hright⟩ := (hmem x).mp hrest
    · exact (havoid k hk).1 (hleft ▸ hx)
    · exact (Finset.mem_sdiff.mp hk).2 ((hspecial x (hO hk)).mp hx)
    · exact (havoid k hk).2 (hright ▸ hx)
  refine SplitGraphSmallRowsThree.hamiltonian_of_prefix_and_remaining_chain
    G C hC pref rest D.toList hprefNodup hprefChain hprefLastC hnodup hchain hhead hlast
    hsep (Finset.nodup_toList D) (fun x hx => (hD.mp hx).1)
    (fun x hx htail => (hD.mp htail).2 hx) ?_ (by simp [hprefNe])
  intro x
  have hx := Finset.mem_univ x
  rw [hpartition] at hx
  rcases Finset.mem_union.mp hx with hxC | hxI
  · by_cases h : x ∈ pref ++ rest
    · exact Or.inl h
    · exact Or.inr (hD.mpr ⟨hxC,h⟩)
  · by_cases hs : x ∈ S
    · exact Or.inl (List.mem_append_left _ ((hspecial x hxI).mpr hs))
    · have ho : x ∈ O := Finset.mem_sdiff.mpr ⟨hxI,hs⟩
      exact Or.inl (List.mem_append_right _ ((hmem x).mpr ⟨x,ho,Or.inr (Or.inl rfl)⟩))

/-- Ordinary selections are disjoint from a prefix when all double rows
involve only special labels and every prefix clique vertex has a special
label selecting it. -/
theorem hamiltonian_of_selected_prefix_of_double_rows
    (G : SimpleGraph V) (C I S : Finset V) (pref : List V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hprefNe : pref ≠ []) (hprefNodup : pref.Nodup) (hprefChain : pref.IsChain G.Adj)
    (hprefLastC : ∀ v, v ∈ pref.getLast? → v ∈ C)
    (hspecial : ∀ i ∈ I, i ∈ pref ↔ i ∈ S)
    (left right : V → V)
    (hleftC : ∀ k ∈ I, left k ∈ C) (hrightC : ∀ k ∈ I, right k ∈ C)
    (hleftAdj : ∀ k ∈ I, G.Adj (left k) k)
    (hrightAdj : ∀ k ∈ I, G.Adj (right k) k)
    (hneq : ∀ k ∈ I, left k ≠ right k)
    (hcap : ∀ x ∈ C, (I.filter (fun i => left i = x ∨ right i = x)).card ≤ 2)
    (hdouble : ∀ x ∈ C, (I.filter (fun i => left i = x ∨ right i = x)).card = 2 →
      I.filter (fun i => left i = x ∨ right i = x) ⊆ S)
    (hprefixClique : ∀ x ∈ C, x ∈ pref →
      ∃ i ∈ I, i ∈ S ∧ (left i = x ∨ right i = x)) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  have huniq (x : V) (hx : x ∈ C) (k l : V) (hk : k ∈ I \ S) (hl : l ∈ I)
      (hkx : left k = x ∨ right k = x) (hlx : left l = x ∨ right l = x) : k = l := by
    by_contra hne
    let R := I.filter (fun i => left i = x ∨ right i = x)
    have hkR : k ∈ R := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hk).1,hkx⟩
    have hlR : l ∈ R := Finset.mem_filter.mpr ⟨hl,hlx⟩
    have hle : ({k,l} : Finset V).card ≤ R.card := by
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hkR
      · exact hlR
    have hpair : ({k,l} : Finset V).card = 2 := by simp [hne]
    have hcap' : R.card ≤ 2 := hcap x hx
    have hcard : R.card = 2 := by omega
    exact (Finset.mem_sdiff.mp hk).2 (hdouble x hx hcard hkR)
  refine hamiltonian_of_selected_prefix G C I S pref hC hdisj hpartition hprefNe hprefNodup
    hprefChain hprefLastC hspecial left right hleftC hrightC hleftAdj hrightAdj hneq ?_ ?_
  · intro k hk
    have hkI := (Finset.mem_sdiff.mp hk).1
    have hav (x : V) (hx : x ∈ C) (hkx : left k = x ∨ right k = x) : x ∉ pref := by
      intro hp
      obtain ⟨l,hlI,hlS,hlx⟩ := hprefixClique x hx hp
      have heq := huniq x hx k l hk hlI hkx hlx
      exact (Finset.mem_sdiff.mp hk).2 (heq.symm ▸ hlS)
    exact ⟨hav (left k) (hleftC k hkI) (Or.inl rfl),
      hav (right k) (hrightC k hkI) (Or.inr rfl)⟩
  · intro x hx k hk l hl hkx hlx
    exact huniq x hx k l hk (Finset.mem_sdiff.mp hl).1 hkx hlx

end SplitGraphSmallRowsCompletion

#print axioms SplitGraphSmallRowsCompletion.hamiltonian_of_selected_prefix
#print axioms SplitGraphSmallRowsCompletion.hamiltonian_of_selected_prefix_of_double_rows
