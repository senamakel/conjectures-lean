import Implications.SplitGraphTrees

/-!
The full triple-row case in the connectivity-two split-graph path argument.
-/

namespace SplitGraphTripleRowPath

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

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

private theorem clique_list_chain
    (G : SimpleGraph V) (C : Finset V) (hC : G.IsClique (C : Set V))
    (l : List V) (hnodup : l.Nodup) (hsub : ∀ x ∈ l, x ∈ C) : l.IsChain G.Adj := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y l₁ l₂ heq
  have hx : x ∈ l := by rw [heq]; simp
  have hy : y ∈ l := by rw [heq]; simp
  have hxy : x ≠ y := by
    intro h
    subst y
    have hc := (List.nodup_iff_count_le_one.mp hnodup) x
    rw [heq] at hc
    simp [List.count_append, List.count_cons] at hc
    omega
  exact hC (hsub x hx) (hsub y hy) hxy

private theorem chain_join {G : SimpleGraph V} {L R : List V} {x y : V}
    (hL : L.IsChain G.Adj) (hR : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y) (hxy : G.Adj x y) :
    (L ++ R).IsChain G.Adj := by
  apply hL.append hR
  intro a ha b hb
  have he : x = a := by simpa [hx] using ha
  have he' : y = b := by simpa [hy] using hb
  exact he ▸ he' ▸ hxy

/-- With distinct non-`t` clique neighbours for two labels, all three labels
and the clique can be ordered into a Hamiltonian path. -/
private theorem path_of_distinct_attachments
    (G : SimpleGraph V) (C I : Finset V) (t i j k x y : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hi : i ∈ I) (hj : j ∈ I) (hk : k ∈ I)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hI : I = {i,j,k}) (ht : t ∈ C) (hxC : x ∈ C) (hyC : y ∈ C)
    (hxt : x ≠ t) (hyt : y ≠ t) (hxy : x ≠ y)
    (hti : G.Adj t i) (htk : G.Adj t k)
    (hxi : G.Adj x i) (hyj : G.Adj y j) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let D := C.erase t
  let M := D.erase x |>.erase y
  let middle : List V := x :: (M.toList ++ [y])
  let prefix : List V := [k,t,i]
  let path : List V := prefix ++ middle ++ [j]
  have hmiddleNodup : middle.Nodup := by simp [middle, M, D, hxy]
  have hmiddleFin : middle.toFinset = D := by
    ext v
    simp [middle, M, D, Finset.mem_erase, and_assoc, and_left_comm, and_comm, hxy]
  have hmiddleSub : ∀ v ∈ middle, v ∈ C := by
    intro v hv
    have hvD : v ∈ D := by simpa [hmiddleFin] using List.mem_toFinset.mpr hv
    exact (Finset.mem_erase.mp hvD).2
  have hmiddleChain := clique_list_chain G C hC middle hmiddleNodup hmiddleSub
  have hmiddleHead : middle.head? = some x := by simp [middle]
  have hmiddleLast : middle.getLast? = some y := by simp [middle]
  have hiC : i ∉ C := fun h => (Finset.disjoint_left.mp hdisj) h hi
  have hjC : j ∉ C := fun h => (Finset.disjoint_left.mp hdisj) h hj
  have hkC : k ∉ C := fun h => (Finset.disjoint_left.mp hdisj) h hk
  have hti' : t ≠ i := by intro he; subst i; exact hiC ht
  have htk' : t ≠ k := by intro he; subst k; exact hkC ht
  have hprefixChain : prefix.IsChain G.Adj := by simp [prefix, hti, htk]
  have hprefixNodup : prefix.Nodup := by
    simp [prefix, hij, hik, hjk, hti', htk']
  have hprefixMiddle : (prefix ++ middle).Nodup := by
    rw [List.nodup_append']
    refine ⟨hprefixNodup, hmiddleNodup, ?_⟩
    intro v hv w hw he
    subst w
    have hv' : v = k ∨ v = t ∨ v = i := by simpa [prefix] using hv
    rcases hv' with rfl | rfl | rfl
    · exact hkC ((hmiddleSub v hw).trans he)
    · have htD : t ∉ D := by simp [D]
      have htm : t ∈ middle.toFinset := List.mem_toFinset.mpr hw
      rw [hmiddleFin] at htm
      exact htD htm
    · exact hiC ((hmiddleSub v hw).trans he)
  have hpathNodup : path.Nodup := by
    dsimp [path]
    rw [List.nodup_append']
    refine ⟨hprefixMiddle, by simp [hjC], ?_⟩
    intro v hv w hw he
    subst w
    rcases List.mem_append.mp hv with hvprefix | hvmiddle
    · have hv' : v = k ∨ v = t ∨ v = i := by simpa [prefix] using hvprefix
      rcases hv' with rfl | rfl | rfl
      · exact hjk
      · exact hjC ht
      · exact hij
    · exact hjC (hmiddleSub v hvmiddle)
  have hfirst : (prefix ++ middle).IsChain G.Adj :=
    chain_join hprefixChain hmiddleChain (by simp [prefix]) hmiddleHead hxi.symm
  have hpathChain : path.IsChain G.Adj := by
    have h := chain_join hfirst (List.IsChain.singleton j) hmiddleLast (by simp) hyj
    simpa [path] using h
  have hcover : ∀ v : V, v ∈ path := by
    intro v
    have hv : v ∈ C ∪ I := by rw [← hpartition]; exact Finset.mem_univ v
    rcases Finset.mem_union.mp hv with hvC | hvI
    · by_cases hvt : v = t
      · subst v
        simp [path, prefix]
      · have hvD : v ∈ D := Finset.mem_erase.mpr ⟨hvt, hvC⟩
        have hvm : v ∈ middle := List.mem_toFinset.mp (by rw [hmiddleFin]; exact hvD)
        simp [path, prefix, hvm]
    · rw [hI] at hvI
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvI
      rcases hvI with rfl | rfl | rfl <;> simp [path, prefix]
  exact hamiltonian_of_list G path (by simp [path, prefix]) hpathNodup hpathChain hcover

/-- A full triple row plus the connectivity-two row bounds forces a Hamiltonian
path through the clique and all three independent vertices. -/
theorem hamiltonian_of_split_partition_triple_row_of_rows
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (ht : t ∈ C) (hroweq : row G I t = I) (hIcard : I.card = 3)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hIeq⟩ := Finset.card_eq_three.mp hIcard
  have haI : a ∈ I := by rw [hIeq]; simp
  have hbI : b ∈ I := by rw [hIeq]; simp
  have hcI : c ∈ I := by rw [hIeq]; simp
  have adjT (i : V) (hi : i ∈ I) : G.Adj t i := by
    have hm : i ∈ row G I t := by simpa [hroweq] using hi
    exact (Finset.mem_filter.mp hm).2
  have second (i : V) (hi : i ∈ I) : ∃ x ∈ C, x ≠ t ∧ G.Adj x i := by
    obtain ⟨q,hq,d,hd,hqd,hqi,hdi⟩ := hdeg i hi
    by_cases hqt : q = t
    · subst q
      exact ⟨d,hd,by intro he; subst d; exact hqd rfl,hdi⟩
    · exact ⟨q,hq,hqt,hqi⟩
  obtain ⟨x,hxC,hxt,hxa⟩ := second a haI
  obtain ⟨y,hyC,hyt,hyb⟩ := second b hbI
  obtain ⟨z,hzC,hzt,hzc⟩ := second c hcI
  by_cases hxy : x = y
  · by_cases hxz : x = z
    · subst y
      subst z
      by_cases hextra : ∃ u ∈ C, u ≠ t ∧ u ≠ x
      · obtain ⟨u,hu,hut,hux⟩ := hextra
        have hrowpos : (row G I u).Nonempty := by
          by_contra he
          have hempty : row G I u = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
          have hd := hdiff t ht u hu (by intro heq; exact hut heq.symm)
          have hle : 3 ≤ (rowDiff G I t u).card := by
            rw [rowDiff, hroweq, hempty]
            simp [hIcard]
          omega
        obtain ⟨i,hi⟩ := hrowpos
        have hiI : i ∈ I := (Finset.mem_filter.mp hi).1
        have hui : G.Adj u i := (Finset.mem_filter.mp hi).2
        have hmemI : i = a ∨ i = b ∨ i = c := by
          rw [hIeq] at hiI
          simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm,
            or_comm, or_left_comm, or_assoc] using hiI
        rcases hmemI with rfl | rfl | rfl
        · exact path_of_distinct_attachments G C I t a b c u x hC hdisj hpartition
            haI hbI hcI hab hac hbc hIeq ht hu hxC hut hxt hxa hyb
            (adjT a haI) (adjT c hcI) hui hyb
        · exact path_of_distinct_attachments G C I t b a c u x hC hdisj hpartition
            hbI haI hcI hab.symm hbc hac.symm hIeq ht hu hxC hut hxt hyb hxa
            (adjT b hbI) (adjT c hcI) hui hxa
        · exact path_of_distinct_attachments G C I t c a b u x hC hdisj hpartition
            hcI haI hbI hac.symm hbc.symm hab hIeq ht hu hxC hut hxt hzc hxa
            (adjT c hcI) (adjT b hbI) hui hxa
      · have hCsub : C ⊆ {t,x} := by
          intro u hu
          by_cases hut : u = t
          · simp [hut]
          by_cases hux : u = x
          · simp [hux]
          exact (hextra ⟨u,hu,hut,hux⟩).elim
        have hCeq : C = {t,x} := by
          apply Finset.Subset.antisymm hCsub
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact ht
          · exact hxC
        let path : List V := [a,t,b,x,c]
        have hti : t ∉ I := fun hi => (Finset.disjoint_left.mp hdisj) ht hi
        have hxi : x ∉ I := fun hi => (Finset.disjoint_left.mp hdisj) hxC hi
        have hn : path.Nodup := by simp [path, hab, hac, hbc, hti, hxi, hxt]
        have hcAdj : G.Adj x c := hzc
        have hchain : path.IsChain G.Adj := by
          simp [path, adjT a haI, adjT b hbI, hxa, hcAdj]
        have hcover : ∀ v : V, v ∈ path := by
          intro v
          have hv : v ∈ C ∪ I := by rw [← hpartition]; exact Finset.mem_univ v
          rcases Finset.mem_union.mp hv with hvC | hvI
          · rw [hCeq] at hvC
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvC
            rcases hvC with rfl | rfl <;> simp [path]
          · rw [hIeq] at hvI
            simp only [Finset.mem_insert, Finset.mem_singleton] at hvI
            rcases hvI with rfl | rfl | rfl <;> simp [path]
        exact hamiltonian_of_list G path (by simp [path]) hn hchain hcover
    · exact path_of_distinct_attachments G C I t a c b x z hC hdisj hpartition
        haI hcI hbI hac hbc.symm hab.symm hIeq ht hxC hzC hxt hzt hxz
        (adjT a haI) (adjT b hbI) hxa hzc
  · exact path_of_distinct_attachments G C I t a b c x y hC hdisj hpartition
      haI hbI hcI hab hac hbc hIeq ht hxC hyC hxt hyt hxy
      (adjT a haI) (adjT c hcI) hxa hyb
  
end SplitGraphTripleRowPath
