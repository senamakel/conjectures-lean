import Implications.SplitGraphSmallRows
import Implications.SplitGraphSmallRowsPath
import Implications.SplitGraphSmallRowsBlocks

/-!
The triangle alternative for three selected degree-two clique rows.
-/

namespace SplitGraphSmallRowsThree

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem hamiltonian_of_list
    (G : SimpleGraph V) (l : List V) (hne : l ≠ []) (hnodup : l.Nodup)
    (hchain : l.IsChain G.Adj) (hcover : ∀ v : V, v ∈ l) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let p := SimpleGraph.Walk.ofSupport l hne hchain
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport hne hchain] using hnodup
  have hvertices : ∀ v : V, v ∈ p.support := by
    intro v
    rw [SimpleGraph.Walk.support_ofSupport hne hchain]
    exact hcover v
  exact ⟨_, _, p, hp.isHamiltonian_of_mem hvertices⟩

/-- Append a disjoint chain of clique-ended blocks and then the unused clique
vertices to a prefix whose final vertex lies in the clique. -/
theorem hamiltonian_of_prefix_and_remaining_chain
    (G : SimpleGraph V) (C : Finset V) (hC : G.IsClique (C : Set V))
    (pref rest tail : List V)
    (hprefNodup : pref.Nodup) (hprefChain : pref.IsChain G.Adj)
    (hprefLastC : ∀ x, x ∈ pref.getLast? → x ∈ C)
    (hrestNodup : rest.Nodup) (hrestChain : rest.IsChain G.Adj)
    (hrestHeadC : ∀ x, x ∈ rest.head? → x ∈ C)
    (hrestLastC : ∀ x, x ∈ rest.getLast? → x ∈ C)
    (hprefRestDisjoint : ∀ x ∈ pref, x ∉ rest)
    (htailNodup : tail.Nodup) (htailC : ∀ x ∈ tail, x ∈ C)
    (hbaseTailDisjoint : ∀ x ∈ pref ++ rest, x ∉ tail)
    (hcover : ∀ x : V, x ∈ pref ++ rest ∨ x ∈ tail)
    (hne : pref ++ rest ++ tail ≠ []) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let base := pref ++ rest
  have hbaseNodup : base.Nodup := by
    simp only [base]
    rw [List.nodup_append']
    exact ⟨hprefNodup, hrestNodup, hprefRestDisjoint⟩
  have hbaseChain : base.IsChain G.Adj := by
    simp only [base]
    rw [List.isChain_append]
    refine ⟨hprefChain, hrestChain, ?_⟩
    intro x hx y hy
    exact hC (hprefLastC x hx) (hrestHeadC y hy) (by
      intro heq
      subst y
      exact hprefRestDisjoint x (List.mem_of_mem_getLast? hx)
        (List.mem_of_mem_head? hy))
  have hbaseLastC : ∀ x, x ∈ base.getLast? → x ∈ C := by
    intro x hx
    by_cases hrest : rest = []
    · subst rest
      have hlast : base.getLast? = pref.getLast? := by simp [base]
      rw [hlast] at hx
      exact hprefLastC x hx
    · have hlast : base.getLast? = rest.getLast? := by
        change (pref ++ rest).getLast? = rest.getLast?
        rw [List.getLast?_append_of_ne_nil _ hrest]
      rw [hlast] at hx
      exact hrestLastC x hx
  apply hamiltonian_of_list G (base ++ tail) (by simpa [base] using hne)
  · rw [List.nodup_append']
    refine ⟨hbaseNodup, htailNodup, List.disjoint_left.mpr (by
      intro x hx hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hbaseTailDisjoint x (List.mem_append_left _ hx) hy
      · exact hbaseTailDisjoint x (List.mem_append_right _ hx) hy)⟩
  · rw [List.isChain_append]
    refine ⟨hbaseChain, ?_, ?_⟩
    · rw [List.isChain_iff_forall_rel_of_append_cons_cons]
      intro x y l₁ l₂ heq
      have hx : x ∈ tail := by rw [heq]; simp
      have hy : y ∈ tail := by rw [heq]; simp
      have hxy : x ≠ y := by
        intro heqxy
        subst y
        have hcount := (List.nodup_iff_count_le_one.mp htailNodup) x
        rw [heq] at hcount
        simp [List.count_append] at hcount
        omega
      exact hC (htailC x hx) (htailC y hy) hxy
    · intro x hx y hy
      exact hC (hbaseLastC x hx) (htailC y (List.mem_of_mem_head? hy)) (by
        intro heqxy
        subst y
        exact hbaseTailDisjoint x (List.mem_of_mem_getLast? hx)
          (List.mem_of_mem_head? hy))
  · intro x
    rcases hcover x with hx | hx
    · exact List.mem_append_left _ (by simpa [base] using hx)
    · exact List.mem_append_right _ hx

omit [Fintype V] [DecidableEq V] in
/-- The six-vertex path through the three pair rows, starting at an independent
vertex and ending at a clique vertex. -/
theorem triangle_prefix_is_nodup_chain
    (G : SimpleGraph V) (C I : Finset V) (hdisj : Disjoint C I)
    (a b c x y z : V)
    (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : G.Adj a x) (hxb : G.Adj x b)
    (hby : G.Adj b y) (hyc : G.Adj y c) (hcz : G.Adj c z) :
    ([a, x, b, y, c, z] : List V).Nodup ∧
      ([a, x, b, y, c, z] : List V).IsChain G.Adj ∧
      ∀ v, v ∈ ([a, x, b, y, c, z] : List V).getLast? → v ∈ C := by
  have haC : a ∉ C := fun h => (Finset.disjoint_left.mp hdisj) h ha
  have hbC : b ∉ C := fun h => (Finset.disjoint_left.mp hdisj) h hb
  have hcC : c ∉ C := fun h => (Finset.disjoint_left.mp hdisj) h hc
  have hxI : x ∉ I := fun h => (Finset.disjoint_left.mp hdisj) hx h
  have hyI : y ∉ I := fun h => (Finset.disjoint_left.mp hdisj) hy h
  have hzI : z ∉ I := fun h => (Finset.disjoint_left.mp hdisj) hz h
  have hIC : ∀ i ∈ I, ∀ q ∈ C, i ≠ q := by
    intro i hi q hq heq
    subst q
    exact (Finset.disjoint_left.mp hdisj) hq hi
  have haxne := hIC a ha x hx
  have hayne := hIC a ha y hy
  have hazne := hIC a ha z hz
  have hxbne := (hIC b hb x hx).symm
  have hxcne := (hIC c hc x hx).symm
  have hbyne := hIC b hb y hy
  have hbzne := hIC b hb z hz
  have hycne := (hIC c hc y hy).symm
  have hczne := hIC c hc z hz
  have hnodup : ([a, x, b, y, c, z] : List V).Nodup := by
    simp [hab, hac, hbc, hxy, hxz, hyz, haxne, hayne, hazne,
      hxbne, hxcne, hbyne, hbzne, hycne, hczne]
  have hchain : ([a, x, b, y, c, z] : List V).IsChain G.Adj := by
    simp [List.isChain_cons, hax, hxb, hby, hyc, hcz]
  refine ⟨hnodup, hchain, ?_⟩
  intro v hv
  have hvz : z = v := by simpa using hv
  exact hvz ▸ hz

/-- A triangle of selected pair rows supplies the prefix; any disjoint chain
of the remaining clique-ended blocks and the unused clique tail completes it. -/
theorem hamiltonian_of_triangle_block_and_remaining_chain
    (G : SimpleGraph V) (C I : Finset V) (hC : G.IsClique (C : Set V))
    (hdisj : Disjoint C I) (a b c x y z : V)
    (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I)
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : G.Adj a x) (hxb : G.Adj x b)
    (hby : G.Adj b y) (hyc : G.Adj y c) (hcz : G.Adj c z)
    (rest tail : List V)
    (hrestNodup : rest.Nodup) (hrestChain : rest.IsChain G.Adj)
    (hrestHeadC : ∀ v, v ∈ rest.head? → v ∈ C)
    (hrestLastC : ∀ v, v ∈ rest.getLast? → v ∈ C)
    (hprefixRestDisjoint : ∀ v ∈ [a, x, b, y, c, z], v ∉ rest)
    (htailNodup : tail.Nodup) (htailC : ∀ v ∈ tail, v ∈ C)
    (hbaseTailDisjoint : ∀ v ∈ ([a, x, b, y, c, z] ++ rest), v ∉ tail)
    (hcover : ∀ v : V, v ∈ [a, x, b, y, c, z] ++ rest ∨ v ∈ tail)
    (hne : [a, x, b, y, c, z] ++ rest ++ tail ≠ []) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨hprefNodup, hprefChain, hprefLastC⟩ := triangle_prefix_is_nodup_chain
    G C I hdisj a b c x y z ha hb hc hx hy hz hab hac hbc hxy hxz hyz
    hax hxb hby hyc hcz
  exact hamiltonian_of_prefix_and_remaining_chain G C hC
    [a, x, b, y, c, z] rest tail hprefNodup hprefChain hprefLastC
    hrestNodup hrestChain hrestHeadC hrestLastC hprefixRestDisjoint
    htailNodup htailC hbaseTailDisjoint hcover hne

variable {α : Type*} [DecidableEq α]

private theorem intersecting_pair_rows
    (s t : Finset α) (hs : s.card = 2) (ht : t.card = 2)
    (hdiff : (s \ t ∪ t \ s).card ≤ 2) :
    ∃ x, x ∈ s ∧ x ∈ t := by
  classical
  by_contra hn
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      exact False.elim (hn ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)
    · simp
  have hEq : s ∪ t = s \ t ∪ t \ s := by
    rw [← Finset.symmDiff_eq_union hdisj, Finset.symmDiff_def]
  have hst : (s ∪ t).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hs, ht]
  rw [hEq] at hst
  omega

/-- Three distinct, pairwise-intersecting two-element rows with no common
element are exactly the three edges of a triangle. -/
theorem three_pair_rows_are_triangle
    (F : Finset (Finset α))
    (hcardF : F.card = 3)
    (hcard : ∀ s ∈ F, s.card = 2)
    (hint : ∀ s ∈ F, ∀ t ∈ F, s ≠ t → ∃ x, x ∈ s ∧ x ∈ t)
    (hnocenter : ¬ ∃ x, ∀ s ∈ F, x ∈ s) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      F = {({a,b} : Finset α), {b,c}, {a,c}} := by
  classical
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain hcenter | htriangle :=
    SplitGraphSmallRows.pairwise_intersecting_two_sets F hne hcard hint
  · exact (hnocenter hcenter).elim
  · obtain ⟨a,b,c,hab,hac,hbc,hsub⟩ := htriangle
    have hFsub : F ⊆ ({({a,b} : Finset α), {b,c}, {a,c}} : Finset (Finset α)) := by
      intro s hs
      have hs' := hsub s hs
      have hcardS := hcard s hs
      have hsTriple : s ⊆ ({a,b,c} : Finset α) := by simpa using hs'
      have hpair : s = {a,b} ∨ s = {b,c} ∨ s = {a,c} := by
        rcases Finset.card_eq_two.mp hcardS with ⟨x,y,hxy,heq⟩
        have hx : x = a ∨ x = b ∨ x = c := by
          have hxmem : x ∈ s := by rw [heq]; simp
          have := hsTriple hxmem
          simpa using this
        have hy : y = a ∨ y = b ∨ y = c := by
          have hymem : y ∈ s := by rw [heq]; simp
          have := hsTriple hymem
          simpa using this
        rcases hx with hxa | hxb | hxc <;>
          rcases hy with hya | hyb | hyc <;>
          subst x <;> subst y <;> simp_all [Finset.pair_comm]
      rcases hpair with h | h | h <;> simp [h]
    have hp12 : ({a,b} : Finset α) ≠ {b,c} := by
      intro he
      have hc : c ∈ ({a,b} : Finset α) := he ▸ (by simp)
      simp [hac.symm, hbc.symm] at hc
    have hp13 : ({a,b} : Finset α) ≠ {a,c} := by
      intro he
      have hb : b ∈ ({a,c} : Finset α) := he.symm ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · exact hab hb.symm
      · exact hbc hb
    have hp23 : ({b,c} : Finset α) ≠ {a,c} := by
      intro he
      have hb : b ∈ ({a,c} : Finset α) := he ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · exact hab hb.symm
      · exact hbc hb
    have hp1 : ({a,b} : Finset α) ∉ ({({b,c} : Finset α), {a,c}} : Finset (Finset α)) := by
      simp [hp12, hp13]
    have htargetCard : ({({a,b} : Finset α), {b,c}, {a,c}} : Finset (Finset α)).card = 3 := by
      rw [Finset.card_insert_of_notMem hp1,
        Finset.card_insert_of_notMem (by simpa using hp23)]
      simp
    have hEq := Finset.eq_of_subset_of_card_le hFsub
      (by rw [hcardF, htargetCard])
    exact ⟨a,b,c,hab,hac,hbc,hEq⟩

/-- A three-element family of selected double rows with exact incidence two
has the triangle shape, and its three row indices map to the three distinct
pair sets. -/
theorem three_selected_rows_form_triangle
    {C I : Type*} [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq I]
    (clique : Finset C) (indep : Finset I) (S : Finset C)
    (selected : C → Finset I)
    (hSsub : S ⊆ clique) (hScard : S.card = 3)
    (hrowCard : ∀ q ∈ S, (selected q).card = 2)
    (hselectedSub : ∀ q ∈ S, selected q ⊆ indep)
    (hdegree : ∀ i ∈ indep, (clique.filter (fun q => i ∈ selected q)).card = 2)
    (hmeet : ∀ q ∈ S, ∀ d ∈ S, q ≠ d → ∃ i, i ∈ selected q ∧ i ∈ selected d) :
    ∃ x y z a b c, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      selected x = {a,b} ∧ selected y = {b,c} ∧ selected z = {a,c} := by
  classical
  let F : Finset (Finset I) := S.image selected
  have hnoCenter : ¬ ∃ i, ∀ q ∈ S, i ∈ selected q := by
    rintro ⟨i, hi⟩
    have hiI : i ∈ indep := by
      obtain ⟨q, hq⟩ := S.nonempty_iff_ne_empty.mpr (by intro h; rw [h] at hScard; simp at hScard)
      exact hselectedSub q hq (hi q hq)
    have hsub : S ⊆ clique.filter (fun q => i ∈ selected q) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨hSsub hq, hi q hq⟩
    have hle := Finset.card_le_card hsub
    rw [hdegree i hiI] at hle
    omega
  have hinj : Set.InjOn selected S := by
    intro q hq d hd heq
    by_contra hqd
    have hpairSub : ({q,d} : Finset C) ⊆ S := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hq
      · exact hd
    have hpairCard : ({q,d} : Finset C).card = 2 := by simp [hqd]
    have hdiffCard : (S \ {q,d}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hpairSub, hScard, hpairCard]
    have hdiffNonempty : (S \ {q,d}).Nonempty :=
      Finset.card_pos.mp (by omega : 0 < (S \ {q,d}).card)
    obtain ⟨e, heSD⟩ := hdiffNonempty
    have heS := (Finset.mem_sdiff.mp heSD).1
    have heNot := (Finset.mem_sdiff.mp heSD).2
    have hqe : e ≠ q := by
      intro h
      subst e
      exact heNot (by simp)
    have hde : e ≠ d := by
      intro h
      subst e
      exact heNot (by simp)
    have hthird : ∃ e ∈ S, e ≠ q ∧ e ≠ d := ⟨e, heS, hqe, hde⟩
    obtain ⟨e, he, hqe, hde⟩ := hthird
    obtain ⟨i, hiq, hie⟩ := hmeet q hq e he hqe.symm
    have hid : i ∈ selected d := by simpa [heq] using hiq
    have hiI : i ∈ indep := hselectedSub q hq hiq
    have hthree : ({q,d,e} : Finset C) ⊆ clique.filter (fun c => i ∈ selected c) := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hSsub hq, hiq⟩
      · exact Finset.mem_filter.mpr ⟨hSsub hd, hid⟩
      · exact Finset.mem_filter.mpr ⟨hSsub he, hie⟩
    have hthreeCard : ({q,d,e} : Finset C).card = 3 := by
      simp [hqd, hqe, hde, Ne.symm hqd, Ne.symm hqe, Ne.symm hde]
    have hle := Finset.card_le_card hthree
    rw [hdegree i hiI, hthreeCard] at hle
    omega
  have hFcard : F.card = 3 := by
    dsimp [F]
    rw [Finset.card_image_of_injOn hinj, hScard]
  have hFrows : ∀ A ∈ F, A.card = 2 := by
    intro A hA
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hA
    exact hrowCard q hq
  have hFmeet : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∃ i, i ∈ A ∧ i ∈ B := by
    intro A hA B hB hAB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hB
    have hqd : q ≠ d := by
      intro he
      apply hAB
      simpa [he]
    exact hmeet q hq d hd hqd
  have hFnoCenter : ¬ ∃ i, ∀ A ∈ F, i ∈ A := by
    rintro ⟨i, hi⟩
    apply hnoCenter
    refine ⟨i, ?_⟩
    intro q hq
    exact hi (selected q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  obtain ⟨a,b,c,hab,hac,hbc,hF⟩ :=
    three_pair_rows_are_triangle F hFcard hFrows hFmeet hFnoCenter
  have hmemAB : ({a,b} : Finset I) ∈ F := by rw [hF]; simp
  have hmemBC : ({b,c} : Finset I) ∈ F := by rw [hF]; simp
  have hmemAC : ({a,c} : Finset I) ∈ F := by rw [hF]; simp
  obtain ⟨x, hx, hxEq⟩ := Finset.mem_image.mp hmemAB
  obtain ⟨y, hy, hyEq⟩ := Finset.mem_image.mp hmemBC
  obtain ⟨z, hz, hzEq⟩ := Finset.mem_image.mp hmemAC
  have hxy : x ≠ y := by
    intro he
    have hEq : ({a,b} : Finset I) = {b,c} := by rw [← hxEq, he, hyEq]
    have hc : c ∈ ({a,b} : Finset I) := hEq.symm ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc
    · exact hac hc.symm
    · exact hbc hc.symm
  have hxz : x ≠ z := by
    intro he
    have hEq : ({a,b} : Finset I) = {a,c} := hxEq.symm.trans (by simpa [he] using hzEq)
    have hbmem : b ∈ ({a,c} : Finset I) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
    rcases hbmem with h | h
    · exact hab h.symm
    · exact hbc h
  have hyz : y ≠ z := by
    intro he
    have hEq : ({b,c} : Finset I) = {a,c} := hyEq.symm.trans (by simpa [he] using hzEq)
    have hbmem : b ∈ ({a,c} : Finset I) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
    rcases hbmem with h | h
    · exact hab h.symm
    · exact hbc h
  exact ⟨x,y,z,a,b,c,hx,hy,hz,hxy,hxz,hyz,hab,hac,hbc,hxEq,hyEq,hzEq⟩

/-- Specialize the finite-family result to selected endpoint incidences in a
split graph. The original row bounds force any selected double row to equal
the full graph row, so the symmetric-difference bound makes those rows
pairwise intersecting. -/
theorem chosen_three_double_rows_form_triangle
    (G : SimpleGraph V) (C I : Finset V) (left right : V → V)
    (hleftC : ∀ i ∈ I, left i ∈ C) (hrightC : ∀ i ∈ I, right i ∈ C)
    (hleftAdj : ∀ i ∈ I, G.Adj (left i) i)
    (hrightAdj : ∀ i ∈ I, G.Adj (right i) i)
    (hneq : ∀ i ∈ I, left i ≠ right i)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 2)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hcount : (C.filter (fun q => (I.filter (fun i => left i = q ∨ right i = q)).card = 2)).card = 3) :
    ∃ x y z a b c, x ∈ C ∧ y ∈ C ∧ z ∈ C ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      I.filter (fun i => left i = x ∨ right i = x) = {a,b} ∧
      I.filter (fun i => left i = y ∨ right i = y) = {b,c} ∧
      I.filter (fun i => left i = z ∨ right i = z) = {a,c} := by
  classical
  let selected : V → Finset V := fun q => I.filter (fun i => left i = q ∨ right i = q)
  let S : Finset V := C.filter (fun q => (selected q).card = 2)
  have hSsub : S ⊆ C := fun q hq => (Finset.mem_filter.mp hq).1
  have hSCard : S.card = 3 := hcount
  have hrowCard : ∀ q ∈ S, (selected q).card = 2 := fun q hq =>
    (Finset.mem_filter.mp hq).2
  have hselectedSub : ∀ q ∈ S, selected q ⊆ I := by
    intro q hq i hi
    exact (Finset.mem_filter.mp hi).1
  have hdegree : ∀ i ∈ I, (C.filter (fun q => i ∈ selected q)).card = 2 := by
    intro i hi
    have hEq : C.filter (fun q => i ∈ selected q) = {left i, right i} := by
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_filter.mp hq
        have hi' := Finset.mem_filter.mp hq'.2
        rcases hi'.2 with heq | heq
        · exact Finset.mem_insert.mpr (Or.inl heq.symm)
        · simp [heq.symm]
      · intro hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with hq | hq
        · subst q
          exact Finset.mem_filter.mpr ⟨hleftC i hi,
            Finset.mem_filter.mpr ⟨hi, Or.inl rfl⟩⟩
        · subst q
          exact Finset.mem_filter.mpr ⟨hrightC i hi,
            Finset.mem_filter.mpr ⟨hi, Or.inr rfl⟩⟩
    rw [hEq]
    simp [hneq i hi]
  have hselectedSubRow : ∀ q ∈ C, selected q ⊆ row G I q := by
    intro q hq i hi
    have hi' := Finset.mem_filter.mp hi
    rcases hi'.2 with heq | heq
    · rw [row]
      exact Finset.mem_filter.mpr ⟨hi'.1, heq ▸ hleftAdj i hi'.1⟩
    · rw [row]
      exact Finset.mem_filter.mpr ⟨hi'.1, heq ▸ hrightAdj i hi'.1⟩
  have hselectedEq : ∀ q ∈ S, selected q = row G I q := by
    intro q hq
    apply Finset.eq_of_subset_of_card_le (hselectedSubRow q (hSsub hq))
    rw [hrowCard q hq]
    exact hrow q (hSsub hq)
  have hmeet : ∀ q ∈ S, ∀ d ∈ S, q ≠ d → ∃ i, i ∈ selected q ∧ i ∈ selected d := by
    intro q hq d hd hqd
    rw [hselectedEq q hq, hselectedEq d hd]
    apply intersecting_pair_rows
    · rw [← hselectedEq q hq]
      exact hrowCard q hq
    · rw [← hselectedEq d hd]
      exact hrowCard d hd
    · simpa [rowDiff] using hdiff q (hSsub hq) d (hSsub hd) hqd
  obtain ⟨x,y,z,a,b,c,hx,hy,hz,hxy,hxz,hyz,hab,hac,hbc,hxEq,hyEq,hzEq⟩ :=
    three_selected_rows_form_triangle C I S selected hSsub hSCard hrowCard
      hselectedSub hdegree hmeet
  exact ⟨x,y,z,a,b,c,hSsub hx,hSsub hy,hSsub hz,hxy,hxz,hyz,hab,hac,hbc,hxEq,hyEq,hzEq⟩

/-- The non-common-label case with exactly three selected double rows. The
triangle prefix is followed by the ordinary blocks for every other independent
vertex, then the clique vertices not yet used. -/
theorem hamiltonian_of_split_partition_three_double_rows
    (G : SimpleGraph V) (C I : Finset V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (left right : V → V)
    (hleftC : ∀ i ∈ I, left i ∈ C) (hrightC : ∀ i ∈ I, right i ∈ C)
    (hleftAdj : ∀ i ∈ I, G.Adj (left i) i)
    (hrightAdj : ∀ i ∈ I, G.Adj (right i) i)
    (hneq : ∀ i ∈ I, left i ≠ right i)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 2)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hcount : (C.filter (fun q => (I.filter (fun i => left i = q ∨ right i = q)).card = 2)).card = 3)
    (huniv : (Finset.univ : Finset V).Nonempty) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  obtain ⟨x,y,z,a,b,c,hxC,hyC,hzC,hxy,hxz,hyz,hab,hac,hbc,
      hrowX,hrowY,hrowZ⟩ := chosen_three_double_rows_form_triangle
    G C I left right hleftC hrightC hleftAdj hrightAdj hneq hrow hdiff hcount
  let special : Finset V := {a,b,c}
  let O : Finset V := I \ special
  have hOSub : O ⊆ I := Finset.sdiff_subset
  have hS : C.filter (fun q => (I.filter (fun i => left i = q ∨ right i = q)).card = 2) = {x,y,z} := by
    have htriSub : ({x,y,z} : Finset V) ⊆
        C.filter (fun q => (I.filter (fun i => left i = q ∨ right i = q)).card = 2) := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hxC, by rw [hrowX]; simp [hab]⟩
      · exact Finset.mem_filter.mpr ⟨hyC, by rw [hrowY]; simp [hbc]⟩
      · exact Finset.mem_filter.mpr ⟨hzC, by rw [hrowZ]; simp [hac]⟩
    have htriCard : ({x,y,z} : Finset V).card = 3 := by simp [hxy, hxz, hyz]
    have hEq := Finset.eq_of_subset_of_card_le htriSub (by rw [hcount, htriCard])
    exact hEq.symm
  have hselectedBound : ∀ q ∈ C,
      (I.filter (fun i => left i = q ∨ right i = q)).card ≤ 2 := by
    intro q hq
    exact (Finset.card_le_card (by
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hadj : G.Adj q i := by
        rcases hi'.2 with heq | heq
        · exact heq ▸ hleftAdj i hi'.1
        · exact heq ▸ hrightAdj i hi'.1
      exact Finset.mem_filter.mpr ⟨hi'.1, hadj⟩)).trans (hrow q hq)
  have hselectedAtSpecial : ∀ q ∈ ({x,y,z} : Finset V),
      I.filter (fun i => left i = q ∨ right i = q) ⊆ special := by
    intro q hq i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq
    · subst q
      rw [hrowX] at hi
      simp only [special, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · subst q
      rw [hrowY] at hi
      simp only [special, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      rcases hi with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · subst q
      rw [hrowZ] at hi
      simp only [special, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  have hOavoidSpecial : ∀ k ∈ O, left k ∉ ({x,y,z} : Finset V) ∧
      right k ∉ ({x,y,z} : Finset V) := by
    intro k hk
    have hkI := (Finset.mem_sdiff.mp hk).1
    constructor <;> intro h
    · have hkrow : k ∈ I.filter (fun i => left i = left k ∨ right i = left k) :=
        Finset.mem_filter.mpr ⟨hkI, Or.inl rfl⟩
      have hknot := (Finset.mem_sdiff.mp hk).2
      exact hknot (hselectedAtSpecial (left k) h hkrow)
    · have hkrow : k ∈ I.filter (fun i => left i = right k ∨ right i = right k) :=
        Finset.mem_filter.mpr ⟨hkI, Or.inr rfl⟩
      have hknot := (Finset.mem_sdiff.mp hk).2
      exact hknot (hselectedAtSpecial (right k) h hkrow)
  have hunique : ∀ q ∈ C, ∀ k ∈ O, ∀ l ∈ O,
      (left k = q ∨ right k = q) → (left l = q ∨ right l = q) → k = l := by
    intro q hq k hk l hl hqk hql
    by_cases hqS : q ∈ ({x,y,z} : Finset V)
    · have hkr : k ∈ I.filter (fun i => left i = q ∨ right i = q) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hk).1, hqk⟩
      have hksub := hselectedAtSpecial q hqS hkr
      have hknot := (Finset.mem_sdiff.mp hk).2
      exact False.elim (hknot hksub)
    · have hcard : (I.filter (fun i => left i = q ∨ right i = q)).card ≤ 1 := by
        have hle := hselectedBound q hq
        have hneTwo : (I.filter (fun i => left i = q ∨ right i = q)).card ≠ 2 := by
          intro heq
          exact hqS (by
            rw [← hS]
            exact Finset.mem_filter.mpr ⟨hq, heq⟩)
        omega
      have hpairs : ({k,l} : Finset V) ⊆ I.filter (fun i => left i = q ∨ right i = q) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hk).1, hqk⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hl).1, hql⟩
      by_contra hkl
      have hpairsCard : ({k,l} : Finset V).card = 2 := by simp [hkl]
      have := Finset.card_le_card hpairs
      omega
  let rest := O.toList.flatMap (SplitGraphSmallRowsBlocks.ordinaryBlock left right)
  have hblocks := SplitGraphSmallRowsBlocks.ordinary_blocks_nodup_chain_ends
      G C I O hC hdisj hOSub left right
      (fun k hk => hleftC k (hOSub hk)) (fun k hk => hrightC k (hOSub hk))
      (fun k hk => hleftAdj k (hOSub hk)) (fun k hk => hrightAdj k (hOSub hk))
      (fun k hk => hneq k (hOSub hk)) hunique
  have hrestNodup : rest.Nodup := by
    simpa [rest] using hblocks.1
  have hrestChain : rest.IsChain G.Adj := by
    simpa [rest] using hblocks.2.1
  have hrestHeadC : ∀ v, v ∈ rest.head? → v ∈ C := by
    simpa [rest] using hblocks.2.2.1
  have hrestLastC : ∀ v, v ∈ rest.getLast? → v ∈ C := by
    simpa [rest] using hblocks.2.2.2.1
  have hrestMem : ∀ v, v ∈ rest ↔ ∃ k ∈ O,
      v = left k ∨ v = k ∨ v = right k := by
    simpa [rest] using hblocks.2.2.2.2
  have hselectedAdj (q i : V) (hi : i ∈ I.filter (fun j => left j = q ∨ right j = q)) :
      G.Adj q i := by
    have hi' := Finset.mem_filter.mp hi
    rcases hi'.2 with h | h
    · exact h ▸ hleftAdj i hi'.1
    · exact h ▸ hrightAdj i hi'.1
  have haX : a ∈ I.filter (fun i => left i = x ∨ right i = x) := by
    rw [hrowX]
    simp
  have hbX : b ∈ I.filter (fun i => left i = x ∨ right i = x) := by
    rw [hrowX]
    simp
  have hbY : b ∈ I.filter (fun i => left i = y ∨ right i = y) := by
    rw [hrowY]
    simp
  have hcY : c ∈ I.filter (fun i => left i = y ∨ right i = y) := by
    rw [hrowY]
    simp
  have hcZ : c ∈ I.filter (fun i => left i = z ∨ right i = z) := by
    rw [hrowZ]
    simp
  have hax : G.Adj a x := (hselectedAdj x a haX).symm
  have hxb : G.Adj x b := hselectedAdj x b hbX
  have hby : G.Adj b y := (hselectedAdj y b hbY).symm
  have hyc : G.Adj y c := hselectedAdj y c hcY
  have hcz : G.Adj c z := (hselectedAdj z c hcZ).symm
  have haI : a ∈ I := (Finset.mem_filter.mp haX).1
  have hbI : b ∈ I := (Finset.mem_filter.mp hbX).1
  have hcI : c ∈ I := (Finset.mem_filter.mp hcY).1
  have specialIndependentNotRest : ∀ i ∈ special, i ∈ I → i ∉ rest := by
    intro i his hiI hrest
    obtain ⟨k, hk, hcase⟩ := (hrestMem i).mp hrest
    have hkI := hOSub hk
    rcases hcase with h | h | h
    · have hiC : i ∈ C := h.symm ▸ hleftC k hkI
      exact (Finset.disjoint_left.mp hdisj) hiC hiI
    · subst k
      exact (Finset.mem_sdiff.mp hk).2 his
    · have hiC : i ∈ C := h.symm ▸ hrightC k hkI
      exact (Finset.disjoint_left.mp hdisj) hiC hiI
  have specialCliqueNotRest : ∀ q ∈ ({x,y,z} : Finset V), q ∈ C → q ∉ rest := by
    intro q hq hqC hrest
    obtain ⟨k, hk, hcase⟩ := (hrestMem q).mp hrest
    have hkI := hOSub hk
    rcases hcase with h | h | h
    · have hleftMem : left k ∈ ({x,y,z} : Finset V) := h.symm ▸ hq
      exact (hOavoidSpecial k hk).1 hleftMem
    · subst k
      exact (Finset.disjoint_left.mp hdisj) hqC hkI
    · have hrightMem : right k ∈ ({x,y,z} : Finset V) := h.symm ▸ hq
      exact (hOavoidSpecial k hk).2 hrightMem
  have hprefixRestDisjoint : ∀ v ∈ ([a,x,b,y,c,z] : List V), v ∉ rest := by
    intro v hv hvr
    simp only [List.mem_cons, List.not_mem_nil] at hv
    simp only [or_false] at hv
    rcases hv with hva | hvx | hvb | hvy | hvc | hvz
    · subst v; exact specialIndependentNotRest a (by simp [special]) haI hvr
    · subst v; exact specialCliqueNotRest x (by simp) hxC hvr
    · subst v; exact specialIndependentNotRest b (by simp [special]) hbI hvr
    · subst v; exact specialCliqueNotRest y (by simp) hyC hvr
    · subst v; exact specialIndependentNotRest c (by simp [special]) hcI hvr
    · subst v; exact specialCliqueNotRest z (by simp) hzC hvr
  let usedClique : Finset V := {x,y,z} ∪ O.biUnion (fun k => {left k, right k})
  let tailFin : Finset V := C \ usedClique
  let tail : List V := tailFin.toList
  have htailNodup : tail.Nodup := by
    change tailFin.toList.Nodup
    exact tailFin.nodup_toList
  have htailC : ∀ v ∈ tail, v ∈ C := by
    intro v hv
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
  have hbaseTailDisjoint : ∀ v ∈ ([a,x,b,y,c,z] ++ rest), v ∉ tail := by
    intro v hv hvtail
    have hvC : v ∈ C := htailC v hvtail
    have hvNotUsed : v ∉ usedClique := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hvtail)).2
    have hvUsed : v ∈ usedClique := by
      rcases List.mem_append.mp hv with hvprefix | hvrest
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hvprefix
        rcases hvprefix with h | h | h | h | h | h
        · subst v; exact False.elim ((Finset.disjoint_left.mp hdisj) hvC haI)
        · subst v; exact Finset.mem_union.mpr (Or.inl (by simp))
        · subst v; exact False.elim ((Finset.disjoint_left.mp hdisj) hvC hbI)
        · subst v; exact Finset.mem_union.mpr (Or.inl (by simp))
        · subst v; exact False.elim ((Finset.disjoint_left.mp hdisj) hvC hcI)
        · subst v; exact Finset.mem_union.mpr (Or.inl (by simp))
      · obtain ⟨k, hk, hcase⟩ := (hrestMem v).mp hvrest
        rcases hcase with h | h | h
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨k, hk, by simp [h]⟩))
        · have hvI : v ∈ I := h.symm ▸ hOSub hk
          exact False.elim ((Finset.disjoint_left.mp hdisj) hvC hvI)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨k, hk, by simp [h]⟩))
    exact hvNotUsed hvUsed
  have hcover : ∀ v : V, v ∈ ([a,x,b,y,c,z] ++ rest) ∨ v ∈ tail := by
    intro v
    have hv : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
    rw [hpartition] at hv
    rcases Finset.mem_union.mp hv with hvC | hvI
    · by_cases hvUsed : v ∈ usedClique
      · rcases Finset.mem_union.mp hvUsed with hvSpecial | hvRestEnds
        · left
          have hv' : v = x ∨ v = y ∨ v = z := by simpa using hvSpecial
          apply List.mem_append_left
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rcases hv' with h | h | h <;> simp [h]
        · obtain ⟨k, hk, hvEnds⟩ := Finset.mem_biUnion.mp hvRestEnds
          have hvEnds' : v = left k ∨ v = right k := by
            simpa using hvEnds
          left
          apply List.mem_append_right
          have hcase : v = left k ∨ v = k ∨ v = right k := by
            rcases hvEnds' with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          exact (hrestMem v).2 ⟨k, hk, hcase⟩
      · right
        exact Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hvC, hvUsed⟩)
    · by_cases hvSpecial : v ∈ special
      · left
        apply List.mem_append_left
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        simp only [special, Finset.mem_insert, Finset.mem_singleton] at hvSpecial
        rcases hvSpecial with h | h | h <;> simp [h]
      · have hvO : v ∈ O := Finset.mem_sdiff.mpr ⟨hvI, hvSpecial⟩
        left
        apply List.mem_append_right
        exact (hrestMem v).2 ⟨v, hvO, Or.inr (Or.inl rfl)⟩
  exact hamiltonian_of_triangle_block_and_remaining_chain G C I hC hdisj
    a b c x y z haI hbI hcI hxC hyC hzC hab hac hbc hxy hxz hyz
    hax hxb hby hyc hcz rest tail hrestNodup hrestChain hrestHeadC hrestLastC
    hprefixRestDisjoint htailNodup htailC hbaseTailDisjoint hcover (by simp [tail])

end SplitGraphSmallRowsThree

#print axioms SplitGraphSmallRowsThree.three_pair_rows_are_triangle
#print axioms SplitGraphSmallRowsThree.hamiltonian_of_triangle_block_and_remaining_chain
#print axioms SplitGraphSmallRowsThree.chosen_three_double_rows_form_triangle
#print axioms SplitGraphSmallRowsThree.hamiltonian_of_split_partition_three_double_rows
