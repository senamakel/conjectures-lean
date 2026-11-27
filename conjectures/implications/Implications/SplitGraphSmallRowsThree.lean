import Implications.SplitGraphSmallRows
import Implications.SplitGraphSmallRowsPath

/-!
The triangle alternative for three selected degree-two clique rows.
-/

namespace SplitGraphSmallRowsThree

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem hamiltonian_of_list
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
    exact List.disjoint_left.mpr (by
      intro x hx hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hbaseTailDisjoint x (List.mem_append_left _ hx) hy
      · exact hbaseTailDisjoint x (List.mem_append_right _ hx) hy)
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

end SplitGraphSmallRowsThree
