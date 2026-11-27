import Implications.SplitGraphSmallRowsPath

namespace SplitGraphSmallRowsAssembly

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The local path block for two independent vertices that share one selected
clique neighbor. -/
theorem shared_clique_neighbor_block
    (G : SimpleGraph V) (C I : Finset V) (hdisj : Disjoint C I)
    (a c b i j : V) (ha : a ∈ C) (hc : c ∈ C) (hb : b ∈ C)
    (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    (hac : a ≠ c) (hcb : c ≠ b) (hab : a ≠ b)
    (hai : G.Adj a i) (hci : G.Adj c i)
    (hcj : G.Adj c j) (hbj : G.Adj b j) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.support = [a, i, c, j, b] := by
  have hia : G.Adj i c := hci.symm
  have hjc : G.Adj j c := hcj.symm
  have hne_ai : a ≠ i := by
    intro h
    subst i
    exact (Finset.disjoint_left.mp hdisj) ha hi
  have hne_ic : i ≠ c := by
    intro h
    subst c
    exact (Finset.disjoint_left.mp hdisj) hc hi
  have hne_cj : c ≠ j := by
    intro h
    subst j
    exact (Finset.disjoint_left.mp hdisj) hc hj
  have hne_jb : j ≠ b := by
    intro h
    subst j
    exact (Finset.disjoint_left.mp hdisj) hb hj
  have hnodup : ([a, i, c, j, b] : List V).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil]
    exact ⟨⟨hne_ai, by
      simp only [List.mem_cons, List.not_mem_nil]
      exact ⟨hne_ic.symm, by
        simp only [List.mem_cons, List.not_mem_nil]
        exact ⟨hne_cj, by
          simp only [List.mem_cons, List.not_mem_nil]
          exact ⟨hne_jb.symm, by
            simp only [List.mem_cons, List.not_mem_nil]
            exact ⟨hab, by simp⟩⟩⟩⟩⟩⟩
  have hchain : ([a, i, c, j, b] : List V).IsChain G.Adj := by
    simp [List.isChain_cons, hai, hia, hcj, hbj]
  let p := SimpleGraph.Walk.ofSupport ([a, i, c, j, b] : List V) (by simp) hchain
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport (by simp) hchain] using hnodup
  refine ⟨p, hp, ?_⟩
  exact SimpleGraph.Walk.support_ofSupport (by simp) hchain

/-- Append a clique list to any nodup chain whose final vertex is in the
clique. This is the reusable assembly step for clique-ended path blocks. -/
theorem hamiltonian_of_clique_ended_chain
    (G : SimpleGraph V) (C : Finset V) (hC : G.IsClique (C : Set V))
    (base tail : List V)
    (hbaseNodup : base.Nodup) (hbaseChain : base.IsChain G.Adj)
    (hbaseLastC : ∀ x, x ∈ base.getLast? → x ∈ C)
    (htailNodup : tail.Nodup) (htailC : ∀ x ∈ tail, x ∈ C)
    (hdisjoint : ∀ x ∈ base, x ∉ tail)
    (hcover : ∀ x : V, x ∈ base ∨ x ∈ tail)
    (hne : base ++ tail ≠ []) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  have hnodup : (base ++ tail).Nodup := by
    rw [List.nodup_append']
    exact ⟨hbaseNodup, htailNodup, hdisjoint⟩
  have htailChain : tail.IsChain G.Adj := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro x y l₁ l₂ heq
    have hx : x ∈ tail := by rw [heq]; simp
    have hy : y ∈ tail := by rw [heq]; simp
    have hxy : x ≠ y := by
      intro h
      subst y
      have hcount := (List.nodup_iff_count_le_one.mp htailNodup) x
      rw [heq] at hcount
      simp [List.count_append] at hcount
      omega
    exact hC (htailC x hx) (htailC y hy) hxy
  have hchain : (base ++ tail).IsChain G.Adj := by
    rw [List.isChain_append]
    refine ⟨hbaseChain, htailChain, ?_⟩
    intro x hx y hy
    have hxC := hbaseLastC x hx
    exact hC hxC (htailC y (List.mem_of_mem_head? hy)) (by
      intro h
      subst y
      exact hdisjoint x (List.mem_of_mem_getLast? hx) (List.mem_of_mem_head? hy))
  have hcover' : ∀ x : V, x ∈ base ++ tail := by
    intro x
    rcases hcover x with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ hx
  let p := SimpleGraph.Walk.ofSupport (base ++ tail) hne hchain
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport hne hchain] using hnodup
  have hvertices : ∀ x : V, x ∈ p.support := by
    intro x
    rw [SimpleGraph.Walk.support_ofSupport hne hchain]
    exact hcover' x
  exact ⟨_, _, p, hp.isHamiltonian_of_mem hvertices⟩

end SplitGraphSmallRowsAssembly
