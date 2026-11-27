import Implications.SplitGraphSmallRowsPath

namespace SplitGraphSmallRowsAssembly

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

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
