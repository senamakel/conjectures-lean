import Implications.SplitGraphTrees

/-!
Hamiltonian paths for the different-pair incidence pattern with one outsider.
-/

namespace SplitGraphOneOutsiderDifferent

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem clique_list_chain (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique (C : Set V)) (l : List V) (hnodup : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ C) : l.IsChain G.Adj := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y l₁ l₂ heq
  have hx : x ∈ l := by rw [heq]; simp
  have hy : y ∈ l := by rw [heq]; simp
  have hxy : x ≠ y := by
    intro h
    subst y
    have hcount := (List.nodup_iff_count_le_one.mp hnodup) x
    rw [heq] at hcount
    simp [List.count_append, List.count_cons] at hcount
    omega
  exact hC (hsub x hx) (hsub y hy) hxy

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

/-- A core path ending at an independent vertex extends through one extra
clique vertex and then through the unused clique vertices. -/
private theorem hamiltonian_of_core_with_clique_tail
    (G : SimpleGraph V) (C I : Finset V) (core spare : List V)
    (i u : V)
    (hC : G.IsClique (C : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hpathNodup : (core ++ [u] ++ spare).Nodup)
    (htailNodup : ([u] ++ spare).Nodup)
    (hcoreChain : core.IsChain G.Adj) (hcoreLast : core.getLast? = some i)
    (hiI : i ∈ I) (hcoreI : ∀ v ∈ I, v ∈ core)
    (hu : u ∈ C) (hattach : G.Adj i u)
    (hspareNodup : spare.Nodup) (hspareC : ∀ v ∈ spare, v ∈ C)
    (hcoverC : ∀ v ∈ C, v ∈ core ∨ v = u ∨ v ∈ spare) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  let tail := [u] ++ spare
  let path := core ++ tail
  have htailC : ∀ v ∈ tail, v ∈ C := by
    intro v hv
    simp only [tail, List.mem_append, List.mem_singleton] at hv
    rcases hv with h | h
    · exact h ▸ hu
    · exact hspareC v h
  have htailChain : tail.IsChain G.Adj := clique_list_chain G C hC tail
    (by simpa [tail] using htailNodup) htailC
  have hchain : path.IsChain G.Adj := by
    refine List.IsChain.append hcoreChain htailChain ?_
    intro v hv w hw
    rw [hcoreLast] at hv
    have hv' : v = i := by simpa using hv.symm
    have htailHead : tail.head? = some u := by simp [tail]
    rw [htailHead] at hw
    have hw' : w = u := by simpa using hw.symm
    rw [hv', hw']
    exact hattach
  have hcover : ∀ v : V, v ∈ path := by
    intro v
    have hv : v ∈ C ∨ v ∈ I := by
      have hv' : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [hpartition] at hv'
      exact Finset.mem_union.mp hv'
    rcases hv with hvC | hvI
    · rcases hcoverC v hvC with hcore | hu' | hspare
      · exact List.mem_append_left _ hcore
      · exact List.mem_append_right _ (by simp [tail, hu'])
      · exact List.mem_append_right _ (by simp [tail, hspare])
    · exact List.mem_append_left _ (hcoreI v hvI)
  exact hamiltonian_of_list G path (by simp [path, tail])
    (by simpa [path, tail] using hpathNodup) hchain hcover

end SplitGraphOneOutsiderDifferent
