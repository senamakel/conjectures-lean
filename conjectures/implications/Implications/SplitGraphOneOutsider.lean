import Implications.SplitGraphPath

/-!
Path constructions for the connectivity-two split-graph case with one outsider.
-/

namespace SplitGraphOneOutsider

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

/-- The shared-pair branch with one outsider has the explicit spanning path
`[z, x, a, t, c, u] ++ spare ++ [y, b]`. The first five vertices are the
independent/clique incidence core; `u :: spare ++ [y, b]` is the remaining
clique segment. -/
theorem hamiltonian_of_one_outsider_shared_pair_path
    (G : SimpleGraph V) (C I : Finset V)
    (a b c z t x y u : V) (spare : List V)
    (hC : G.IsClique (C : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hI : I = {a, b, c, z})
    (hpathNodup : (([z, x, a, t, c, u] ++ spare ++ [y, b]) : List V).Nodup)
    (hspareC : ∀ v ∈ spare, v ∈ C)
    (hcoverC : ∀ v ∈ C, v ∈ ([u] ++ spare ++ [y]))
    (hzx : G.Adj z x) (hxa : G.Adj x a) (hat : G.Adj a t)
    (htc : G.Adj t c) (hcu : G.Adj c u) (hby : G.Adj y b) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  let core : List V := [z, x, a, t, c]
  let segment : List V := [u] ++ spare ++ [y]
  let tail : List V := segment ++ [b]
  let path := core ++ tail
  have hcoreChain : core.IsChain G.Adj := by
    simp [core, List.isChain_cons, hzx, hxa, hat, htc]
  have hsegmentC : ∀ v ∈ segment, v ∈ C := by
    intro v hv
    simp only [segment, List.mem_append, List.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact hu
    · rcases List.mem_append.mp hv with hv | hv
      · exact hspareC v hv
      · simp only [List.mem_singleton] at hv
        exact hv ▸ hy
  have hsegmentNodup : segment.Nodup := by
    have h := hpathNodup
    simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil] at h
    exact h.2.1.2.1
  have hsegmentChain : segment.IsChain G.Adj :=
    clique_list_chain G C hC segment hsegmentNodup hsegmentC
  have htailChain : tail.IsChain G.Adj := by
    rw [List.isChain_append]
    refine ⟨hsegmentChain, by simp, ?_⟩
    intro v hv w hw
    simp only [segment, List.mem_append, List.mem_singleton] at hv
    simp only [List.mem_singleton] at hw
    rcases List.mem_append.mp hv with hv | hv
    · simp at hv
      subst v
      exact hby
    · simp only [List.mem_singleton] at hv
      subst v
      exact hby
  have hchain : path.IsChain G.Adj := by
    rw [List.isChain_append]
    refine ⟨?_, htailChain, ?_⟩
    · simpa [core] using hcoreChain
    · intro v hv w hw
      simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hv
      simp only [tail, List.mem_append, List.mem_singleton] at hw
      rcases hv with hvz | hvx | hva | hvt | hvc
      · simp at hvz
      · simp at hvx
      · simp at hva
      · simp at hvt
      · subst v
        rcases hw with hwu | hw
        · subst w
          exact hcu
        · rcases List.mem_append.mp hw with hw | hw
          · simp at hw
          · simp at hw
            exact hcu
  have hcover : ∀ v : V, v ∈ path := by
    intro v
    have hv : v ∈ C ∨ v ∈ I := by
      have hmem : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [hpartition] at hmem
      exact Finset.mem_union.mp hmem
    rcases hv with hvC | hvI
    · exact List.mem_append_right _ (hcoverC v hvC)
    · have hvI' : v = a ∨ v = b ∨ v = c ∨ v = z := by
        simpa [hI, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc] using hvI
      rcases hvI' with rfl | rfl | rfl | rfl
      · exact List.mem_append_left _ (by simp [core])
      · exact List.mem_append_right _ (by simp [tail])
      · exact List.mem_append_left _ (by simp [core])
      · exact List.mem_append_left _ (by simp [core])
  exact hamiltonian_of_list G path (by simp [path, core, tail, segment]) hpathNodup hchain hcover

end SplitGraphOneOutsider
