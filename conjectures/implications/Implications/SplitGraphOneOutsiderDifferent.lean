import Implications.SplitGraphTrees

/-!
Hamiltonian paths for the different-pair incidence pattern with one outsider.
-/

namespace SplitGraphOneOutsiderDifferent

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem nodup_of_all_distinct (l : List V)
    (h : ∀ p ∈ l, ∀ q ∈ l, p ≠ q) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.nodup_cons]
    refine ⟨?_, ih ?_⟩
    · intro ha
      exact h a (by simp) a ha rfl
    · intro p hp q hq
      exact h p (by simp [hp]) q (by simp [hq])

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

/-- The different-pair incidence pattern has a core path ending at any
chosen independent label. These four explicit paths are the only path cases
needed when extending through additional clique vertices. -/
theorem core_path_ending_at_each_independent
    (G : SimpleGraph V) (I : Finset V) (a b c z t x y i : V)
    (hI : I = {a, b, c, z})
    (hvertices : ∀ p ∈ ([a, b, c, z, t, x, y] : List V),
      ∀ q ∈ ([a, b, c, z, t, x, y] : List V), p ≠ q)
    (hC : G.IsClique ({t, x, y} : Set V))
    (htrow : row G I t = {a, b, c})
    (hxrow : row G I x = {a, b, z})
    (hyrow : row G I y = {a, c, z})
    (hi : i ∈ ({a, b, c, z} : Finset V)) :
    ∃ core : List V, core.Nodup ∧ core.IsChain G.Adj ∧
      core.getLast? = some i ∧ (∀ q ∈ I, q ∈ core) ∧
      t ∈ core ∧ x ∈ core ∧ y ∈ core := by
  classical
  have hit : i = a ∨ i = b ∨ i = c ∨ i = z := by
    simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc] using hi
  have hbt : G.Adj b t := (Finset.mem_filter.mp (by rw [htrow]; simp)).2
  have hat : G.Adj a t := (Finset.mem_filter.mp (by rw [htrow]; simp)).2
  have hct : G.Adj c t := (Finset.mem_filter.mp (by rw [htrow]; simp)).2
  have hxa : G.Adj x a := (Finset.mem_filter.mp (by rw [hxrow]; simp)).2
  have hxb : G.Adj x b := (Finset.mem_filter.mp (by rw [hxrow]; simp)).2
  have hxz : G.Adj x z := (Finset.mem_filter.mp (by rw [hxrow]; simp)).2
  have hya : G.Adj y a := (Finset.mem_filter.mp (by rw [hyrow]; simp)).2
  have hyc : G.Adj y c := (Finset.mem_filter.mp (by rw [hyrow]; simp)).2
  have hyz : G.Adj y z := (Finset.mem_filter.mp (by rw [hyrow]; simp)).2
  have htx : G.Adj t x := hC (by simp) (by simp) (by
    intro h; exact hvertices t (by simp) x (by simp) h)
  have hty : G.Adj t y := hC (by simp) (by simp) (by
    intro h; exact hvertices t (by simp) y (by simp) h)
  have hxy : G.Adj x y := hC (by simp) (by simp) (by
    intro h; exact hvertices x (by simp) y (by simp) h)
  have hdistinct (l : List V) (hl : ∀ q ∈ l, q ∈ ([a,b,c,z,t,x,y] : List V)) :
      ∀ p ∈ l, ∀ q ∈ l, p ≠ q := by
    intro p hp q hq
    exact hvertices p (hl p hp) q (hl q hq)
  have hcoverA (l : List V) (hl : ∀ q ∈ l, q ∈ ({a,b,c,z,t,x,y} : Finset V)) :
      ∀ q ∈ I, q ∈ l := by
    intro q hq
    have hq' : q = a ∨ q = b ∨ q = c ∨ q = z := by
      simpa [hI, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc] using hq
    rcases hq' with rfl | rfl | rfl | rfl
    · exact hl a (by simp)
    · exact hl b (by simp)
    · exact hl c (by simp)
    · exact hl z (by simp)
  rcases hit with rfl | rfl | rfl | rfl
  · refine ⟨[b, x, z, y, c, t, a], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply nodup_of_all_distinct
      exact hdistinct _ (by simp)
    · simp [List.isChain_cons, hxb, hxz, hyz.symm, hyc, hct.symm, hat.symm,
        hvertices t (by simp) x (by simp)]
    · simp
    · exact hcoverA _ (by intro q hq; simp at hq ⊢ <;> tauto)
    · simp
    · simp
    · simp
  · refine ⟨[a, t, c, y, z, x, b], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply nodup_of_all_distinct
      exact hdistinct _ (by simp)
    · simp [List.isChain_cons, hat, hct, hyc.symm, hyz, hxz.symm, hxb]
    · simp
    · exact hcoverA _ (by intro q hq; simp at hq ⊢ <;> tauto)
    · simp
    · simp
    · simp
  · refine ⟨[b, t, a, x, z, y, c], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply nodup_of_all_distinct
      exact hdistinct _ (by simp)
    · simp [List.isChain_cons, hbt, hat, hxa.symm, hxz, hyz.symm, hyc]
    · simp
    · exact hcoverA _ (by intro q hq; simp at hq ⊢ <;> tauto)
    · simp
    · simp
    · simp
  · refine ⟨[b, x, a, t, c, y, z], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply nodup_of_all_distinct
      exact hdistinct _ (by simp)
    · simp [List.isChain_cons, hxb, hxa.symm, hat, hct, hyc.symm, hyz]
    · simp
    · exact hcoverA _ (by intro q hq; simp at hq ⊢ <;> tauto)
    · simp
    · simp
    · simp

end SplitGraphOneOutsiderDifferent
