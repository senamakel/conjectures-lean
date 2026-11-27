import Implications.SplitGraphTrees

/-!
Path constructions for the connectivity-two split-graph case with one outsider.
-/

namespace SplitGraphOneOutsider
open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sublist_append_self (l r : List V) : l.Sublist (l ++ r) := by
  induction l with
  | nil =>
    induction r with
    | nil => exact List.Sublist.refl []
    | cons a r ih => exact List.Sublist.cons a ih
  | cons a l ih => exact List.Sublist.cons_cons a ih

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
    (hu : u ∈ C) (hy : y ∈ C)
    (hspareC : ∀ v ∈ spare, v ∈ C)
    (hcoverC : ∀ v ∈ C, v = x ∨ v = t ∨ v ∈ ([u] ++ spare ++ [y]))
    (hzx : G.Adj z x) (hxa : G.Adj x a) (hat : G.Adj a t)
    (htc : G.Adj t c) (hcu : G.Adj c u) (hby : G.Adj y b) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  let core : List V := [z, x, a, t, c]
  let segment : List V := [u] ++ spare ++ [y]
  let tail : List V := segment ++ [b]
  let path := core ++ tail
  have hsegmentSubPath : segment.Sublist path := by
    have hsegTail : segment.Sublist tail := by
      exact sublist_append_self segment [b]
    dsimp [path, core]
    exact List.Sublist.cons z (List.Sublist.cons x (List.Sublist.cons a
      (List.Sublist.cons t (List.Sublist.cons c hsegTail))))
  have hsegmentNodup : segment.Nodup := hsegmentSubPath.nodup (by
    simpa [path, core, tail, segment, List.append_assoc] using hpathNodup)
  have hcoreChain : core.IsChain G.Adj := by
    simp [core, List.isChain_cons, hzx, hxa, hat, htc]
  have hsegmentC : ∀ v ∈ segment, v ∈ C := by
    intro v hv
    simp only [segment, List.mem_append, List.mem_cons, List.not_mem_nil,
      List.mem_singleton, or_false] at hv
    rcases hv with hv | hv
    · rcases hv with hvu | hvspare
      · exact hvu ▸ hu
      · exact hspareC v hvspare
    · exact hv ▸ hy
  have hsegmentChain : segment.IsChain G.Adj :=
    clique_list_chain G C hC segment hsegmentNodup hsegmentC
  have hsegmentHead : segment.head? = some u := by simp [segment]
  have hsegmentLast : segment.getLast? = some y := by
    unfold segment
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  have htailChain : tail.IsChain G.Adj := by
    refine List.IsChain.append hsegmentChain (by simp) ?_
    intro v hv w hw
    rw [hsegmentLast] at hv
    have hv' : v = y := by simpa using hv.symm
    have hw' : w = b := by simpa using hw.symm
    rw [hv', hw']
    exact hby
  have hchain : path.IsChain G.Adj := by
    refine List.IsChain.append ?_ htailChain ?_
    · simpa [core] using hcoreChain
    · intro v hv w hw
      have hcoreLast : core.getLast? = some c := by simp [core]
      rw [hcoreLast] at hv
      have hv' : v = c := by simpa using hv.symm
      have htailHead : tail.head? = some u := by
        change (segment ++ [b]).head? = some u
        rw [List.head?_append_of_ne_nil segment (by simp [segment]), hsegmentHead]
      rw [htailHead] at hw
      have hw' : w = u := by simpa using hw.symm
      rw [hv', hw']
      exact hcu
  have hcover : ∀ v : V, v ∈ path := by
    intro v
    have hv : v ∈ C ∨ v ∈ I := by
      have hmem : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [hpartition] at hmem
      exact Finset.mem_union.mp hmem
    rcases hv with hvC | hvI
    · rcases hcoverC v hvC with rfl | rfl | htail
      · exact List.mem_append_left _ (by simp [core])
      · exact List.mem_append_left _ (by simp [core])
      · exact List.mem_append_right _ (List.mem_append_left _ htail)
    · have hvI' : v = a ∨ v = b ∨ v = c ∨ v = z := by
        simpa [hI, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc] using hvI
      rcases hvI' with rfl | rfl | rfl | rfl
      · exact List.mem_append_left _ (by simp [core])
      · exact List.mem_append_right _ (by simp [tail])
      · exact List.mem_append_left _ (by simp [core])
      · exact List.mem_append_left _ (by simp [core])
  exact hamiltonian_of_list G path (by simp [path, core, tail, segment])
    (by simpa [path, core, tail, segment] using hpathNodup) hchain hcover

/-- With one outsider, two clique rows containing that outsider and the same
pair from the central triple give a Hamiltonian path. The omitted independent
vertex has a second attachment, which enters the remaining clique segment. -/
theorem hamiltonian_of_one_outsider_shared_pair_rows
    (G : SimpleGraph V) (C I : Finset V) (a b c z t x y : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hI : I = {a, b, c, z})
    (hab : a ≠ b) (hac : a ≠ c) (haz : a ≠ z) (hbc : b ≠ c) (hbz : b ≠ z) (hcz : c ≠ z)
    (ht : t ∈ C) (hx : x ∈ C) (hy : y ∈ C)
    (htx : t ≠ x) (hty : t ≠ y) (hxy : x ≠ y)
    (htrow : row G I t = {a, b, c})
    (hxrow : row G I x = {a, b, z}) (hyrow : row G I y = {a, b, z})
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  have haI : a ∈ I := by simp [hI]
  have hbI : b ∈ I := by simp [hI]
  have hcI : c ∈ I := by simp [hI]
  have hzI : z ∈ I := by simp [hI]
  have hCI {q i : V} (hq : q ∈ C) (hi : i ∈ I) : q ≠ i := by
    intro h
    subst i
    exact (Finset.disjoint_left.mp hdisj) hq hi
  have hadj {q i : V} (hi : i ∈ row G I q) : G.Adj q i :=
    (Finset.mem_filter.mp hi).2
  have hzx : G.Adj z x := (hadj (show z ∈ row G I x by simp [hxrow])).symm
  have hxa : G.Adj x a := hadj (by simp [hxrow])
  have hat : G.Adj a t := (hadj (show a ∈ row G I t by simp [htrow])).symm
  have htc : G.Adj t c := hadj (by simp [htrow])
  have hyb : G.Adj y b := hadj (by simp [hyrow])
  have hxnc : ¬ G.Adj x c := by
    intro h
    have hc : c ∈ row G I x := Finset.mem_filter.mpr ⟨hcI, h⟩
    simpa [hxrow, hac.symm, hbc.symm, hcz] using hc
  have hync : ¬ G.Adj y c := by
    intro h
    have hc : c ∈ row G I y := Finset.mem_filter.mpr ⟨hcI, h⟩
    simpa [hyrow, hac.symm, hbc.symm, hcz] using hc
  have hextra : ∃ u ∈ C, u ≠ t ∧ G.Adj u c := by
    obtain ⟨q, hq, d, hd, hqd, hqc, hdc⟩ := hdeg c hcI
    by_cases hqt : q = t
    · exact ⟨d, hd, fun hdt => hqd (hqt.trans hdt.symm), hdc⟩
    · exact ⟨q, hq, hqt, hqc⟩
  obtain ⟨u, hu, hut, huc⟩ := hextra
  have hux : u ≠ x := fun h => hxnc (h ▸ huc)
  have huy : u ≠ y := fun h => hync (h ▸ huc)
  let S := (((C.erase t).erase x).erase y).erase u
  let spare := S.toList
  let fixed : List V := [z, x, a, t, c, u, y, b]
  have hfixed : fixed.Nodup := by
    simp [fixed, List.nodup_cons, haz.symm, hbz.symm, hcz.symm,
      hab, hac, hbc.symm, htx.symm, hty, hxy, hut.symm, hux.symm, huy,
      (hCI hx hzI).symm, (hCI ht hzI).symm,
      (hCI hu hzI).symm, (hCI hy hzI).symm, hCI hx haI, hCI hx hcI, hCI hx hbI,
      (hCI ht haI).symm, (hCI hu haI).symm, (hCI hy haI).symm,
      hCI ht hcI, hCI ht hbI, (hCI hu hcI).symm, (hCI hy hcI).symm,
      hCI hu hbI, hCI hy hbI]
  have hspareC : ∀ v ∈ spare, v ∈ C := by
    intro v hv
    have hv' : v ∈ S := Finset.mem_toList.mp hv
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hv').2).2).2).2
  have hcombined : (fixed ++ spare).Nodup := by
    rw [List.nodup_append']
    refine ⟨hfixed, S.nodup_toList, ?_⟩
    intro v hv hvs
    have hvS : v ∈ S := Finset.mem_toList.mp hvs
    have hvC := hspareC v hvs
    simp only [fixed, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (Finset.disjoint_left.mp hdisj) hvC hzI
    · simpa [S] using hvS
    · exact (Finset.disjoint_left.mp hdisj) hvC haI
    · simpa [S] using hvS
    · exact (Finset.disjoint_left.mp hdisj) hvC hcI
    · simpa [S] using hvS
    · simpa [S] using hvS
    · exact (Finset.disjoint_left.mp hdisj) hvC hbI
  have hperm : (fixed ++ spare).Perm ([z,x,a,t,c,u] ++ spare ++ [y,b]) := by
    simpa [fixed, List.append_assoc] using
      (List.Perm.append_left [z,x,a,t,c,u] (List.perm_append_comm : ([y,b] ++ spare).Perm (spare ++ [y,b])))
  have hcover : ∀ v ∈ C, v = x ∨ v = t ∨ v ∈ ([u] ++ spare ++ [y]) := by
    intro v hv
    by_cases hvx : v = x
    · exact Or.inl hvx
    by_cases hvt : v = t
    · exact Or.inr (Or.inl hvt)
    right
    right
    by_cases hvu : v = u
    · simp [hvu]
    by_cases hvy : v = y
    · simp [hvy]
    have hvS : v ∈ S := by simp [S, hv, hvx, hvt, hvu, hvy]
    have hvsp : v ∈ spare := Finset.mem_toList.mpr hvS
    simp [hvsp]
  exact hamiltonian_of_one_outsider_shared_pair_path G C I a b c z t x y u spare
    hC hpartition hI (hperm.nodup hcombined) hu hy hspareC hcover hzx hxa hat htc huc.symm hyb

#print axioms hamiltonian_of_one_outsider_shared_pair_rows

end SplitGraphOneOutsider

#print axioms SplitGraphOneOutsider.hamiltonian_of_one_outsider_shared_pair_path
