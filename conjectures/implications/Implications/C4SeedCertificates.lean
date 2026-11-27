import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Maps
import Implications.C4Extremal42SearchConstraints

/-!
# Finite certificates for the three published 41-vertex `C₄` extremal seeds

The three records in the [McKay sparse6 data file](https://users.cecs.anu.edu.au/~bdm/data/extremal/c4_n41e132.maybe.s6)
are represented here by their 41 neighbourhood bitmasks.  Their SHA-256 digests, in order, are
`4033a0cc2e1e8f6d7cb05009d2ed0b0cfcec9ce969d76c6ed2faec68b3405927`,
`7b21f509d31f8002aba9c00d5a21a1db422177bd6a832cee6b4e80dad460db60`, and
`8282afa2558555cbdad70ff78767b188cd328b83626e8b59c0f11ad31e000042`.
Each record decodes to 41 vertices and 132 edges. For vertices `u` and `v`, having no common
neighbour is the bitwise condition `land (N u) (N v) = 0`.

`compatibleCliqueSearchBool` is a depth-pruned search.  It either skips the next
candidate, or takes it and restricts later candidates to vertices compatible
with it. `search_correct` proves equivalence with the proposition that an
actual pairwise-compatible list of the requested size is a sublist of the
candidates. The three closed Boolean results below are checked by
`decide +kernel`, and `checker_false` converts each Boolean result to that
proposition. All three certificates depend only on the standard Lean axioms.

This certifies only that the three supplied seeds have no compatible
six-element set.  It makes no claim that the list of seeds is exhaustive.
-/

namespace C4SeedCertificates

private def compatible (g : Array Nat) (u v : Nat) : Bool :=
  Nat.land (g[u]!) (g[v]!) == 0

/-- The skip-or-take search, with the candidate list filtered after each take. -/
def compatibleCliqueSearchBool (g : Array Nat) : List Nat → Nat → Bool
  | _, 0 => true
  | [], _ + 1 => false
  | v :: vs, k + 1 =>
      compatibleCliqueSearchBool g vs (k + 1) ||
        compatibleCliqueSearchBool g (vs.filter (compatible g v)) k
termination_by candidates _ => candidates.length
decreasing_by
  · simp_wf
  · simp_wf
    have hfilter : (vs.filter (compatible g v)).length ≤ vs.length :=
      List.length_filter_le _ _
    omega

/--
There is a pairwise-compatible list of the requested size that is an ordered
sublist of the candidates.  This is the mathematical specification of the
search result.
-/
def ExistsCompatibleClique (g : Array Nat) (candidates : List Nat) (size : Nat) : Prop :=
  ∃ chosen : List Nat, chosen.length = size ∧ List.Sublist chosen candidates ∧
    chosen.Pairwise (fun u v => compatible g u v = true)

/-- A true checker result produces an actual compatible sublist witness. -/
theorem search_sound (g : Array Nat) : (candidates : List Nat) → (size : Nat) →
    compatibleCliqueSearchBool g candidates size = true →
      ExistsCompatibleClique g candidates size
  | _, 0, _ => ⟨[], by simp, List.nil_sublist _, List.Pairwise.nil⟩
  | [], Nat.succ _, h => by simp [compatibleCliqueSearchBool] at h
  | v :: vs, Nat.succ size, h => by
      have hsplit :
          compatibleCliqueSearchBool g vs (Nat.succ size) = true ∨
            compatibleCliqueSearchBool g (vs.filter (compatible g v)) size = true := by
        simpa only [compatibleCliqueSearchBool, Bool.or_eq_true] using h
      rcases hsplit with hskip | htake
      · obtain ⟨chosen, hlen, hsub, hpairs⟩ := search_sound g vs (Nat.succ size) hskip
        exact ⟨chosen, hlen, hsub.cons v, hpairs⟩
      · obtain ⟨chosen, hlen, hsub, hpairs⟩ :=
          search_sound g (vs.filter (compatible g v)) size htake
        refine ⟨v :: chosen, by simp [hlen], ?_, ?_⟩
        · exact List.Sublist.cons_cons v (hsub.trans List.filter_sublist)
        · apply List.Pairwise.cons
          · intro w hw
            exact (List.mem_filter.mp (hsub.subset hw)).2
          · exact hpairs
termination_by candidates => candidates.length
decreasing_by
  · simp_wf
  · simp_wf
    have hfilter : (vs.filter (compatible g v)).length ≤ vs.length :=
      List.length_filter_le _ _
    omega

/-- A genuine compatible sublist is found by the depth-pruned checker. -/
theorem search_complete (g : Array Nat) : (candidates : List Nat) → (size : Nat) →
    ExistsCompatibleClique g candidates size →
      compatibleCliqueSearchBool g candidates size = true
  | _, 0, _ => by simp [compatibleCliqueSearchBool]
  | [], Nat.succ _, h => by
      obtain ⟨chosen, hlen, hsub, _⟩ := h
      have hlenBound : chosen.length ≤ 0 := by simpa using hsub.length_le
      omega
  | v :: vs, Nat.succ size, h => by
      obtain ⟨chosen, hlen, hsub, hpairs⟩ := h
      cases chosen with
      | nil => simp at hlen
      | cons a tail =>
          rcases List.cons_sublist_cons'.mp hsub with hskip | ⟨hav, htail⟩
          · have hskipSpec : ExistsCompatibleClique g vs (Nat.succ size) :=
                ⟨a :: tail, hlen, hskip, hpairs⟩
            simp only [compatibleCliqueSearchBool, Bool.or_eq_true]
            exact Or.inl (search_complete g vs (Nat.succ size) hskipSpec)
          · subst a
            have hlenTail : tail.length = size := by simpa using hlen
            have hpairsTail : tail.Pairwise (fun u w => compatible g u w = true) :=
              hpairs.of_cons
            have hcompatible : ∀ w ∈ tail, compatible g v w = true := by
              intro w hw
              exact List.rel_of_pairwise_cons hpairs hw
            have htailFiltered :
                List.Sublist tail (vs.filter (compatible g v)) := by
              rw [← List.filter_eq_self.mpr hcompatible]
              exact htail.filter (compatible g v)
            have htakeSpec : ExistsCompatibleClique g (vs.filter (compatible g v)) size :=
              ⟨tail, hlenTail, htailFiltered, hpairsTail⟩
            simp only [compatibleCliqueSearchBool, Bool.or_eq_true]
            exact Or.inr (search_complete g (vs.filter (compatible g v)) size htakeSpec)
termination_by candidates => candidates.length
decreasing_by
  · simp_wf
  · simp_wf
    have hfilter : (vs.filter (compatible g v)).length ≤ vs.length :=
      List.length_filter_le _ _
    omega

/-- The Boolean search is sound and complete for the stated clique property. -/
theorem search_correct (g : Array Nat) (candidates : List Nat) (size : Nat) :
    compatibleCliqueSearchBool g candidates size = true ↔
      ExistsCompatibleClique g candidates size :=
  ⟨search_sound g candidates size, search_complete g candidates size⟩

/-- The executable Boolean certificate for a graph's candidate set and clique size. -/
def checker (g : Array Nat) (vertices size : Nat) : Bool :=
  compatibleCliqueSearchBool g (List.range vertices) size

/-- A false Boolean certificate proves that no compatible clique of this size exists. -/
theorem checker_false {g : Array Nat} {vertices size : Nat}
    (h : checker g vertices size = false) :
    ¬ ExistsCompatibleClique g (List.range vertices) size := by
  intro hc
  have htrue : checker g vertices size = true :=
    (search_correct g (List.range vertices) size).2 hc
  rw [h] at htrue
  contradiction

private def seed1 : Array Nat := #[21541946382, 4325701, 2181050499, 274888393777, 805310568, 1236950712984, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 537468948, 1168233469956, 1099679499328, 4296294592, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 8642363656, 377880576, 137598353412, 1116978282497, 292632412672, 553060925520, 13023318032, 139859069952, 319169757316, 696321867777, 1140859076864, 103280542209, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952, 8657068064]

private def seed2 : Array Nat := #[21541946382, 4325701, 2181050499, 274888393777, 805310568, 137439085208, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 1100049096724, 68721842180, 167871552, 1103807922368, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 1108153991432, 377880576, 137598353412, 17466654721, 292632412672, 553060925520, 13023318032, 1239370697728, 319169757316, 696321867777, 41347449088, 1202792169985, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952, 18262036480]

private def seed3 : Array Nat := #[21541946382, 4325701, 2181050499, 274888393777, 1100316938344, 137439085208, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1100585641728, 537468948, 68721842180, 167871552, 4296294592, 584116229120, 34381037602, 279189825536, 412385087744, 1099585585280, 618488930312, 1748107266, 8642363656, 377880576, 1237109981188, 17466654721, 292632412672, 553060925520, 13023318032, 139859069952, 319169757316, 696321867777, 41347449088, 103280542209, 1196148588544, 188980666432, 74122264608, 2282487816, 4565565952, 34394343440]

theorem seed1_no_compatible_six :
    ¬ ExistsCompatibleClique seed1 (List.range 41) 6 := by
  apply checker_false
  decide +kernel

theorem seed2_no_compatible_six :
    ¬ ExistsCompatibleClique seed2 (List.range 41) 6 := by
  apply checker_false
  decide +kernel

theorem seed3_no_compatible_six :
    ¬ ExistsCompatibleClique seed3 (List.range 41) 6 := by
  apply checker_false
  decide +kernel

/-! ## Connecting the masks to simple graphs

The row at index `u` is the open neighborhood of `u`: bit `v` records the
edge `u--v`.  The three concrete arrays are symmetric and loopless, so they
define actual simple graphs.  Their kernel-checked mask certificates then
rule out six pairwise disjoint open neighborhoods in any graph isomorphic to
one of them.
-/

private def maskGraph (g : Array Nat)
    (hsym : ∀ u v : Fin 41,
      Nat.testBit g[u.val]! v.val = Nat.testBit g[v.val]! u.val)
    (hloop : ∀ u : Fin 41, Nat.testBit g[u.val]! u.val = false) :
    SimpleGraph (Fin 41) :=
  { Adj := fun u v => Nat.testBit g[u.val]! v.val = true
    symm := ⟨fun {u v} huv => by simpa [hsym u v] using huv⟩
    loopless := ⟨fun {u} hu => by simpa [hloop u] using hu⟩ }

private theorem seed1_graph_symm : ∀ u v : Fin 41,
    Nat.testBit seed1[u.val]! v.val = Nat.testBit seed1[v.val]! u.val := by
  decide +kernel +revert

private theorem seed2_graph_symm : ∀ u v : Fin 41,
    Nat.testBit seed2[u.val]! v.val = Nat.testBit seed2[v.val]! u.val := by
  decide +kernel +revert

private theorem seed3_graph_symm : ∀ u v : Fin 41,
    Nat.testBit seed3[u.val]! v.val = Nat.testBit seed3[v.val]! u.val := by
  decide +kernel +revert

private theorem seed1_graph_loop : ∀ u : Fin 41,
    Nat.testBit seed1[u.val]! u.val = false := by decide +kernel

private theorem seed2_graph_loop : ∀ u : Fin 41,
    Nat.testBit seed2[u.val]! u.val = false := by decide +kernel

private theorem seed3_graph_loop : ∀ u : Fin 41,
    Nat.testBit seed3[u.val]! u.val = false := by decide +kernel

/-- The three McKay mask records, interpreted as simple graphs on 41 vertices. -/
def seed1Graph : SimpleGraph (Fin 41) := maskGraph seed1 seed1_graph_symm seed1_graph_loop
def seed2Graph : SimpleGraph (Fin 41) := maskGraph seed2 seed2_graph_symm seed2_graph_loop
def seed3Graph : SimpleGraph (Fin 41) := maskGraph seed3 seed3_graph_symm seed3_graph_loop

private def maskNeighbors (g : Array Nat) (u : Fin 41) : Finset (Fin 41) :=
  Finset.univ.filter (fun v => Nat.testBit g[u.val]! v.val)

private theorem seed1_neighbor_disjoint_iff : ∀ u v : Fin 41,
    Disjoint (maskNeighbors seed1 u) (maskNeighbors seed1 v) ↔
      compatible seed1 u.val v.val = true := by
  intro u v
  decide +kernel +revert

private theorem seed2_neighbor_disjoint_iff : ∀ u v : Fin 41,
    Disjoint (maskNeighbors seed2 u) (maskNeighbors seed2 v) ↔
      compatible seed2 u.val v.val = true := by
  intro u v
  decide +kernel +revert

private theorem seed3_neighbor_disjoint_iff : ∀ u v : Fin 41,
    Disjoint (maskNeighbors seed3 u) (maskNeighbors seed3 v) ↔
      compatible seed3 u.val v.val = true := by
  intro u v
  decide +kernel +revert

private theorem compatible_of_nodup_pairwise {g : Array Nat} (l : List (Fin 41))
    (hnd : l.Nodup)
    (hp : l.Pairwise (fun u v => compatible g u.val v.val = true)) :
    ExistsCompatibleClique g (List.range 41) l.length := by
  let s : Finset (Fin 41) := l.toFinset
  let sorted : List (Fin 41) := (List.finRange 41).filter (· ∈ s)
  have hperm : l.Perm sorted := by
    apply List.perm_of_nodup_nodup_toFinset_eq hnd
    · exact (List.nodup_finRange 41).filter _
    · change l.toFinset = ((List.finRange 41).filter (· ∈ s)).toFinset
      ext x
      simp [s]
  have hsorted : sorted.Pairwise (fun u v => compatible g u.val v.val = true) :=
    (hperm.pairwise_iff (by intro u v; simp [compatible, Nat.land_comm])).mp hp
  refine ⟨sorted.map Fin.val, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hperm.length_eq.symm
  · have hbase : (List.finRange 41).map Fin.val = List.range 41 := by decide +kernel
    have hfilter : List.Sublist ((List.finRange 41).filter (· ∈ s)) (List.finRange 41) :=
      List.filter_sublist
    have hsub := hfilter.map Fin.val
    rw [hbase] at hsub
    simpa [sorted] using hsub
  · exact List.Pairwise.map Fin.val (by intro u v huv; exact huv) hsorted

private theorem no_disjoint_six_of_mask_iso {V : Type*} {G : SimpleGraph V}
    {g : Array Nat}
    {hsym : ∀ u v : Fin 41, Nat.testBit g[u.val]! v.val = Nat.testBit g[v.val]! u.val}
    {hloop : ∀ u : Fin 41, Nat.testBit g[u.val]! u.val = false}
    (iso : G ≃g maskGraph g hsym hloop)
    (hcompat : ∀ u v : Fin 41, Disjoint (maskNeighbors g u) (maskNeighbors g v) ↔
      compatible g u.val v.val = true)
    (hcert : ¬ ExistsCompatibleClique g (List.range 41) 6) :
    ¬ ∃ chosen : List V, chosen.length = 6 ∧ chosen.Nodup ∧
      chosen.Pairwise (fun u v => Disjoint (G.neighborSet u) (G.neighborSet v)) := by
  rintro ⟨chosen, hlen, hnd, hpairs⟩
  let mapped := chosen.map iso
  have hmappedLen : mapped.length = 6 := by simp [mapped, hlen]
  have hmappedNodup : mapped.Nodup := hnd.map iso.injective
  have hmappedPairs : mapped.Pairwise (fun u v => compatible g u.val v.val = true) := by
    apply List.pairwise_map.mpr
    apply hpairs.imp
    intro u v huv
    apply (hcompat _ _).mp
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    have hx₁' : iso.symm x ∈ G.neighborSet u := by
      apply (SimpleGraph.Iso.apply_mem_neighborSet_iff iso).mp
      rw [show iso (iso.symm x) = x from iso.right_inv x]
      simpa [maskNeighbors, maskGraph] using hx₁
    have hx₂' : iso.symm x ∈ G.neighborSet v := by
      apply (SimpleGraph.Iso.apply_mem_neighborSet_iff iso).mp
      rw [show iso (iso.symm x) = x from iso.right_inv x]
      simpa [maskNeighbors, maskGraph] using hx₂
    exact (Set.disjoint_left.mp huv hx₁') hx₂'
  have hc := compatible_of_nodup_pairwise mapped hmappedNodup hmappedPairs
  exact hcert (by simpa [hmappedLen] using hc)

/-- An isomorphism to a certified seed rules out six distinct vertices
with pairwise disjoint open neighborhoods. -/
theorem no_disjoint_six_of_seed_iso {V : Type*} (G : SimpleGraph V)
    (hseed : Nonempty (G ≃g seed1Graph) ∨ Nonempty (G ≃g seed2Graph) ∨
      Nonempty (G ≃g seed3Graph)) :
    ¬ ∃ chosen : List V, chosen.length = 6 ∧ chosen.Nodup ∧
      chosen.Pairwise (fun u v => Disjoint (G.neighborSet u) (G.neighborSet v)) := by
  rcases hseed with h | h | h
  · obtain ⟨iso⟩ := h
    exact no_disjoint_six_of_mask_iso iso seed1_neighbor_disjoint_iff seed1_no_compatible_six
  · obtain ⟨iso⟩ := h
    exact no_disjoint_six_of_mask_iso iso seed2_neighbor_disjoint_iff seed2_no_compatible_six
  · obtain ⟨iso⟩ := h
    exact no_disjoint_six_of_mask_iso iso seed3_neighbor_disjoint_iff seed3_no_compatible_six

/-- A classified extremal deletion cannot contain a six-set satisfying the
compatibility condition used by `C4Extremal42`: such a set would give six
pairwise disjoint open neighborhoods in the deletion graph. -/
theorem no_compatible_six_in_seed_deletion (G : SimpleGraph (Fin 42))
    [DecidableRel G.Adj] (v : Fin 42)
    (hseed : Nonempty (G.induce ({v}ᶜ : Set (Fin 42)) ≃g seed1Graph) ∨
      Nonempty (G.induce ({v}ᶜ : Set (Fin 42)) ≃g seed2Graph) ∨
      Nonempty (G.induce ({v}ᶜ : Set (Fin 42)) ≃g seed3Graph)) :
    ¬ ∃ S : Finset (Fin 42), S.card = 6 ∧ v ∉ S ∧
      ∀ u ∈ S, ∀ w ∈ S, u ≠ w → ∀ x, x ≠ v → G.Adj u x → ¬ G.Adj w x := by
  intro h
  obtain ⟨S, hcard, hvS, hcompat⟩ := h
  let e : {x : Fin 42 // x ∈ S} ↪ {x : Fin 42 // x ∈ ({v}ᶜ : Set (Fin 42))} :=
    ⟨fun x => ⟨x.1, by
      change x.1 ≠ v
      intro hx
      apply hvS
      simpa [hx] using x.2⟩, fun a b hab => by
      apply Subtype.ext
      exact congrArg (fun x : {x : Fin 42 // x ∈ ({v}ᶜ : Set (Fin 42))} => x.1) hab⟩
  let T : Finset {x : Fin 42 // x ∈ ({v}ᶜ : Set (Fin 42))} := S.attach.map e
  have hTcard : T.card = 6 := by simp [T, e, hcard]
  have hTnodup : T.toList.Nodup := Finset.nodup_toList T
  have hTpair : T.toList.Pairwise (fun a b =>
      Disjoint ((G.induce ({v}ᶜ : Set (Fin 42))).neighborSet a)
        ((G.induce ({v}ᶜ : Set (Fin 42))).neighborSet b)) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro a b hab
    have hab' : a.1 ≠ b.1 := by
      intro heq
      have hnd := hTnodup.sublist hab
      have heq' : a = b := Subtype.ext heq
      exact (by simpa [heq'] using hnd)
    have haTList : a ∈ T.toList := hab.subset (by simp)
    have hbTList : b ∈ T.toList := hab.subset (by simp)
    have haT : a ∈ T := by simpa using haTList
    have hbT : b ∈ T := by simpa using hbTList
    obtain ⟨a', ha'S, haEq⟩ := Finset.mem_map.mp haT
    obtain ⟨b', hb'S, hbEq⟩ := Finset.mem_map.mp hbT
    have haS : a.1 ∈ S := by
      have hv := a'.2
      have heq' : a'.1 = a.1 := congrArg Subtype.val haEq
      simpa [heq'] using hv
    have hbS : b.1 ∈ S := by
      have hv := b'.2
      have heq' : b'.1 = b.1 := congrArg Subtype.val hbEq
      simpa [heq'] using hv
    apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have hx₁' : G.Adj a.1 x.1 := by simpa [SimpleGraph.induce_adj] using hx₁
    have hx₂' : G.Adj b.1 x.1 := by simpa [SimpleGraph.induce_adj] using hx₂
    exact hcompat a.1 haS b.1 hbS hab' x.1 x.property hx₁' hx₂'
  have hn := no_disjoint_six_of_seed_iso
    (G.induce ({v}ᶜ : Set (Fin 42))) hseed
  apply hn
  refine ⟨T.toList, ?_, hTnodup, hTpair⟩
  simpa using hTcard

/-- If every 132-edge deletion is isomorphic to one of the three certified
seeds, then the one-vertex counting reduction gives the 137-edge bound.  This
is conditional on that classification premise; the three records are not
claimed to exhaust all extremal 41-vertex graphs. -/
theorem simpleGraph_c4Free_edge_count_le_137_of_seed_classification
    (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    (h41 : ∀ v, C4Extremal42.inducedDeletionCount G v ≤ 132)
    (hclass : ∀ v, C4Extremal42.inducedDeletionCount G v = 132 →
      Nonempty (G.induce ({v}ᶜ : Set (Fin 42)) ≃g seed1Graph) ∨
        Nonempty (G.induce ({v}ᶜ : Set (Fin 42)) ≃g seed2Graph) ∨
        Nonempty (G.induce ({v}ᶜ : Set (Fin 42)) ≃g seed3Graph)) :
    G.edgeFinset.card ≤ 137 := by
  apply C4Extremal42.simpleGraph_c4Free_edge_count_le_137 G hfree h41
  intro v hd
  exact no_compatible_six_in_seed_deletion G v (hclass v hd)

/-- Exhaustiveness of the three certificates among 41-vertex four-cycle-free
graphs with 132 edges. This is an explicit mathematical input. -/
def Ex41SeedClassification : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V),
    Fintype.card V = 41 → C4VertexExtension.C4Free H → H.edgeSet.ncard = 132 →
      Nonempty (H ≃g seed1Graph) ∨ Nonempty (H ≃g seed2Graph) ∨ Nonempty (H ≃g seed3Graph)

/-- Together, the published 41-vertex upper bound and an exhaustive
classification by the three certified seeds would give the 137-edge upper bound. -/
theorem edge_count_le_137_of_ex41_and_seed_classification
    (h41 : Implications.C4PolaritySurvivorBound.Ex41C4Bound)
    (hclass : Ex41SeedClassification) (G : SimpleGraph (Fin 42)) [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 4).Free G) : G.edgeFinset.card ≤ 137 := by
  classical
  have hC4 : C4VertexExtension.C4Free G := by
    rintro x y z w hxy hzw hxz hyz ⟨hxw, hyw⟩
    exact hzw (C4Extremal42.commonNeighbors_subsingleton_of_cycleGraph_free G hfree x y hxy
      ⟨hxz, hyz⟩ ⟨hxw, hyw⟩)
  apply simpleGraph_c4Free_edge_count_le_137_of_seed_classification G hfree
    (C4Extremal42.deletion_count_le_132_of_ex41 h41 G hC4)
  intro v hv
  let S : Set (Fin 42) := {v}ᶜ
  have hcard : Fintype.card S = 41 := by
    change Fintype.card {i : Fin 42 // i ≠ v} = 41
    simp [Fintype.card_subtype_compl]
  apply hclass (G.induce S) hcard (Implications.C4PolaritySurvivorBound.c4Free_induce G hC4 S)
  simpa only [C4Extremal42.inducedDeletionCount, S, SimpleGraph.edgeFinset_card,
    Set.fintypeCard_eq_ncard] using hv

#print axioms edge_count_le_137_of_ex41_and_seed_classification
#print axioms seed1_no_compatible_six
#print axioms seed2_no_compatible_six
#print axioms seed3_no_compatible_six
#print axioms no_disjoint_six_of_seed_iso
#print axioms no_compatible_six_in_seed_deletion
#print axioms simpleGraph_c4Free_edge_count_le_137_of_seed_classification

end C4SeedCertificates
