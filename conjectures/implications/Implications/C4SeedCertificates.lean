import Mathlib.Data.Nat.Bitwise

/-!
# Finite certificates for the three published 41-vertex `C₄` extremal seeds

The [McKay sparse6 data file](https://users.cecs.anu.edu.au/~bdm/data/extremal/c4_n41e132.maybe.s6)
is represented here
by their 41 neighbourhood bitmasks.  Their SHA-256 digests, in order, are
`4033a0cc2e1e8f6d7cb05009d2ed0b0cfcec9ce969d76c6ed2faec68b3405927`,
`7b21f509d31f8002aba9c00d5a21a1db422177bd6a832cee6b4e80dad460db60`, and
`8282afa2558555cbdad70ff78767b188cd328b83626e8b59c0f11ad31e000042`.
Each record decodes to 41 vertices and 132 edges.  For vertices `u` and `v`, having no common
neighbour is the bitwise condition `land (N u) (N v) = 0`.

`compatibleCliqueSearch` is a depth-pruned search.  It either skips the next
candidate, or takes it and restricts later candidates to vertices compatible
with it.  The proposition-valued recursion is itself the search's
specification, proved equivalent to the Boolean checker by `search_correct`.
The three closed Boolean results below are checked by `native_decide`, and
`checker_false` converts each Boolean result back to its proposition.

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
termination_by candidates => candidates.length
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
theorem search_sound (g : Array Nat) (candidates : List Nat) (size : Nat)
    (h : compatibleCliqueSearchBool g candidates size = true) :
    ExistsCompatibleClique g candidates size := by
  cases size with
  | zero =>
      exact ⟨[], by simp, List.nil_sublist _, List.Pairwise.nil⟩
  | succ size =>
    cases candidates with
    | nil => simp [compatibleCliqueSearchBool] at h
    | cons v vs =>
      have hsplit :
          compatibleCliqueSearchBool g vs (size + 1) = true ∨
            compatibleCliqueSearchBool g (vs.filter (compatible g v)) size = true := by
        simpa [compatibleCliqueSearchBool, Bool.or_eq_true] using h
      rcases hsplit with hskip | htake
      · obtain ⟨chosen, hlen, hsub, hpairs⟩ := search_sound g vs (size + 1) hskip
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
    omega
  · simp_wf
    have hfilter : (vs.filter (compatible g v)).length ≤ vs.length :=
      List.length_filter_le _ _
    omega

/-- A genuine compatible sublist is found by the depth-pruned checker. -/
theorem search_complete (g : Array Nat) (candidates : List Nat) (size : Nat)
    (h : ExistsCompatibleClique g candidates size) :
    compatibleCliqueSearchBool g candidates size = true := by
  obtain ⟨chosen, hlen, hsub, hpairs⟩ := h
  cases size with
  | zero => simp [compatibleCliqueSearchBool]
  | succ size =>
    cases candidates with
    | nil =>
        have hlenBound := hsub.length_le
        simp at hlenBound
        omega
    | cons v vs =>
        cases chosen with
        | nil => simp at hlen
        | cons a tail =>
          have hsplit : List.Sublist (a :: tail) (v :: vs) := hsub
          rcases (List.cons_sublist_cons'.mp hsplit) with htail | ⟨hav, htail⟩
          ·
            have hskip : ExistsCompatibleClique g vs (size + 1) :=
              ⟨a :: tail, hlen, htail, hpairs⟩
            rw [compatibleCliqueSearchBool, Bool.or_eq_true]
            exact Or.inl (search_complete g vs (size + 1) hskip)
          ·
            subst a
            have hlenTail : tail.length = size := by simpa using hlen
            have hpairsTail : tail.Pairwise (fun u w => compatible g u w = true) :=
              hpairs.of_cons
            have hcompatible : ∀ w ∈ tail, compatible g v w = true := by
              intro w hw
              exact hpairs.rel_of_pairwise_cons hw
            have htailFiltered :
                List.Sublist tail (vs.filter (compatible g v)) := by
              rw [← List.filter_eq_self.mpr hcompatible]
              exact htail.filter (compatible g v)
            have htake :
                ExistsCompatibleClique g (vs.filter (compatible g v)) size :=
              ⟨tail, hlenTail, htailFiltered, hpairsTail⟩
            rw [compatibleCliqueSearchBool, Bool.or_eq_true]
            exact Or.inr (search_complete g (vs.filter (compatible g v)) size htake)
termination_by candidates => candidates.length
decreasing_by
  · simp_wf
    omega
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
  native_decide

theorem seed2_no_compatible_six :
    ¬ ExistsCompatibleClique seed2 (List.range 41) 6 := by
  apply checker_false
  native_decide

theorem seed3_no_compatible_six :
    ¬ ExistsCompatibleClique seed3 (List.range 41) 6 := by
  apply checker_false
  native_decide

#print axioms seed1_no_compatible_six
#print axioms seed2_no_compatible_six
#print axioms seed3_no_compatible_six

end C4SeedCertificates
