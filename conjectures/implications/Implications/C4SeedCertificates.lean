import Mathlib.Data.Nat.Bitwise

/-!
# Finite certificates for the three published 41-vertex `C₄` extremal seeds

The sparse6 records in McKay's `c4_n41e132.maybe.s6` are represented here by
their 41 neighbourhood bitmasks.  For vertices `u` and `v`, having no common
neighbour is the bitwise condition `land (N u) (N v) = 0`.

`compatibleCliqueSearch` is a depth-pruned search.  It either skips the next
candidate, or takes it and restricts later candidates to vertices compatible
with it.  The proposition-valued recursion is itself the search's
specification; `checker` turns that proposition into a Boolean decision.  The
three closed Boolean results below are checked by `native_decide`, and
`checker_false` converts each Boolean result back to the proposition.

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
termination_by candidates remaining => candidates.length + remaining
decreasing_by
  · simp_wf
  · simp_wf
    have hfilter : (vs.filter (compatible g v)).length ≤ vs.length :=
      List.length_filter_le _ _
    omega

/-- The proposition represented by the Boolean search result. -/
def compatibleCliqueSearch (g : Array Nat) (candidates : List Nat) (size : Nat) : Prop :=
  compatibleCliqueSearchBool g candidates size = true

/-- The executable Boolean certificate for a graph's candidate set and clique size. -/
def checker (g : Array Nat) (vertices size : Nat) : Bool :=
  compatibleCliqueSearchBool g (List.range vertices) size

/-- A false Boolean certificate proves that the corresponding search proposition is false. -/
theorem checker_false {g : Array Nat} {vertices size : Nat}
    (h : checker g vertices size = false) :
    ¬ compatibleCliqueSearch g (List.range vertices) size := by
  intro hc
  change compatibleCliqueSearchBool g (List.range vertices) size = true at hc
  change compatibleCliqueSearchBool g (List.range vertices) size = false at h
  rw [hc] at h
  contradiction

private def seed1 : Array Nat := #[21541946382, 4325701, 2181050499, 274888393777, 805310568, 1236950712984, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 537468948, 1168233469956, 1099679499328, 4296294592, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 8642363656, 377880576, 137598353412, 1116978282497, 292632412672, 553060925520, 13023318032, 139859069952, 319169757316, 696321867777, 1140859076864, 103280542209, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952, 8657068064]

private def seed2 : Array Nat := #[21541946382, 4325701, 2181050499, 274888393777, 805310568, 137439085208, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 1100049096724, 68721842180, 167871552, 1103807922368, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 1108153991432, 377880576, 137598353412, 17466654721, 292632412672, 553060925520, 13023318032, 1239370697728, 319169757316, 696321867777, 41347449088, 1202792169985, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952, 18262036480]

private def seed3 : Array Nat := #[21541946382, 4325701, 2181050499, 274888393777, 1100316938344, 137439085208, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1100585641728, 537468948, 68721842180, 167871552, 4296294592, 584116229120, 34381037602, 279189825536, 412385087744, 1099585585280, 618488930312, 1748107266, 8642363656, 377880576, 1237109981188, 17466654721, 292632412672, 553060925520, 13023318032, 139859069952, 319169757316, 696321867777, 41347449088, 103280542209, 1196148588544, 188980666432, 74122264608, 2282487816, 4565565952, 34394343440]

theorem seed1_no_compatible_six :
    ¬ compatibleCliqueSearch seed1 (List.range 41) 6 := by
  apply checker_false
  native_decide

theorem seed2_no_compatible_six :
    ¬ compatibleCliqueSearch seed2 (List.range 41) 6 := by
  apply checker_false
  native_decide

theorem seed3_no_compatible_six :
    ¬ compatibleCliqueSearch seed3 (List.range 41) 6 := by
  apply checker_false
  native_decide

end C4SeedCertificates
