import Implications.C4Extremal42RootedClauses
import Implications.C4SequentialAtMostOne

/-! The common-neighbor encoding for each non-root vertex pair. -/

namespace C4Extremal42

/-- The vertices that can be common neighbors of a non-root pair in the
graph with root 0 deleted. -/
def CommonNeighborIndices (u v : Fin 42) := {w : Fin 42 // w ≠ 0 ∧ w ≠ u ∧ w ≠ v}

/-- There are 39 candidates for each pair of distinct non-root vertices. -/
noncomputable def commonNeighborEnumeration (u v : Fin 42)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) : Fin 39 ≃ CommonNeighborIndices u v := by
  classical
  let S := (((Finset.univ : Finset (Fin 42)).erase 0).erase u).erase v
  have hS : S.card = 39 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (by simp [hv, huv.symm]),
      Finset.card_erase_of_mem (by simp [hu]), Finset.card_erase_of_mem (by simp)]
    simp
  have hcard : Fintype.card S = 39 := by simpa only [Fintype.card_coe] using hS
  exact (Fintype.equivFinOfCardEq hcard).symm.trans
    (Equiv.subtypeEquivRight fun w => by
      simp [S, and_assoc, and_comm, and_left_comm])

/-- Auxiliary flags and prefix variables exist exactly when the pair has
at most one common neighbor outside the root. The equivalence holds for
every ordering of the 39 candidate vertices. -/
theorem common_neighbor_flags_iff (G : SimpleGraph (Fin 42)) (u v : Fin 42)
    (enumerate : Fin 39 ≃ CommonNeighborIndices u v) :
    (∃ flags : Fin 39 → Prop,
      (∀ i, G.Adj u (enumerate i).val ∧ G.Adj v (enumerate i).val → flags i) ∧
      ∃ seen, C4SequentialAtMostOne.Sequential flags seen) ↔
      ∀ x y : CommonNeighborIndices u v, x ≠ y →
        ¬ ((G.Adj u x.val ∧ G.Adj v x.val) ∧ (G.Adj u y.val ∧ G.Adj v y.val)) := by
  rw [C4SequentialAtMostOne.exists_flags_sequential_iff]
  constructor
  · intro h x y hxy hboth
    let i := enumerate.symm x
    let j := enumerate.symm y
    have hij : i ≠ j := fun heq => hxy (enumerate.symm.injective heq)
    have hi : G.Adj u (enumerate i).val ∧ G.Adj v (enumerate i).val := by
      simpa [i] using hboth.1
    have hj : G.Adj u (enumerate j).val ∧ G.Adj v (enumerate j).val := by
      simpa [j] using hboth.2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt ⟨hi, hj⟩
    · exact h j i hgt ⟨hj, hi⟩
  · intro h i j hij
    exact h (enumerate i) (enumerate j) (fun heq => hij.ne (enumerate.injective heq))

/-- The fixed-root common-neighbor clauses characterize four-cycle-freeness.
The original root clauses are paired with one sequential counter for each
unordered non-root pair. -/
theorem c4Free_iff_rooted_common_neighbor_flags (G : SimpleGraph (Fin 42))
    (hroot : ∀ u, G.Adj (0 : Fin 42) u ↔ 0 < u ∧ u ≤ 6) :
    C4VertexExtension.C4Free G ↔ RootCycleClauses G ∧
      ∀ u v : Fin 42, ∀ (hu : u ≠ 0) (hv : v ≠ 0) (huv : u < v),
        (let enumerate := commonNeighborEnumeration u v hu hv huv.ne
         ∃ flags : Fin 39 → Prop,
          (∀ i, G.Adj u (enumerate i).val ∧ G.Adj v (enumerate i).val → flags i) ∧
          ∃ seen, C4SequentialAtMostOne.Sequential flags seen) := by
  constructor
  · intro hfree
    refine ⟨((c4Free_iff_rooted_cycle_clauses G hroot).mp hfree).2, ?_⟩
    intro u v hu hv huv
    dsimp only
    apply (common_neighbor_flags_iff G u v _).mpr
    intro x y hxy hboth
    have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    exact hfree huv.ne hval hboth.1.1 hboth.1.2 hboth.2
  · rintro ⟨hRootClauses, ham⟩
    apply (c4Free_iff_rooted_cycle_clauses G hroot).mpr
    refine ⟨?_, hRootClauses⟩
    intro u v x y huv hxy hux' hu hv hx hy huy' hvx' hvy' hux hvx hboth
    have h := (common_neighbor_flags_iff G u v _).mp (ham u v hu hv huv)
    exact h ⟨x, hx, hux'.ne.symm, hvx'.symm⟩ ⟨y, hy, huy'.symm, hvy'.symm⟩
      (fun h => hxy.ne (congrArg Subtype.val h)) ⟨⟨hux, hvx⟩, hboth⟩

#print axioms common_neighbor_flags_iff
#print axioms c4Free_iff_rooted_common_neighbor_flags

end C4Extremal42
