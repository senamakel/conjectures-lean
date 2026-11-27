import Implications.C4Extremal42RootLabel

/-! Graph semantics of the two families of cycle clauses in the rooted search. -/

namespace C4Extremal42

/-- The four-literal clauses apply to four distinct non-root vertices,
using the two opposite pairs of the putative cycle. -/
def NonrootCycleClauses (G : SimpleGraph (Fin 42)) : Prop :=
  ∀ ⦃u v x y : Fin 42⦄, u < v → x < y → u < x →
    u ≠ 0 → v ≠ 0 → x ≠ 0 → y ≠ 0 → u ≠ y → v ≠ x → v ≠ y →
    G.Adj u x → G.Adj v x → ¬ (G.Adj u y ∧ G.Adj v y)

/-- The two-literal clauses forbid the fixed neighbors of root 0 from
sharing a second neighbor. -/
def RootCycleClauses (G : SimpleGraph (Fin 42)) : Prop :=
  ∀ ⦃u v x : Fin 42⦄, u < v → 0 < u → v ≤ 6 → x ≠ 0 → x ≠ u → x ≠ v →
    ¬ (G.Adj u x ∧ G.Adj v x)

private theorem nonroot_apply (G : SimpleGraph (Fin 42)) (h : NonrootCycleClauses G)
    (u v x y : Fin 42) (huv : u ≠ v) (hxy : x ≠ y)
    (hu : u ≠ 0) (hv : v ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y) :
    False := by
  wlog huv' : u < v generalizing u v
  · exact this v u huv.symm hxy hv hu hx hy hvx hux hvy huy (lt_of_le_of_ne (le_of_not_gt huv') huv.symm)
  wlog hxy' : x < y generalizing x y
  · exact this y x hxy.symm hy hx huy hvy hux hvx (lt_of_le_of_ne (le_of_not_gt hxy') hxy.symm)
  by_cases hux' : u < x
  · exact h huv' hxy' hux' hu hv hx hy huy.ne hvx.ne hvy.ne hux hvx ⟨huy, hvy⟩
  · have hxu : x < u := lt_of_le_of_ne (le_of_not_gt hux') hux.ne.symm
    exact h hxy' huv' hxu hx hy hu hv hvx.ne.symm huy.ne.symm hvy.ne.symm
      hux.symm huy.symm ⟨hvx.symm, hvy.symm⟩

private theorem root_apply (G : SimpleGraph (Fin 42)) (h : RootCycleClauses G)
    (hroot : ∀ u, G.Adj (0 : Fin 42) u ↔ 0 < u ∧ u ≤ 6)
    (u v x : Fin 42) (huv : u ≠ v) (hx : x ≠ 0)
    (hu : G.Adj 0 u) (hv : G.Adj 0 v) (hux : G.Adj u x) (hvx : G.Adj v x) :
    False := by
  rcases lt_or_gt_of_ne huv with hlt | hlt
  · exact h hlt ((hroot u).mp hu).1 ((hroot v).mp hv).2 hx hux.ne.symm hvx.ne.symm ⟨hux, hvx⟩
  · exact h hlt ((hroot v).mp hv).1 ((hroot u).mp hu).2 hx hvx.ne.symm hux.ne.symm ⟨hvx, hux⟩

/-- With the root labels fixed, the two clause families characterize
four-cycle-freeness. The four-literal family uses one clause per choice
of the two opposite pairs, ordered by the lower endpoint. -/
theorem c4Free_iff_rooted_cycle_clauses (G : SimpleGraph (Fin 42))
    (hroot : ∀ u, G.Adj (0 : Fin 42) u ↔ 0 < u ∧ u ≤ 6) :
    C4VertexExtension.C4Free G ↔ NonrootCycleClauses G ∧ RootCycleClauses G := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v x y huv hxy _ _ _ _ _ _ _ _ hux hvx
      exact h huv.ne hxy.ne hux hvx
    · intro u v x huv hu hv hx _ _
      have hu0 := (hroot u).mpr ⟨hu, huv.le.trans hv⟩
      have hv0 := (hroot v).mpr ⟨hu.trans huv, hv⟩
      exact h huv.ne hx.symm hu0.symm hv0.symm
  · rintro ⟨hnon, hrootClauses⟩ u v x y huv hxy hux hvx ⟨huy, hvy⟩
    by_cases hu : u = 0
    · subst u
      exact root_apply G hrootClauses hroot x y v hxy huv.symm hux huy hvx.symm hvy.symm
    by_cases hv : v = 0
    · subst v
      exact root_apply G hrootClauses hroot x y u hxy huv hvx hvy hux.symm huy.symm
    by_cases hx : x = 0
    · subst x
      exact root_apply G hrootClauses hroot u v y huv hxy.symm hux.symm hvx.symm huy hvy
    by_cases hy : y = 0
    · subst y
      exact root_apply G hrootClauses hroot u v x huv hxy huy.symm hvy.symm hux hvx
    exact nonroot_apply G hnon u v x y huv hxy hu hv hx hy hux hvx huy hvy

/-- When all degrees are in the search window, the edge count is encoded
by 24 true degree-threshold flags on the non-root vertices. -/
theorem edge_count_eq_138_iff_rooted_degree_flags (G : SimpleGraph (Fin 42))
    [DecidableRel G.Adj] (hzero : G.degree 0 = 6)
    (hwindow : ∀ v, 6 ≤ G.degree v ∧ G.degree v ≤ 8) :
    G.edgeFinset.card = 138 ↔
      (∑ v ∈ (Finset.univ : Finset (Fin 42)).erase 0,
        ((if 7 ≤ G.degree v then 1 else 0) + (if 8 ≤ G.degree v then 1 else 0))) = 24 := by
  let flags : Fin 42 → ℕ := fun v =>
    (if 7 ≤ G.degree v then 1 else 0) + (if 8 ≤ G.degree v then 1 else 0)
  change _ ↔ (∑ v ∈ (Finset.univ : Finset (Fin 42)).erase 0, flags v) = 24
  have hsum : (∑ v : Fin 42, G.degree v) = 252 + ∑ v : Fin 42, flags v := by
    calc
      _ = ∑ v : Fin 42, (6 + flags v) := by
        apply Finset.sum_congr rfl
        intro v _
        have hv := hwindow v
        dsimp [flags]
        split <;> split <;> omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hz : flags 0 = 0 := by simp [flags, hzero]
  have herase := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 42)))
    flags (Finset.mem_univ (0 : Fin 42))
  rw [hz, add_zero] at herase
  rw [G.sum_degrees_eq_twice_card_edges, ← herase] at hsum
  omega

#print axioms c4Free_iff_rooted_cycle_clauses
#print axioms edge_count_eq_138_iff_rooted_degree_flags

end C4Extremal42
