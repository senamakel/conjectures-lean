import HajosCatlin.Statement
import HajosCatlin.Graph

/-!
# `C₅[K₃]` contains no subdivision of `K₈`

Suppose `f : Fin 8 → V` and paths `P` form a subdivision model of `K₈` in `C₅[K₃]`. Write
`a c` for the number of branch vertices in column `c` (so `a c ≤ 3` and `∑ a c = 8`), and call
a vertex *free* if it is not a branch vertex (there are `15 − 8 = 7`).

Two branch vertices are non-adjacent exactly when their columns differ by `±2`. Group these pairs
by their *middle* column: a pair of type `c` has one end in column `c − 1` and the other in
column `c + 1`, and there are `a (c−1) · a (c+1)` of them (`S f c` below).

1. (`walk_cross`) A walk from column `c − 1` to column `c + 1` meets column `c`, or else it
   stays in columns `c + 2, c + 3, c + 4, c + 1` and, stepping by at most one column at a time,
   passes through both `c + 2` and `c + 3`. Either way its interior (the vertices other than the
   two ends, `support.tail.dropLast`) meets column `c`, or has at least two vertices.
2. The interiors are free (`internal_avoid`) and pairwise disjoint (`internal_disjoint`), so
   their sizes add up to at most `7`.
3. The pairs of type `c` whose interior meets column `c` have disjoint interiors, each containing
   a free vertex of column `c`; there are at most `3 − a c` of those.

Together: `2 ∑ a(c−1)a(c+1) ≤ 7 + ∑ min (a(c−1)a(c+1)) (3 − a c)`. A check over the `4⁵`
vectors `a` (kernel `decide`) shows the left side always exceeds the right (`arith`).
-/

open SimpleGraph HajosConjecture Finset

namespace HajosCatlin

/-! ### Columns along a walk -/

private lemma fin5_step : ∀ i j c : Fin 5, (j = i ∨ j = i + 1 ∨ i = j + 1) → i ≠ c → j ≠ c →
    (i - c).val ≤ (j - c).val + 1 := by decide

private lemma fin5_facts : ∀ c : Fin 5, (c - 1 - c).val = 4 ∧ (c + 1 - c).val = 1 ∧
    c ≠ c - 1 ∧ c ≠ c + 1 ∧ c - 1 ≠ c + 1 := by decide

private lemma fin5_sub_val : ∀ i c : Fin 5, (i - c).val = 2 → i = c + 2 := by decide

private lemma fin5_swap : ∀ c c' : Fin 5, c - 1 = c' + 1 → c + 1 = c' - 1 → False := by decide

lemma adj_col {x y : Fin 5 × Fin 3} (h : catlin.Adj x y) :
    y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ x.1 = y.1 + 1 := by
  change catlinAdj x y at h
  rcases h with ⟨h1, _⟩ | h | h
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Discrete intermediate value theorem: a walk that avoids column `c` takes every value of
`(column − c)` between its two ends. -/
lemma walk_ivt (c : Fin 5) {u v : Fin 5 × Fin 3} (p : catlin.Walk u v) :
    (∀ x ∈ p.support, x.1 ≠ c) → ∀ t : ℕ, (v.1 - c).val ≤ t → t ≤ (u.1 - c).val →
      ∃ x ∈ p.support, (x.1 - c).val = t := by
  induction p with
  | nil =>
    intro _ t h1 h2
    exact ⟨_, Walk.start_mem_support _, by omega⟩
  | @cons u w v h q ih =>
    intro hav t h1 h2
    have hu : u.1 ≠ c := hav u (Walk.start_mem_support _)
    have hq : ∀ x ∈ q.support, x.1 ≠ c := fun x hx => hav x (by simp [Walk.support_cons, hx])
    by_cases ht : t ≤ (w.1 - c).val
    · obtain ⟨x, hx, hxt⟩ := ih hq t h1 ht
      exact ⟨x, by simp [Walk.support_cons, hx], hxt⟩
    · have := fin5_step _ _ _ (adj_col h) hu (hq w (Walk.start_mem_support q))
      exact ⟨u, Walk.start_mem_support _, by omega⟩

/-- A vertex of a walk other than its two ends lies in `support.tail.dropLast`. -/
lemma mem_interior {W : Type*} {G : SimpleGraph W} {u v : W} (p : G.Walk u v) {x : W}
    (hx : x ∈ p.support) (hu : x ≠ u) (hv : x ≠ v) : x ∈ p.support.tail.dropLast := by
  cases p with
  | nil => exact absurd (List.mem_singleton.mp hx) hu
  | cons h q =>
    rw [Walk.support_cons, List.tail_cons]
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact absurd hx hu
    · rw [← List.dropLast_append_getLast (Walk.support_ne_nil q), List.mem_append] at hx
      rcases hx with hx | hx
      · exact hx
      · rw [Walk.getLast_support, List.mem_singleton] at hx
        exact absurd hx hv

/-- **Step 1.** The interior of a walk from column `c − 1` to column `c + 1` meets column `c`,
or has two distinct vertices. -/
lemma walk_cross {u v : Fin 5 × Fin 3} (p : catlin.Walk u v) (c : Fin 5)
    (hu : u.1 = c - 1) (hv : v.1 = c + 1) :
    (∃ x ∈ p.support.tail.dropLast, x.1 = c) ∨
      ∃ x ∈ p.support.tail.dropLast, ∃ y ∈ p.support.tail.dropLast, x ≠ y := by
  obtain ⟨h4, h1, hc1, hc2, -⟩ := fin5_facts c
  by_cases h : ∃ x ∈ p.support, x.1 = c
  · obtain ⟨x, hx, hxc⟩ := h
    left
    refine ⟨x, mem_interior p hx ?_ ?_, hxc⟩
    · rintro rfl; exact hc1 (hxc.symm.trans hu)
    · rintro rfl; exact hc2 (hxc.symm.trans hv)
  · push Not at h
    right
    rw [← hu] at h4
    rw [← hv] at h1
    obtain ⟨x, hx, hx2⟩ := walk_ivt c p h 2 (by omega) (by omega)
    obtain ⟨y, hy, hy3⟩ := walk_ivt c p h 3 (by omega) (by omega)
    refine ⟨x, mem_interior p hx ?_ ?_, y, mem_interior p hy ?_ ?_, ?_⟩ <;>
      rintro rfl <;> omega

/-! ### Counting -/

/-- The arithmetic core: for every column-count vector `a` with entries `≤ 3` summing to `8`,
`7 + ∑ min (a(c−1)a(c+1)) (3 − a c) < 2 ∑ a(c−1)a(c+1)`. Checked by the kernel over `4⁵` vectors. -/
lemma arith (a : Fin 5 → ℕ) (ha : ∀ c, a c ≤ 3) (hs : ∑ c, a c = 8) :
    7 + ∑ c, min (a (c - 1) * a (c + 1)) (3 - a c) < 2 * ∑ c, a (c - 1) * a (c + 1) := by
  have key : ∀ a0 < 4, ∀ a1 < 4, ∀ a2 < 4, ∀ a3 < 4, ∀ a4 < 4, a0 + a1 + a2 + a3 + a4 = 8 →
      7 + (min (a4 * a1) (3 - a0) + min (a0 * a2) (3 - a1) + min (a1 * a3) (3 - a2) +
        min (a2 * a4) (3 - a3) + min (a3 * a0) (3 - a4)) <
      2 * (a4 * a1 + a0 * a2 + a1 * a3 + a2 * a4 + a3 * a0) := by
    decide
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceSub, Fin.reduceAdd] at hs ⊢
  exact key _ (by have := ha 0; omega) _ (by have := ha 1; omega) _ (by have := ha 2; omega)
    _ (by have := ha 3; omega) _ (by have := ha 4; omega) hs

variable {f : Fin 8 → Fin 5 × Fin 3}
  {P : ∀ w w', (completeGraph (Fin 8)).Adj w w' → catlin.Walk (f w) (f w')}

/-- The non-adjacent branch pairs of type `c`: one end in column `c − 1`, the other in `c + 1`. -/
def S (f : Fin 8 → Fin 5 × Fin 3) (c : Fin 5) : Finset (Fin 8 × Fin 8) :=
  (univ.filter fun w => (f w).1 = c - 1) ×ˢ (univ.filter fun w => (f w).1 = c + 1)

/-- The interior of the path of the pair `e.2`, as a finset. -/
def interior (P : ∀ w w', (completeGraph (Fin 8)).Adj w w' → catlin.Walk (f w) (f w'))
    (e : Σ _ : Fin 5, Fin 8 × Fin 8) : Finset (Fin 5 × Fin 3) :=
  if h : e.2.1 ≠ e.2.2 then (P e.2.1 e.2.2 h).support.tail.dropLast.toFinset else ∅

lemma mem_S {c : Fin 5} {p : Fin 8 × Fin 8} :
    p ∈ S f c ↔ (f p.1).1 = c - 1 ∧ (f p.2).1 = c + 1 := by
  simp [S]

lemma S_ne {c : Fin 5} {p : Fin 8 × Fin 8} (hp : p ∈ S f c) : p.1 ≠ p.2 := by
  rw [mem_S] at hp
  intro h
  rw [h] at hp
  exact (fin5_facts c).2.2.2.2 (hp.1.symm.trans hp.2)

lemma interior_eq {c : Fin 5} {p : Fin 8 × Fin 8} (hp : p ∈ S f c) :
    interior P ⟨c, p⟩ = (P p.1 p.2 (S_ne hp)).support.tail.dropLast.toFinset :=
  dif_pos (S_ne hp)

section Model

variable (hM : IsSubdivisionModel (completeGraph (Fin 8)) catlin f P)
include hM

/-- **Step 2a.** Interiors consist of free vertices. -/
lemma interior_subset (e : Σ _ : Fin 5, Fin 8 × Fin 8) :
    interior P e ⊆ (univ.image f)ᶜ := by
  unfold interior
  split_ifs with h
  · intro x hx
    rw [List.mem_toFinset] at hx
    have := hM.internal_avoid _ _ h x hx
    simpa [Set.mem_range] using this
  · exact empty_subset _

/-- **Step 2b.** Interiors of distinct pairs are disjoint. -/
lemma interior_disjoint {e e' : Σ _ : Fin 5, Fin 8 × Fin 8}
    (he : e ∈ univ.sigma (S f)) (he' : e' ∈ univ.sigma (S f)) (hne : e ≠ e') :
    Disjoint (interior P e) (interior P e') := by
  obtain ⟨c, w, w'⟩ := e
  obtain ⟨c', x, x'⟩ := e'
  have hw : (w, w') ∈ S f c := (mem_sigma.mp he).2
  have hx : (x, x') ∈ S f c' := (mem_sigma.mp he').2
  rw [interior_eq hw, interior_eq hx, Finset.disjoint_left]
  intro y hy hy'
  rw [List.mem_toFinset] at hy hy'
  refine hM.internal_disjoint w w' (S_ne hw) x x' (S_ne hx) ?_ y hy hy'
  rw [mem_S] at hw hx
  intro hs
  rw [Sym2.eq_iff] at hs
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply hne
    have : c = c' := sub_left_inj.mp (hw.1.symm.trans hx.1)
    subst this
    rfl
  · exact fin5_swap c c' (hw.1.symm.trans hx.2) (hw.2.symm.trans hx.1)

/-- **Step 2.** The interiors of all non-adjacent branch pairs have at most `7` vertices in all. -/
lemma sum_interior_le :
    ∑ c, ∑ p ∈ S f c, (interior P ⟨c, p⟩).card ≤ 7 := by
  have hsig : ∑ e ∈ univ.sigma (S f), (interior P e).card =
      ∑ c, ∑ p ∈ S f c, (interior P ⟨c, p⟩).card := sum_sigma _ _ _
  rw [← hsig, ← card_biUnion (fun e he e' he' hne =>
    interior_disjoint hM (mem_coe.mp he) (mem_coe.mp he') hne)]
  calc ((univ.sigma (S f)).biUnion (interior P)).card
      ≤ ((univ : Finset (Fin 8)).image f)ᶜ.card :=
        card_le_card (biUnion_subset.mpr fun e _ => interior_subset hM e)
    _ = 7 := by
        rw [card_compl, card_image_of_injective _ hM.injective]
        simp

/-- The pairs of type `c` whose interior meets column `c`. -/
def E1 (f : Fin 8 → Fin 5 × Fin 3)
    (P : ∀ w w', (completeGraph (Fin 8)).Adj w w' → catlin.Walk (f w) (f w')) (c : Fin 5) :
    Finset (Fin 8 × Fin 8) :=
  (S f c).filter fun p => ∃ x ∈ interior P ⟨c, p⟩, x.1 = c

omit hM in
/-- **Step 1, counted.** Each pair of type `c` has `2 ≤ |interior| + [interior meets column c]`. -/
lemma two_le (c : Fin 5) {p : Fin 8 × Fin 8} (hp : p ∈ S f c) :
    2 ≤ (interior P ⟨c, p⟩).card + (if ∃ x ∈ interior P ⟨c, p⟩, x.1 = c then 1 else 0) := by
  have hp' := mem_S.mp hp
  have hcross := walk_cross (P p.1 p.2 (S_ne hp)) c hp'.1 hp'.2
  rcases hcross with ⟨x, hx, hxc⟩ | ⟨x, hx, y, hy, hxy⟩
  · have hx' : x ∈ interior P ⟨c, p⟩ := by rw [interior_eq hp]; exact List.mem_toFinset.mpr hx
    rw [if_pos ⟨x, hx', hxc⟩]
    have := card_pos.mpr ⟨x, hx'⟩
    omega
  · have : 1 < (interior P ⟨c, p⟩).card := by
      rw [interior_eq hp]
      exact one_lt_card.mpr ⟨x, List.mem_toFinset.mpr hx, y, List.mem_toFinset.mpr hy, hxy⟩
    omega

/-- **Step 3.** At most `3 − a c` pairs of type `c` reach a free vertex of column `c`; here in the
form `|E1 c| + a c ≤ 3`. -/
lemma card_E1_add (c : Fin 5) :
    (E1 f P c).card + (univ.filter fun w : Fin 8 => (f w).1 = c).card ≤ 3 := by
  set F := (((univ : Finset (Fin 8)).image f)ᶜ).filter fun x => x.1 = c
  have hE1 : (E1 f P c).card ≤ F.card := by
    have hdisj : ((E1 f P c : Set (Fin 8 × Fin 8))).PairwiseDisjoint
        (fun p => (interior P ⟨c, p⟩).filter fun x => x.1 = c) := by
      intro p hp p' hp' hne
      have hp1 := (mem_filter.mp (mem_coe.mp hp)).1
      have hp2 := (mem_filter.mp (mem_coe.mp hp')).1
      refine disjoint_filter_filter (interior_disjoint hM (mem_sigma.mpr ⟨mem_univ _, hp1⟩)
        (mem_sigma.mpr ⟨mem_univ _, hp2⟩) ?_)
      intro h
      exact hne (by simpa using h)
    calc (E1 f P c).card = ∑ p ∈ E1 f P c, 1 := card_eq_sum_ones _
      _ ≤ ∑ p ∈ E1 f P c, ((interior P ⟨c, p⟩).filter fun x => x.1 = c).card := by
          apply sum_le_sum
          intro p hp
          obtain ⟨x, hx, hxc⟩ := (mem_filter.mp hp).2
          exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, hxc⟩⟩
      _ = ((E1 f P c).biUnion fun p => (interior P ⟨c, p⟩).filter fun x => x.1 = c).card :=
          (card_biUnion hdisj).symm
      _ ≤ F.card := by
          apply card_le_card
          rw [biUnion_subset]
          intro p _
          exact filter_subset_filter _ (interior_subset hM _)
  have hcol : F ∪ (univ.filter fun w : Fin 8 => (f w).1 = c).image f ⊆
      (univ : Finset (Fin 3)).image fun b => (c, b) := by
    intro x hx
    rw [mem_image]
    refine ⟨x.2, mem_univ _, ?_⟩
    rcases mem_union.mp hx with hx | hx
    · exact Prod.ext (mem_filter.mp hx).2.symm rfl
    · obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
      exact Prod.ext (mem_filter.mp hw).2.symm rfl
  have hdisj : Disjoint F ((univ.filter fun w : Fin 8 => (f w).1 = c).image f) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (mem_filter.mp hx).1
    rw [mem_compl] at h1
    exact h1 (image_subset_image (filter_subset _ _) hx')
  have := card_le_card hcol
  rw [card_union_of_disjoint hdisj, card_image_of_injective _ hM.injective] at this
  have h3 : ((univ : Finset (Fin 3)).image fun b => ((c, b) : Fin 5 × Fin 3)).card ≤ 3 :=
    (card_image_le).trans (by simp)
  omega

end Model

/-- **`C₅[K₃]` contains no subdivision of `K₈`.** -/
theorem not_containsSubdivision : ¬ ContainsSubdivision (completeGraph (Fin 8)) catlin := by
  rintro ⟨f, P, hM⟩
  set a : Fin 5 → ℕ := fun c => (univ.filter fun w : Fin 8 => (f w).1 = c).card with ha_def
  have hS : ∀ c, (S f c).card = a (c - 1) * a (c + 1) := fun c => card_product _ _
  have hsum : ∑ c, a c = 8 := by
    rw [ha_def, ← card_eq_sum_card_fiberwise (fun w _ => mem_univ ((f w).1))]
    simp
  have ha3 : ∀ c, a c ≤ 3 := fun c => le_trans (Nat.le_add_left _ _) (card_E1_add hM c)
  -- `2 |S c| ≤ ∑_{p ∈ S c} (|interior| + [meets c])`, summed over `c`
  have hlow : 2 * ∑ c, a (c - 1) * a (c + 1) ≤
      ∑ c, ∑ p ∈ S f c, (interior P ⟨c, p⟩).card + ∑ c, (E1 f P c).card := by
    rw [← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro c _
    rw [← hS, E1, card_filter, ← sum_add_distrib, card_eq_sum_ones, mul_sum]
    apply sum_le_sum
    intro p hp
    simpa using two_le c hp
  have hE1 : ∑ c, (E1 f P c).card ≤ ∑ c, min (a (c - 1) * a (c + 1)) (3 - a c) := by
    apply sum_le_sum
    intro c _
    have h1 := card_E1_add hM c
    have h2 : (E1 f P c).card ≤ a (c - 1) * a (c + 1) :=
      (hS c) ▸ card_filter_le _ _
    exact le_min h2 (Nat.le_sub_of_add_le (h1 : (E1 f P c).card + a c ≤ 3))
  have := sum_interior_le hM
  have := arith a ha3 hsum
  omega

end HajosCatlin
