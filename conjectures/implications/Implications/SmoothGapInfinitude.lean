import Implications.SmoothGapCounting

/-! A reduction of the infinitude question in Erdős #932 to gaps of
unbounded length, given the classical finiteness of shifted smooth pairs. -/

namespace Implications.SmoothGapInfinitude

open SmoothGapCounting

/-- The qualifying integers strictly inside a prime gap. -/
noncomputable def hits (r : ℕ) : Finset ℕ :=
  (Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
    (fun m => m.maxPrimeFac < primeGap r)

/-- Ordered smooth pairs with a positive difference strictly below the cutoff.
Finiteness at each cutoff is the classical shifted S-unit finiteness input. -/
def closeSmoothPairs (B : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 < p.2 ∧ p.2 - p.1 < B ∧
    p.1.maxPrimeFac < B ∧ p.2.maxPrimeFac < B}

/-- Each two-hit gap of length at most `B` supplies a distinct shifted
smooth pair for the same cutoff. -/
theorem boundedTwoHitGaps_finite (B : ℕ) (hB : (closeSmoothPairs B).Finite) :
    {r | primeGap r ≤ B ∧ 2 ≤ (hits r).card}.Finite := by
  classical
  let S : Set ℕ := {r | primeGap r ≤ B ∧ 2 ≤ (hits r).card}
  have hpairs (r : S) :
      ∃ p : ℕ × ℕ, p ∈ closeSmoothPairs B ∧ p.1 ∈ hits r.val := by
    have hcard : 1 < (hits r.val).card := r.property.2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    suffices hordered : ∀ x ∈ hits r.val, ∀ y ∈ hits r.val, x < y →
        (x, y) ∈ closeSmoothPairs B by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), hordered a ha b hb hlt, ha⟩
      · exact ⟨(b, a), hordered b hb a ha hgt, hb⟩
    intro x hx y hy hxy
    simp only [hits, Finset.mem_filter, Finset.mem_Ioo] at hx hy
    have hgap := r.property.1
    change primeAt (r.val + 1) - primeAt r.val ≤ B at hgap
    exact ⟨hxy, by omega, hx.2.trans_le r.property.1, hy.2.trans_le r.property.1⟩
  choose pair hpair hmem using hpairs
  have hinj : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    let N := max i.val j.val + 1
    have hi : i.val ∈ Finset.range N := Finset.mem_range.mpr (by dsimp [N]; omega)
    have hj : j.val ∈ Finset.range N := Finset.mem_range.mpr (by dsimp [N]; omega)
    have hdis := primeGapInteriors_pairwiseDisjoint N hi hj hne
    have hui := Finset.mem_of_mem_filter _ (hmem i)
    have huj := Finset.mem_of_mem_filter _ (hmem j)
    rw [← hij] at huj
    exact Finset.disjoint_left.mp hdis hui huj
  have hfin : (Set.univ : Set S).Finite :=
    Set.Finite.of_injOn (fun r _ => hpair r) hinj.injOn hB
  simpa using hfin.image (Subtype.val : S → ℕ)

/-- Given shifted S-unit finiteness, Erdős #932 is equivalent to finding
two-hit gaps above every prescribed gap length. -/
theorem infinitelyMany_iff_unbounded_length
    (hclose : ∀ B, (closeSmoothPairs B).Finite) :
    {r | 2 ≤ (hits r).card}.Infinite ↔
      ∀ B, ∃ r, B < primeGap r ∧ 2 ≤ (hits r).card := by
  constructor
  · intro hinf B
    by_contra! hbounded
    apply hinf
    apply (boundedTwoHitGaps_finite B (hclose B)).subset
    intro r hr
    exact ⟨le_of_not_gt (fun hlt => (not_lt_of_ge hr) (hbounded r hlt)), hr⟩
  · intro hunbounded hfinite
    obtain ⟨B, hB⟩ := (hfinite.image primeGap).bddAbove
    obtain ⟨r, hgap, hr⟩ := hunbounded B
    exact (not_le_of_gt hgap) (hB ⟨r, hr, rfl⟩)

#print axioms infinitelyMany_iff_unbounded_length
#print axioms boundedTwoHitGaps_finite

end Implications.SmoothGapInfinitude
