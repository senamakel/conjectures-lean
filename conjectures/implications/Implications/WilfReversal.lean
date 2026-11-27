import Implications.WilfPatternSwap

/-!
# Reversal preserves exact consecutive Wilf counts

Reversing a permutation and its length-eight pattern reflects occurrence starts
about the midpoint of the interval. This gives equality of exact occurrence
counts after applying the same reflection to the prescribed starts.
-/

namespace Implications.WilfReversal

open Implications.WilfPatternSwap

/-- Reversal of the eight positions of a pattern. -/
def reversePattern (p : Fin 8 → Fin 8) : Fin 8 → Fin 8 :=
  p ∘ Fin.revPerm

/-- Reflect a valid length-eight start, and leave invalid start indices fixed. -/
def reverseStartFun {n : ℕ} (s : Fin n) : Fin n :=
  if hs : s.val + 7 < n then ⟨n - 8 - s.val, by omega⟩ else s

private theorem reverseStartFun_involutive {n : ℕ} :
    Function.Involutive (@reverseStartFun n) := by
  intro s
  by_cases hs : s.val + 7 < n
  · simp only [reverseStartFun, dif_pos hs]
    have hreflect : n - 8 - s.val + 7 < n := by omega
    simp only [dif_pos hreflect]
    apply Fin.ext
    omega
  · simp only [reverseStartFun, dif_neg hs]

/-- The involution on all start indices, including the unused tail of `Fin n`. -/
noncomputable def reverseStartEquiv (n : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofInvolutive reverseStartFun reverseStartFun_involutive

/-- Reversal of an ambient permutation. -/
noncomputable def reversePermEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun π := Fin.revPerm.trans π
  invFun π := Fin.revPerm.trans π
  left_inv π := by
    ext i
    simp
  right_inv π := by
    ext i
    simp

private theorem containsAt_reverse_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8) (s : Fin n) (hs : s.val + 7 < n) :
    ContainsAt (Fin.revPerm.trans π) s.val (reversePattern p) ↔
      ContainsAt π (n - 8 - s.val) p := by
  constructor
  · rintro ⟨_, h⟩
    refine ⟨by omega, ?_⟩
    intro i j
    have hi : s.val + i.val < n := by omega
    have hj : s.val + j.val < n := by omega
    have hi' : n - 1 - (s.val + i.val) = n - 8 - s.val + (7 - i.val) := by omega
    have hj' : n - 1 - (s.val + j.val) = n - 8 - s.val + (7 - j.val) := by omega
    have hrev_i : Fin.revPerm ⟨s.val + i.val, hi⟩ =
        ⟨n - 1 - (s.val + i.val), by omega⟩ := by
      apply Fin.ext
      simp [Fin.revPerm_apply]
    have hrev_j : Fin.revPerm ⟨s.val + j.val, hj⟩ =
        ⟨n - 1 - (s.val + j.val), by omega⟩ := by
      apply Fin.ext
      simp [Fin.revPerm_apply]
    have hcmp := h i j
    change (π (Fin.revPerm ⟨s.val + i.val, hi⟩) <
        π (Fin.revPerm ⟨s.val + j.val, hj⟩)) ↔
      reversePattern p i < reversePattern p j at hcmp
    rw [hrev_i, hrev_j, hi', hj'] at hcmp
    simpa [reversePattern, Fin.revPerm_apply] using hcmp
  · rintro ⟨_, h⟩
    refine ⟨hs, ?_⟩
    intro i j
    have hi : s.val + i.val < n := by omega
    have hj : s.val + j.val < n := by omega
    have hi' : n - 1 - (s.val + i.val) = n - 8 - s.val + (7 - i.val) := by omega
    have hj' : n - 1 - (s.val + j.val) = n - 8 - s.val + (7 - j.val) := by omega
    have hrev_i : Fin.revPerm ⟨s.val + i.val, hi⟩ =
        ⟨n - 1 - (s.val + i.val), by omega⟩ := by
      apply Fin.ext
      simp [Fin.revPerm_apply]
    have hrev_j : Fin.revPerm ⟨s.val + j.val, hj⟩ =
        ⟨n - 1 - (s.val + j.val), by omega⟩ := by
      apply Fin.ext
      simp [Fin.revPerm_apply]
    have hcmp := h i j
    change (π ⟨n - 8 - s.val + i.val, by omega⟩ <
        π ⟨n - 8 - s.val + j.val, by omega⟩) ↔ p i < p j at hcmp
    have hcmp' : (π (Fin.revPerm ⟨s.val + i.val, hi⟩) <
        π (Fin.revPerm ⟨s.val + j.val, hj⟩)) ↔ p (Fin.revPerm i) < p (Fin.revPerm j) := by
      simpa [hrev_i, hrev_j, hi', hj', Fin.revPerm_apply] using hcmp
    simpa [reversePattern, Fin.revPerm_apply] using hcmp'

/-- Reversal carries the exact occurrence-start set to its reflected image. -/
theorem occurrenceSet_reverse {n : ℕ} (p : Fin 8 → Fin 8)
    (π : Equiv.Perm (Fin n)) :
    occurrenceSet (reversePattern p) (reversePermEquiv n π) =
      (occurrenceSet p π).map (reverseStartEquiv n).toEmbedding := by
  classical
  ext s
  constructor
  · intro hs
    have hcontains := (Finset.mem_filter.mp hs).2
    have hvalid : s.val + 7 < n := hcontains.1
    have hsource := (containsAt_reverse_iff π p s hvalid).mp hcontains
    refine Finset.mem_map.mpr ⟨(reverseStartEquiv n) s, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    · simp [reverseStartEquiv, reverseStartFun, hvalid]
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨t, ht, hts⟩
    have hcontains := (Finset.mem_filter.mp ht).2
    have hvalid : t.val + 7 < n := hcontains.1
    have hst : (reverseStartEquiv n) t = s := hts
    have hreflected : s.val + 7 < n := by
      have := hvalid
      simp [reverseStartEquiv, reverseStartFun, hvalid] at hst
      apply Fin.ext at hst
      omega
    have hsource := (containsAt_reverse_iff π p s hreflected).mpr ?_
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    · simpa [reversePermEquiv, hst, reverseStartEquiv, reverseStartFun, hvalid] using hcontains

private theorem exactCount_eq_of_equiv_occurrenceSets {α X Y : Type*}
    [Fintype α] [DecidableEq α] [Fintype X] [Fintype Y]
    (occX : X → Finset α) (occY : Y → Finset α) (e : X ≃ Y)
    (h : ∀ x, occY (e x) = occX x)
    (marks : Finset α) :
    WilfCounts.exactCount occX marks = WilfCounts.exactCount occY marks := by
  classical
  unfold WilfCounts.exactCount
  have card_eq :
      Fintype.card {x : X // occX x = marks} =
        Fintype.card {y : Y // occY y = marks} :=
    Fintype.card_congr {
      toFun := fun x => ⟨e x.1, by rw [← h]; exact x.2⟩
      invFun := fun y => ⟨e.symm y.1, by rw [h]; simpa using y.2⟩
      left_inv := by intro x; cases x; simp
      right_inv := by intro y; cases y; simp
    }
  have hx : Fintype.card {x : X // occX x = marks} =
      (Finset.univ.filter fun x : X => occX x = marks).card :=
    Fintype.card_of_subtype _ (by intro x; simp)
  have hy : Fintype.card {y : Y // occY y = marks} =
      (Finset.univ.filter fun y : Y => occY y = marks).card :=
    Fintype.card_of_subtype _ (by intro y; simp)
  rw [← hx, card_eq, hy]

/-- Every exact occurrence set has the same count after reversing both the
pattern and the prescribed set of starts. -/
theorem exactOccurrenceCount_eq_reverse (n : ℕ) (p : Fin 8 → Fin 8)
    (π : Equiv.Perm (Fin n)) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern p))
        ((marks.map (reverseStartEquiv n).toEmbedding)) := by
  classical
  apply exactCount_eq_of_equiv_occurrenceSets
    (occurrenceSet p) (occurrenceSet (reversePattern p))
    (reversePermEquiv n)
  · intro σ
    rw [occurrenceSet_reverse]
  · exact marks

end Implications.WilfReversal
