import Implications.WilfPatternSwap

/-!
# Reversal preserves exact consecutive Wilf counts

Reversing an ambient permutation and its length-eight pattern reflects the
occurrence starts. We prove the exact-count transfer for every pattern and
every prescribed exact set of starts.
-/

namespace Implications.WilfReversal

open Implications.WilfPatternSwap WilfMarked

/-- Reverse the positions of a length-eight pattern. -/
def reversePattern (p : Fin 8 → Fin 8) : Fin 8 → Fin 8 := p ∘ Fin.revPerm

/-- Reflect valid length-eight starts, fixing the invalid tail of `Fin n`. -/
def reverseStartFun {n : ℕ} (s : Fin n) : Fin n :=
  if hs : s.val + 7 < n then ⟨n - 8 - s.val, by omega⟩ else s

private theorem reverseStartFun_involutive {n : ℕ} :
    Function.Involutive (@reverseStartFun n) := by
  intro s
  by_cases hs : s.val + 7 < n
  · have hr : n - 8 - s.val + 7 < n := by omega
    apply Fin.ext
    simp only [reverseStartFun, dif_pos hs, dif_pos hr]
    change n - 8 - (n - 8 - s.val) = s.val
    omega
  · simp [reverseStartFun, hs]

/-- The start-index involution on all of `Fin n`. -/
noncomputable def reverseStartEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := reverseStartFun
  invFun := reverseStartFun
  left_inv := reverseStartFun_involutive
  right_inv := reverseStartFun_involutive

/-- Reverse an ambient permutation by precomposing with `Fin.revPerm`. -/
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

private theorem reverseIndex_eq {n : ℕ} (s : ℕ) (hs : s + 7 < n)
    (i : Fin 8) :
    Fin.revPerm ⟨s + (Fin.rev i).val, by have hi := (Fin.rev i).isLt; omega⟩ =
      ⟨n - 8 - s + i.val, by have hi := i.isLt; omega⟩ := by
  apply Fin.ext
  simp [Fin.revPerm_apply, Fin.rev]
  omega

/-- A reversed permutation contains the reversed pattern at the reflected
start exactly when the original permutation contains the original pattern. -/
private theorem containsAt_reverse_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8) (s : Fin n) (hs : s.val + 7 < n) :
    ContainsAt (Fin.revPerm.trans π) s.val (reversePattern p) ↔
      ContainsAt π (n - 8 - s.val) p := by
  have hr : n - 8 - s.val + 7 < n := by omega
  constructor
  · rintro ⟨_, hrev⟩
    refine ⟨hr, ?_⟩
    intro i j
    have h := hrev (Fin.rev i) (Fin.rev j)
    have hi := reverseIndex_eq s.val hs i
    have hj := reverseIndex_eq s.val hs j
    change (π (Fin.revPerm ⟨s.val + (Fin.rev i).val, by
        have hk := (Fin.rev i).isLt
        omega⟩) <
      π (Fin.revPerm ⟨s.val + (Fin.rev j).val, by
        have hk := (Fin.rev j).isLt
        omega⟩)) ↔
      reversePattern p (Fin.rev i) < reversePattern p (Fin.rev j) at h
    rw [hi, hj] at h
    simpa [reversePattern, Fin.revPerm_apply] using h
  · rintro ⟨_, h⟩
    refine ⟨hs, ?_⟩
    intro i j
    have h' := h (Fin.rev i) (Fin.rev j)
    have hi := reverseIndex_eq s.val hs i
    have hj := reverseIndex_eq s.val hs j
    have hcmp : (π (Fin.revPerm ⟨s.val + i.val, by
        have hk := i.isLt
        omega⟩) <
      π (Fin.revPerm ⟨s.val + j.val, by
        have hk := j.isLt
        omega⟩)) ↔ p (Fin.rev i) < p (Fin.rev j) := by
      simpa [hi, hj, Fin.rev, Fin.revPerm_apply] using h'
    simpa [reversePattern, Fin.revPerm_apply] using hcmp

/-- Reversal maps the exact occurrence-start set to its reflected image. -/
theorem occurrenceSet_reverse {n : ℕ} (p : Fin 8 → Fin 8)
    (π : Equiv.Perm (Fin n)) :
    occurrenceSet (reversePattern p) (reversePermEquiv n π) =
      (occurrenceSet p π).map (reverseStartEquiv n).toEmbedding := by
  classical
  ext s
  constructor
  · intro hs
    have hc := (Finset.mem_filter.mp hs).2
    have hv := hc.1
    have hsource := (containsAt_reverse_iff π p s hv).mp hc
    refine Finset.mem_map.mpr ⟨reverseStartEquiv n s, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    · exact reverseStartFun_involutive s
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨t, ht, hts⟩
    have hc := (Finset.mem_filter.mp ht).2
    have hvt := hc.1
    have hts' := congrArg (reverseStartEquiv n) hts
    have hts'' : reverseStartEquiv n s = t := by
      simpa [reverseStartFun_involutive] using hts'.symm
    have hvs : s.val + 7 < n := by
      by_contra hbad
      have hfix : reverseStartEquiv n s = s := by
        simp [reverseStartEquiv, reverseStartFun, hbad]
      rw [hfix] at hts''
      have := congrArg Fin.val hts''
      omega
    have hsource : ContainsAt (Fin.revPerm.trans π) s.val (reversePattern p) := by
      apply (containsAt_reverse_iff π p s hvs).mpr
      simpa [hts'', reverseStartEquiv, reverseStartFun, hvt] using hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩

private theorem exactCount_eq_of_equiv_occurrenceSets {α β X Y : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype X] [Fintype Y]
    (occX : X → Finset α) (occY : Y → Finset β)
    (eX : X ≃ Y) (eα : α ≃ β)
    (h : ∀ x, occY (eX x) = (occX x).map eα.toEmbedding)
    (marks : Finset α) :
    WilfCounts.exactCount occX marks =
      WilfCounts.exactCount occY (marks.map eα.toEmbedding) := by
  classical
  unfold WilfCounts.exactCount
  have card_eq :
      Fintype.card {x : X // occX x = marks} =
        Fintype.card {y : Y // occY y = marks.map eα.toEmbedding} :=
    Fintype.card_congr {
      toFun := fun x => ⟨eX x.1, by rw [h, x.2]⟩
      invFun := fun y => ⟨eX.symm y.1, by
        apply Finset.map_injective eα.toEmbedding
        simpa using (h (eX.symm y.1)).symm.trans y.2⟩
      left_inv := by intro x; cases x; simp
      right_inv := by intro y; cases y; simp
    }
  have hx : Fintype.card {x : X // occX x = marks} =
      (Finset.univ.filter fun x : X => occX x = marks).card :=
    Fintype.card_of_subtype _ (by intro x; simp)
  have hy : Fintype.card {y : Y // occY y = marks.map eα.toEmbedding} =
      (Finset.univ.filter fun y : Y => occY y = marks.map eα.toEmbedding).card :=
    Fintype.card_of_subtype _ (by intro y; simp)
  rw [← hx, card_eq, hy]

/-- Exact consecutive Wilf counts are preserved by simultaneous reversal of the
pattern and the prescribed starts. -/
theorem exactOccurrenceCount_eq_reverse (n : ℕ) (p : Fin 8 → Fin 8)
    (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern p))
        (marks.map (reverseStartEquiv n).toEmbedding) := by
  apply exactCount_eq_of_equiv_occurrenceSets
    (occurrenceSet p) (occurrenceSet (reversePattern p))
    (reversePermEquiv n) (reverseStartEquiv n)
  · exact occurrenceSet_reverse p
  · exact marks

end Implications.WilfReversal
