import Mathlib

/-!
# Marked-window bijection for the patterns 16237485 and 16247385

The input is a permutation of an arbitrary finite interval, together with a set of
marked starting positions.  `ContainsAt` records classical pattern containment by
preservation of all pairwise comparisons in the window.
-/

namespace WilfMarked

/-- The two length-eight patterns, encoded by their ranks. -/
def sigma : Fin 8 → Fin 8 := ![0, 5, 1, 2, 6, 3, 7, 4]
def tau : Fin 8 → Fin 8 := ![0, 5, 1, 3, 6, 2, 7, 4]

def rankList (p : Fin 8 → Fin 8) : List Nat := List.ofFn fun i => (p i).val

theorem rankList_get (p : Fin 8 → Fin 8) (i : Fin 8) :
    (rankList p)[i.val]! = (p i).val := by
  unfold rankList
  rw [getElem!_pos _ _ (by simp)]
  rw [List.getElem_ofFn (by simp)]

/-- The shared suffix/prefix of two windows has to have the same relative order. -/
def overlapCompatible (p : Fin 8 → Fin 8) (shift : Nat) : Bool :=
  (List.range (8 - shift)).all fun i =>
    (List.range (8 - shift)).all fun j =>
      decide (((rankList p)[shift + i]! < (rankList p)[shift + j]!) ↔
              ((rankList p)[i]! < (rankList p)[j]!))

theorem sigma_overlap_compatible_only_at_5_or_7 (shift : Nat)
    (hpos : 1 ≤ shift) (hsmall : shift < 8)
    (hok : overlapCompatible sigma shift = true) : shift = 5 ∨ shift = 7 := by
  interval_cases shift
  · have hf : overlapCompatible sigma 1 = false := by decide
    rw [hf] at hok
    contradiction
  · have hf : overlapCompatible sigma 2 = false := by decide
    rw [hf] at hok
    contradiction
  · have hf : overlapCompatible sigma 3 = false := by decide
    rw [hf] at hok
    contradiction
  · have hf : overlapCompatible sigma 4 = false := by decide
    rw [hf] at hok
    contradiction
  · exact Or.inl rfl
  · have hf : overlapCompatible sigma 6 = false := by decide
    rw [hf] at hok
    contradiction
  · exact Or.inr rfl

theorem tau_overlap_compatible_only_at_5_or_7 (shift : Nat)
    (hpos : 1 ≤ shift) (hsmall : shift < 8)
    (hok : overlapCompatible tau shift = true) : shift = 5 ∨ shift = 7 := by
  interval_cases shift
  · have hf : overlapCompatible tau 1 = false := by decide
    rw [hf] at hok
    contradiction
  · have hf : overlapCompatible tau 2 = false := by decide
    rw [hf] at hok
    contradiction
  · have hf : overlapCompatible tau 3 = false := by decide
    rw [hf] at hok
    contradiction
  · have hf : overlapCompatible tau 4 = false := by decide
    rw [hf] at hok
    contradiction
  · exact Or.inl rfl
  · have hf : overlapCompatible tau 6 = false := by decide
    rw [hf] at hok
    contradiction
  · exact Or.inr rfl

/-- The adjacent transposition of the fourth and sixth positions. -/
def windowSwap (i : Fin 8) : Fin 8 :=
  if i = 3 then 5 else if i = 5 then 3 else i

theorem windowSwap_involutive : Function.Involutive windowSwap := by
  intro i
  fin_cases i <;> rfl

theorem windowSwap_sigma : sigma ∘ windowSwap = tau := by
  funext i
  fin_cases i <;> rfl

theorem windowSwap_tau : tau ∘ windowSwap = sigma := by
  funext i
  fin_cases i <;> rfl

/-- A window at `s` is the indicated pattern when its values have the same
strict-order comparisons as the pattern. The bound is expressed on the final
index, so this works for any finite ambient permutation. -/
def ContainsAt {n : Nat} (π : Equiv.Perm (Fin n)) (s : Nat)
    (p : Fin 8 → Fin 8) : Prop :=
  ∃ h : s + 7 < n, ∀ i j : Fin 8,
    (π ⟨s + i.val, by
      have hi : i.val ≤ 7 := Nat.le_of_lt_succ i.isLt
      omega⟩ < π ⟨s + j.val, by
      have hj : j.val ≤ 7 := Nat.le_of_lt_succ j.isLt
      omega⟩) ↔ p i < p j

/-- The common part of two same-pattern windows must itself have the same
relative order when read from either window. -/
theorem same_pattern_overlap_compatible {n : Nat} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8) (s t : Nat) (hs : ContainsAt π s p) (ht : ContainsAt π t p)
    (hst : s < t) (hts : t - s < 8) :
    overlapCompatible p (t - s) = true := by
  rcases hs with ⟨hbs, hs⟩
  rcases ht with ⟨hbt, ht⟩
  apply of_decide_eq_true
  simp only [overlapCompatible, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi j hj
  let ai : Fin 8 := ⟨i, by omega⟩
  let aj : Fin 8 := ⟨j, by omega⟩
  let bi : Fin 8 := ⟨(t - s) + i, by omega⟩
  let bj : Fin 8 := ⟨(t - s) + j, by omega⟩
  have hsi := hs bi bj
  have htj := ht ai aj
  have hidxi : (⟨s + bi.val, by
      have hb : bi.val ≤ 7 := Nat.le_of_lt_succ bi.isLt
      omega⟩ : Fin n) = ⟨t + ai.val, by
      have ha : ai.val ≤ 7 := Nat.le_of_lt_succ ai.isLt
      omega⟩ := by
    apply Fin.ext
    simp [ai, bi]
    omega
  have hidxj : (⟨s + bj.val, by
      have hb : bj.val ≤ 7 := Nat.le_of_lt_succ bj.isLt
      omega⟩ : Fin n) = ⟨t + aj.val, by
      have ha : aj.val ≤ 7 := Nat.le_of_lt_succ aj.isLt
      omega⟩ := by
    apply Fin.ext
    simp [aj, bj]
    omega
  have hsame :
      (π ⟨s + bi.val, by
        have hb : bi.val ≤ 7 := Nat.le_of_lt_succ bi.isLt
        omega⟩ < π ⟨s + bj.val, by
        have hb : bj.val ≤ 7 := Nat.le_of_lt_succ bj.isLt
        omega⟩) ↔
      (π ⟨t + ai.val, by
        have ha : ai.val ≤ 7 := Nat.le_of_lt_succ ai.isLt
        omega⟩ < π ⟨t + aj.val, by
        have ha : aj.val ≤ 7 := Nat.le_of_lt_succ aj.isLt
        omega⟩) := by
    rw [hidxi, hidxj]
  have hrel : (p bi < p bj) ↔ (p ai < p aj) :=
    hsi.symm.trans (hsame.trans htj)
  have hbi := rankList_get p bi
  have hbj := rankList_get p bj
  have hai := rankList_get p ai
  have haj := rankList_get p aj
  simpa [ai, aj, bi, bj, hbi, hbj, hai, haj] using hrel

theorem same_pattern_start_distance {n : Nat} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8) (hp : p = sigma ∨ p = tau)
    (s t : Nat) (hs : ContainsAt π s p) (ht : ContainsAt π t p)
    (hst : s < t) (hts : t - s < 8) : t - s = 5 ∨ t - s = 7 := by
  have hov := same_pattern_overlap_compatible π p s t hs ht hst hts
  let d := t - s
  rcases hp with rfl | rfl
  · have h := sigma_overlap_compatible_only_at_5_or_7 d (by omega) hts (by simpa [d] using hov)
    simpa [d] using h
  · have h := tau_overlap_compatible_only_at_5_or_7 d (by omega) hts (by simpa [d] using hov)
    simpa [d] using h

theorem same_pattern_starts_separated {n : Nat} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8) (hp : p = sigma ∨ p = tau)
    (s t : Nat) (hs : ContainsAt π s p) (ht : ContainsAt π t p)
    (hst : s < t) : 5 ≤ t - s := by
  by_cases hsmall : t - s < 8
  · rcases same_pattern_start_distance π p hp s t hs ht hst hsmall with h | h <;> omega
  · omega

end WilfMarked

namespace WilfMarked

#print axioms windowSwap_involutive
#print axioms windowSwap_sigma
#print axioms windowSwap_tau
#print axioms sigma_overlap_compatible_only_at_5_or_7
#print axioms tau_overlap_compatible_only_at_5_or_7
#print axioms same_pattern_overlap_compatible
#print axioms same_pattern_start_distance
#print axioms same_pattern_starts_separated

end WilfMarked
