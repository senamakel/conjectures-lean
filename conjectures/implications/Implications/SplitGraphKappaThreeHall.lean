import Mathlib.Tactic

/-!
Small arithmetic cuts arising in the connectivity-three split-graph case.

The graph-to-cut reductions are recorded separately: a three-incidence bound
and a capacity-two bound imply the stated cut inequality; in the large-set
case, the count of rows meeting the selected set at least twice cannot be
simultaneously large enough to cover the outside-anchor incidences and small
enough for a deficient capacity cut.
-/

namespace SplitGraphKappaThreeHall

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The incidence row, restricted to a selected set of left vertices. -/
def row (S : Finset V) (inc : V → V → Prop) (c : V)
    [DecidableRel inc] : Finset V := S.filter (fun x => inc c x)

/-- Symmetric difference between two rows. -/
def rowDiff (S : Finset V) (inc : V → V → Prop) (c d : V)
    [DecidableRel inc] : Finset V :=
  row S inc c \ row S inc d ∪ row S inc d \ row S inc c

/-- A full anchor row and pairwise symmetric difference at most three force
every row to have at most one element outside the anchor. -/
theorem outside_anchor_le_one_of_rowDiff
    (C S : Finset V) (inc : V → V → Prop) [DecidableRel inc] (a : V)
    (hanchor : (row S inc a).card = 4)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hdiff : ∀ c ∈ C, c ≠ a → (rowDiff S inc c a).card ≤ 3) :
    ∀ c ∈ C, ((row S inc c) \ row S inc a).card ≤ 1 := by
  classical
  intro c hc
  by_cases hca : c = a
  · subst c
    simp
  · let R := row S inc c
    let A := row S inc a
    have hdisj : Disjoint (A \ R) (R \ A) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_sdiff.mp hx₂).1
    have hdiffcard : (rowDiff S inc c a).card =
        (A \ R).card + (R \ A).card := by
      rw [rowDiff]
      rw [Finset.union_comm]
      simpa [A, R] using Finset.card_union_of_disjoint hdisj
    have hAc : A.card = (A \ R).card + (A ∩ R).card := by
      have := Finset.card_sdiff_add_card_inter A R
      omega
    have hRc : R.card = (A ∩ R).card + (R \ A).card := by
      have := Finset.card_sdiff_add_card_inter R A
      rw [Finset.inter_comm] at this
      omega
    have hAcard : A.card = 4 := hanchor
    have hRcard : R.card ≤ 4 := hrow c hc
    have hd := hdiff c hc hca
    rw [hdiffcard] at hd
    dsimp [A, R] at *
    omega

/-- The split-graph row constraints imply the Hall deficit-one condition.
Either no row is full, in which case ordinary incidence counting suffices, or
a full row is an anchor and all other rows have at most one entry outside it. -/
theorem hall_deficit_one_of_row_constraints
    (C S : Finset V) (inc : V → V → Prop) [DecidableRel inc]
    (hdegree : ∀ x ∈ S, 3 ≤ (C.filter (fun c => inc c x)).card)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff S inc c d).card ≤ 3) :
    S.card ≤ C.card + 1 := by
  classical
  by_cases hfull : ∃ a ∈ C, (row S inc a).card = 4
  · obtain ⟨a, ha, hanchor⟩ := hfull
    apply hall_deficit_one_of_single_anchor C S inc (row S inc a)
    · exact hdegree
    · exact hrow
    · simpa using hanchor
    · exact outside_anchor_le_one_of_rowDiff C S inc a hanchor hrow
        (fun c hc hca => hdiff c hc a ha hca)
  · have hrow3 : ∀ c ∈ C, (row S inc c).card ≤ 3 := by
      intro c hc
      have hne : (row S inc c).card ≠ 4 := by
        intro heq
        exact hfull ⟨c, hc, heq⟩
      omega
    have hlow : 3 * S.card ≤ ∑ c ∈ C, (row S inc c).card := by
      calc
        3 * S.card = ∑ x ∈ S, 3 := by simp; ring
        _ ≤ ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
          apply Finset.sum_le_sum
          intro x hx
          exact hdegree x hx
        _ = ∑ c ∈ C, (row S inc c).card :=
          (sum_row_card_eq_sum_degree C S inc).symm
    have hupp : (∑ c ∈ C, (row S inc c).card) ≤ 3 * C.card := by
      calc
        _ ≤ ∑ c ∈ C, (3 : ℕ) := by
          apply Finset.sum_le_sum
          intro c hc
          exact hrow3 c hc
        _ = _ := by simp; ring
    omega

/-- Count incidences by rows or by left vertices. -/
theorem sum_row_card_eq_sum_degree (C S : Finset V) (inc : V → V → Prop)
    [DecidableRel inc] :
    (∑ c ∈ C, (row S inc c).card) =
      ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
  classical
  calc
    (∑ c ∈ C, (row S inc c).card) =
        ∑ c ∈ C, ∑ x ∈ S, (if inc c x then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rfl
          intro c hc
          calc
            (row S inc c).card = ∑ x ∈ row S inc c, (1 : ℕ) := by simp
            _ = ∑ x ∈ S, if inc c x then 1 else 0 := by
              change (∑ x ∈ S.filter (fun x => inc c x), (1 : ℕ)) = _
              exact Finset.sum_filter (s := S) (fun x => inc c x) (fun _ => (1 : ℕ))
    _ = ∑ x ∈ S, ∑ c ∈ C, (if inc c x then (1 : ℕ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            ∑ c ∈ C, (if inc c x then (1 : ℕ) else 0) =
                ∑ c ∈ C.filter (fun c => inc c x), (1 : ℕ) := by
                  exact (Finset.sum_filter (s := C) (fun c => inc c x)
                    (fun _ => (1 : ℕ))).symm
            _ = _ := by simp

/-- If every left vertex has three incidences, every row has size at most
four, and one four-element anchor leaves at most one incidence outside it in
each row, then every selected set has at most one more vertex than rows. -/
theorem hall_deficit_one_of_single_anchor
    (C S : Finset V) (inc : V → V → Prop) [DecidableRel inc] (A : Finset V)
    (hdegree : ∀ x ∈ S, 3 ≤ (C.filter (fun c => inc c x)).card)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hanchor : A.card = 4)
    (houtside : ∀ c ∈ C, ((row S inc c) \ A).card ≤ 1) :
    S.card ≤ C.card + 1 := by
  classical
  by_contra hnot
  have hlarge : C.card + 2 ≤ S.card := by omega
  have htotalLow : 3 * S.card ≤ ∑ c ∈ C, (row S inc c).card := by
    calc
      3 * S.card = ∑ x ∈ S, 3 := by simp; ring
      _ ≤ ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hdegree x hx
      _ = ∑ c ∈ C, (row S inc c).card :=
        (sum_row_card_eq_sum_degree C S inc).symm
  have htotalHigh : (∑ c ∈ C, (row S inc c).card) ≤ 4 * C.card := by
    calc
      _ ≤ ∑ c ∈ C, (4 : ℕ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hrow c hc
      _ = _ := by simp; ring
  have hC : 6 ≤ C.card := by omega
  have houtsideCount :
      (∑ c ∈ C, ((row S inc c) \ A).card) ≤ C.card := by
    calc
      _ ≤ ∑ c ∈ C, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact houtside c hc
      _ = _ := by simp
  have hdouble :
      (∑ c ∈ C, ((row S inc c) \ A).card) =
        ∑ x ∈ S \ A, (C.filter (fun c => inc c x)).card := by
    have hrowEq (c : V) : row (S \ A) inc c = row S inc c \ A := by
      ext x
      simp [row, Finset.mem_sdiff, Finset.mem_filter, and_assoc, and_left_comm,
        and_comm]
    calc
      _ = ∑ c ∈ C, (row (S \ A) inc c).card := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [hrowEq]
      _ = _ := sum_row_card_eq_sum_degree C (S \ A) inc
  have houtsideLow :
      3 * (S \ A).card ≤ ∑ x ∈ S \ A, (C.filter (fun c => inc c x)).card := by
    calc
      3 * (S \ A).card = ∑ x ∈ S \ A, 3 := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        exact hdegree x ((Finset.mem_sdiff.mp hx).1)
  have hSA : C.card - 2 ≤ (S \ A).card := by
    have hdecomp : S.card = (S \ A).card + (S ∩ A).card := by
      have := Finset.card_sdiff_add_card_inter S A
      omega
    have hint : (S ∩ A).card ≤ 4 := by
      exact (Finset.card_le_card Finset.inter_subset_right).trans_eq hanchor
    omega
  rw [← hdouble] at houtsideLow
  omega

/-- For a set of at most five vertices, three incidences per left vertex and
a capacity-two upper bound imply the deficit-one cut inequality. -/
theorem capacity_two_cut_from_incidence (s incidences capacity : ℕ)
    (hsmall : s ≤ 5)
    (hdegree : 3 * s ≤ incidences)
    (hcapacity : incidences ≤ 2 * capacity) :
    2 * s - 2 ≤ capacity := by
  omega

/-- If at least three incidences per vertex outside a four-element anchor
require `b` rows, then a capacity cut below `2s-2` forces `s ≤ 5`. -/
theorem large_set_rows_force_small (s b : ℕ)
    (houtside : 3 * (s - 4) ≤ b)
    (hcut : 2 * b ≤ 2 * s - 3) :
    s ≤ 5 := by
  omega

/-- On sets of size at most five, the ordinary three-incidence count already
forces the capacity cut to be at least `2s-2`. -/
theorem small_set_capacity_cut (s incidences capacity : ℕ)
    (hsmall : s ≤ 5)
    (hdegree : 3 * s ≤ incidences)
    (hcapacity : incidences ≤ 2 * capacity) :
    2 * s - 2 ≤ capacity := by
  exact capacity_two_cut_from_incidence s incidences capacity hsmall hdegree hcapacity

end SplitGraphKappaThreeHall

#print axioms SplitGraphKappaThreeHall.sum_row_card_eq_sum_degree
#print axioms SplitGraphKappaThreeHall.hall_deficit_one_of_single_anchor
#print axioms SplitGraphKappaThreeHall.capacity_two_cut_from_incidence
#print axioms SplitGraphKappaThreeHall.large_set_rows_force_small
#print axioms SplitGraphKappaThreeHall.small_set_capacity_cut
