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
noncomputable def row (S : Finset V) (inc : V → V → Prop) (c : V) : Finset V := by
  classical
  exact S.filter (fun x => inc c x)

/-- Count incidences by rows or by left vertices. -/
theorem sum_row_card_eq_sum_degree (C S : Finset V) (inc : V → V → Prop)
    [DecidableRel inc] :
    (∑ c ∈ C, (row S inc c).card) =
      ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
  classical
  calc
    (∑ c ∈ C, (row S inc c).card) =
        ∑ c ∈ C, ∑ x ∈ S, if inc c x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          calc
            (row S inc c).card = ∑ x ∈ row S inc c, (1 : ℕ) := by simp
            _ = ∑ x ∈ S, if inc c x then 1 else 0 := by
              simp only [row]
              rw [Finset.sum_filter]
    _ = ∑ x ∈ S, ∑ c ∈ C, if inc c x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            ∑ c ∈ C, if inc c x then 1 else 0 =
                ∑ c ∈ C.filter (fun c => inc c x), (1 : ℕ) := by
                  rw [Finset.sum_filter]
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

#print axioms SplitGraphKappaThreeHall.capacity_two_cut_from_incidence
#print axioms SplitGraphKappaThreeHall.large_set_rows_force_small
#print axioms SplitGraphKappaThreeHall.small_set_capacity_cut
