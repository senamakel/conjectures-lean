import Implications.SplitGraphBoundedDeletions

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

private theorem outside_anchor_card_bound
    (C S : Finset V) (inc : V → V → Prop) [DecidableRel inc] (a : V)
    (hanchor : (row S inc a).card = 4)
    (hdiff : ∀ c ∈ C, c ≠ a → (rowDiff S inc c a).card ≤ 3) :
    ∀ c ∈ C, 2 * ((row S inc c) \ row S inc a).card + 1 ≤ (row S inc c).card := by
  classical
  intro c hc
  by_cases hca : c = a
  · subst c
    simp [hanchor]
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
    have hd := hdiff c hc hca
    rw [hdiffcard] at hd
    dsimp [A, R] at *
    omega

/-- A full anchor row and row differences of at most three leave at most
one point outside the anchor in each row of size at most four. -/
theorem outside_anchor_le_one_of_rowDiff
    (C S : Finset V) (inc : V → V → Prop) [DecidableRel inc] (a : V)
    (hanchor : (row S inc a).card = 4)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hdiff : ∀ c ∈ C, c ≠ a → (rowDiff S inc c a).card ≤ 3) :
    ∀ c ∈ C, ((row S inc c) \ row S inc a).card ≤ 1 := by
  intro c hc
  have h := outside_anchor_card_bound C S inc a hanchor hdiff c hc
  have hs := hrow c hc
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
      simp [row, Finset.mem_sdiff, Finset.mem_filter, and_assoc, and_comm]
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
      have := hrow c hc
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

/-- The capacity-two flow cut loses at most two incidences, with capacity
one on each individual incidence edge. -/
theorem capacity_two_cut_of_row_constraints
    (C S : Finset V) (inc : V → V → Prop) [DecidableRel inc]
    (hdegree : ∀ x ∈ S, 3 ≤ (C.filter (fun c => inc c x)).card)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff S inc c d).card ≤ 3) :
    2 * S.card - 2 ≤ ∑ c ∈ C, min 2 (row S inc c).card := by
  classical
  let K := ∑ c ∈ C, min 2 (row S inc c).card
  let E := ∑ c ∈ C, (row S inc c).card
  change 2 * S.card - 2 ≤ K
  have hlo (T : Finset V) (hT : T ⊆ S) :
      3 * T.card ≤ ∑ c ∈ C, (row T inc c).card := by
    rw [sum_row_card_eq_sum_degree]
    calc
      _ = ∑ _x ∈ T, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun x hx => hdegree x (hT hx)
  have hE : 3 * S.card ≤ E := hlo S (fun _ hx => hx)
  have hEK : E ≤ 2 * K := by
    dsimp [E, K]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    have h := hrow c hc
    by_cases hr : (row S inc c).card ≤ 2
    · rw [min_eq_right hr]
      omega
    · rw [min_eq_left (by omega)]
      omega
  by_cases hs : S.card ≤ 5
  · exact capacity_two_cut_from_incidence _ _ _ hs hE hEK
  by_cases hfull : ∃ a ∈ C, (row S inc a).card = 4
  · obtain ⟨a, ha, hanchor⟩ := hfull
    let A := row S inc a
    let B := C.filter fun c => 2 ≤ (row S inc c).card
    have hbK : 2 * B.card ≤ K := by
      calc
        _ = ∑ c ∈ B, (2 : ℕ) := by simp [Nat.mul_comm]
        _ = ∑ c ∈ C, if 2 ≤ (row S inc c).card then 2 else 0 := by
          exact Finset.sum_filter (s := C) (fun c => 2 ≤ (row S inc c).card) (fun _ => (2 : ℕ))
        _ ≤ K := by
          apply Finset.sum_le_sum
          intro c _
          by_cases h : 2 ≤ (row S inc c).card
          · simp [h, min_eq_left h]
          · simp [h]
    have hdiffBound := outside_anchor_card_bound C S inc a hanchor
      (fun c hc hca => hdiff c hc a ha hca)
    have hOut : (∑ c ∈ C, (row (S \ A) inc c).card) ≤ B.card := by
      calc
        _ = ∑ c ∈ C, ((row S inc c) \ A).card := by
          apply Finset.sum_congr rfl
          intro c _
          congr 1
          ext x
          simp [row, A, and_assoc, and_left_comm, and_comm]
        _ ≤ ∑ c ∈ C, if 2 ≤ (row S inc c).card then (1 : ℕ) else 0 := by
          apply Finset.sum_le_sum
          intro c hc
          have hb := hdiffBound c hc
          change 2 * ((row S inc c) \ A).card + 1 ≤ (row S inc c).card at hb
          have hrc := hrow c hc
          split <;> omega
        _ = B.card := by simp [B]
    have hMass := (hlo (S \ A) Finset.sdiff_subset).trans hOut
    have hSout : S.card - 4 ≤ (S \ A).card := by
      have hcount := Finset.card_sdiff_add_card_inter S A
      have hinter := Finset.card_le_card (Finset.inter_subset_right (s := S) (t := A))
      have hA : A.card = 4 := hanchor
      omega
    have h := Nat.mul_le_mul_left 3 hSout
    omega
  · have hscaled : 2 * E ≤ 3 * K := by
      dsimp [E, K]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hc
      have h := hrow c hc
      have hne : (row S inc c).card ≠ 4 := fun heq => hfull ⟨c, hc, heq⟩
      by_cases hr : (row S inc c).card ≤ 2
      · rw [min_eq_right hr]
        omega
      · rw [min_eq_left (by omega)]
        omega
    omega

/-- The capacity bound for every independent-side cut of a split graph
with three-connectivity and induced-tree size at most five. -/
theorem split_graph_capacity_two_cut
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I S : Finset V)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hCI : Disjoint C I) (hC : G.IsClique (C : Set V))
    (hI : G.IsIndepSet (I : Set V)) (hS : S ⊆ I)
    (hcard : 4 ≤ Fintype.card V)
    (hconn : ∀ D : Finset V, D.card < 3 → (G.induce {x | x ∉ D}).Connected)
    (hTree : SplitGraphTrees.inducedTreeBound G 3) :
    2 * S.card - 2 ≤ ∑ c ∈ C, min 2 (row S G.Adj c).card := by
  have hdegree := SplitGraphBoundedDeletions.attachment_count_of_bounded_deletion_connected
    G C I 3 hI hpartition hcard hconn
  have ⟨hrows, hdiff⟩ := SplitGraphBoundedDeletions.restricted_row_bounds G C I S 3 hS hTree hC hI hCI
  apply capacity_two_cut_of_row_constraints C S G.Adj
  · intro x hx
    exact hdegree x (hS hx)
  · intro c hc
    exact hrows c hc
  · intro c hc d hd hcd
    exact hdiff c hc d hd hcd

end SplitGraphKappaThreeHall

#print axioms SplitGraphKappaThreeHall.sum_row_card_eq_sum_degree
#print axioms SplitGraphKappaThreeHall.outside_anchor_le_one_of_rowDiff
#print axioms SplitGraphKappaThreeHall.hall_deficit_one_of_single_anchor
#print axioms SplitGraphKappaThreeHall.hall_deficit_one_of_row_constraints
#print axioms SplitGraphKappaThreeHall.capacity_two_cut_from_incidence
#print axioms SplitGraphKappaThreeHall.large_set_rows_force_small
#print axioms SplitGraphKappaThreeHall.small_set_capacity_cut

#print axioms SplitGraphKappaThreeHall.capacity_two_cut_of_row_constraints
#print axioms SplitGraphKappaThreeHall.split_graph_capacity_two_cut
