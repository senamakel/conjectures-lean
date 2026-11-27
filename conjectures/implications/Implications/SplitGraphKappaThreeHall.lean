import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Omega

/-!
Hall-type bookkeeping for the connectivity-three split-graph case of WOWII 199.

The main theorem isolates the finite set-system obligation. Each left vertex
has incidence degree at least three; right rows have size at most four and
pairwise symmetric difference at most three. If the full rows have either a
common triple or lie in a five-element set, then every left subset has at most
one more element than its row-neighborhood. This is the Hall condition needed
for a two-incidence path-cover approach.
-/

namespace SplitGraphKappaThreeHall

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The incidence row of `c`, restricted to a selected left-side set. -/
def row (S : Finset V) (inc : V → V → Prop) (c : V) : Finset V :=
  S.filter (fun x => inc c x)

/-- The symmetric difference of two incidence rows. -/
def rowDiff (S : Finset V) (inc : V → V → Prop) (c d : V) : Finset V :=
  row S inc c \ row S inc d ∪ row S inc d \ row S inc c

/-- Count incidences by rows or by left vertices. -/
theorem sum_row_card_eq_sum_degree (C S : Finset V) (inc : V → V → Prop) :
    (∑ c ∈ C, (row S inc c).card) =
      ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
  classical
  calc
    (∑ c ∈ C, (row S inc c).card) =
        ∑ c ∈ C, ∑ x ∈ S, if inc c x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          simp [row, Finset.card_filter]
    _ = ∑ x ∈ S, ∑ c ∈ C, if inc c x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.card_filter]

/-- If all four-element rows contain one fixed triple, the row-count bound
gives the Hall deficit-one inequality, provided each smaller row has at most
two entries outside that triple. -/
theorem hall_deficit_one_of_common_triple
    (C S : Finset V) (inc : V → V → Prop) (T : Finset V)
    (hT : T.card = 3)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff S inc c d).card ≤ 3)
    (hdegree : ∀ x ∈ S, 3 ≤ (C.filter (fun c => inc c x)).card)
    (hcore : ∀ c ∈ C, (row S inc c).card = 4 → T ⊆ row S inc c)
    (hsmall : ∀ c ∈ C, (row S inc c).card ≤ 3 →
      ((row S inc c) \ T).card ≤ 2) :
    S.card ≤ C.card + 1 := by
  classical
  let F := C.filter (fun c => (row S inc c).card = 4)
  let f := F.card
  let m := C.card
  have hsum : 3 * S.card ≤ ∑ c ∈ C, (row S inc c).card := by
    calc
      3 * S.card = ∑ x ∈ S, 3 := by simp
      _ ≤ ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hdegree x hx
      _ = ∑ c ∈ C, (row S inc c).card :=
        (sum_row_card_eq_sum_degree C S inc).symm
  have hupper : (∑ c ∈ C, (row S inc c).card) ≤ 3 * m + f := by
    calc
      (∑ c ∈ C, (row S inc c).card) ≤
          ∑ c ∈ C, (3 + if c ∈ F then 1 else 0) := by
        apply Finset.sum_le_sum
        intro c hc
        by_cases hcf : c ∈ F
        · simp only [F, Finset.mem_filter] at hcf
          simp [hcf.2]
        · have hcne : (row S inc c).card ≠ 4 := by
            intro h
            exact hcf (Finset.mem_filter.mpr ⟨hc, h⟩)
          have hle := hrow c hc
          omega
      _ = 3 * m + f := by
        simp [F, m, f, Finset.sum_add_distrib, Finset.sum_ite]
  by_contra hnot
  have hlarge : C.card + 2 ≤ S.card := by omega
  have hf : 6 ≤ f := by
    have : 3 * (m + 2) ≤ 3 * m + f := hsum.trans hupper
    dsimp [m] at this
    omega
  have hcontr : False := by
    rcases (em (∃ c ∈ C, (row S inc c).card = 4)) with hfull | hnone
    · rcases hfull with ⟨c₀, hc₀, hc₀full⟩
      have hFpos : 0 < f := by
        dsimp [f, F]
        exact Finset.card_pos.mpr ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hc₀full⟩⟩
      have hFour := hrow c₀ hc₀
      -- Bound all outside-core incidences by one per full row and two per other row.
      have houtside : 3 * ((S \ T).card) ≤ f + 2 * m := by
        have hcnt :
            (∑ c ∈ C, ((row S inc c) \ T).card) ≤ f + 2 * m := by
          calc
            (∑ c ∈ C, ((row S inc c) \ T).card) ≤
                ∑ c ∈ C, (if c ∈ F then 1 else 2) := by
              apply Finset.sum_le_sum
              intro c hc
              by_cases hcf : c ∈ F
              · have hcorec := hcore c hc ((Finset.mem_filter.mp hcf).2)
                have hcard := Finset.card_sdiff_add_card_inter (row S inc c) T
                have hinter : (row S inc c ∩ T) = T := Finset.inter_eq_right.mpr hcorec
                rw [hinter, (Finset.mem_filter.mp hcf).2, hT] at hcard
                simp [hcf, hcard]
              · have hsmallc : (row S inc c).card ≤ 3 := by
                  have := hrow c hc
                  have hne : (row S inc c).card ≠ 4 := by
                    intro h
                    exact hcf (Finset.mem_filter.mpr ⟨hc, h⟩)
                  omega
                exact (hsmall c hc hsmallc)
            _ = f + 2 * m := by
              simp [F, f, m, Finset.sum_ite]
        have hdouble := sum_row_card_eq_sum_degree C S (fun c x => x ∈ row S inc c)
        -- The fibrewise identity is also used for the set of incidences outside T.
        have hout :
            (∑ c ∈ C, ((row S inc c) \ T).card) =
              ∑ x ∈ S \ T, (C.filter (fun c => x ∈ row S inc c)).card := by
          simpa [row, Finset.mem_sdiff, Finset.filter_filter, and_comm, and_left_comm,
            and_assoc] using
            (sum_row_card_eq_sum_degree C (S \ T) (fun c x => x ∈ row S inc c))
        rw [hout] at hcnt
        have hdegout : 3 * (S \ T).card ≤
            ∑ x ∈ S \ T, (C.filter (fun c => x ∈ row S inc c)).card := by
          calc
            3 * (S \ T).card = ∑ x ∈ S \ T, 3 := by simp
            _ ≤ _ := Finset.sum_le_sum fun x hx => by
              have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
              simpa [row] using hdegree x hxS
        exact hdegout.trans hcnt
      -- Since f ≥ 6, the incidence estimate is at most 3(m − 2).
      have : 3 * S.card ≤ 3 * (m + 1) := by
        have hSdecomp : S.card = (S ∩ T).card + (S \ T).card := by
          have := Finset.card_sdiff_add_card_inter S T
          simpa [Finset.inter_comm] using this.symm
        have hST : (S ∩ T).card ≤ 3 := by
          exact (Finset.card_le_card (Finset.inter_subset_right)).trans_eq hT
        omega
      omega
    · have hfzero : f = 0 := by
        dsimp [f, F]
        rw [Finset.card_eq_zero]
        exact Finset.filter_eq_empty.mpr fun c hc => hnone ⟨c, hc.1, hc.2⟩
      omega
  exact hcontr.elim

/-- The five-element alternative is the matching-set counterpart of the
common-triple case. Smaller rows contribute at most one point outside the
five-set. -/
theorem hall_deficit_one_of_five_set
    (C S : Finset V) (inc : V → V → Prop) (U : Finset V)
    (hU : U.card ≤ 5)
    (hrow : ∀ c ∈ C, (row S inc c).card ≤ 4)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff S inc c d).card ≤ 3)
    (hdegree : ∀ x ∈ S, 3 ≤ (C.filter (fun c => inc c x)).card)
    (hfull : ∀ c ∈ C, (row S inc c).card = 4 → row S inc c ⊆ U)
    (hsmall : ∀ c ∈ C, (row S inc c).card ≤ 3 →
      ((row S inc c) \ U).card ≤ 1) :
    S.card ≤ C.card + 1 := by
  classical
  let F := C.filter (fun c => (row S inc c).card = 4)
  let f := F.card
  let m := C.card
  have hsum : 3 * S.card ≤ ∑ c ∈ C, (row S inc c).card := by
    calc
      3 * S.card = ∑ x ∈ S, 3 := by simp
      _ ≤ ∑ x ∈ S, (C.filter (fun c => inc c x)).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hdegree x hx
      _ = ∑ c ∈ C, (row S inc c).card :=
        (sum_row_card_eq_sum_degree C S inc).symm
  have hupper : (∑ c ∈ C, (row S inc c).card) ≤ 3 * m + f := by
    calc
      (∑ c ∈ C, (row S inc c).card) ≤
          ∑ c ∈ C, (3 + if c ∈ F then 1 else 0) := by
        apply Finset.sum_le_sum
        intro c hc
        by_cases hcf : c ∈ F
        · simp only [F, Finset.mem_filter] at hcf
          simp [hcf.2]
        · have hcne : (row S inc c).card ≠ 4 := by
            intro h
            exact hcf (Finset.mem_filter.mpr ⟨hc, h⟩)
          have hle := hrow c hc
          omega
      _ = 3 * m + f := by
        simp [F, m, f, Finset.sum_add_distrib, Finset.sum_ite]
  by_contra hnot
  have hlarge : C.card + 2 ≤ S.card := by omega
  have hf : 6 ≤ f := by
    have : 3 * (m + 2) ≤ 3 * m + f := hsum.trans hupper
    dsimp [m] at this
    omega
  have houtside : 3 * (S \ U).card ≤ m := by
    have hcnt :
        (∑ c ∈ C, ((row S inc c) \ U).card) ≤ m := by
      calc
        (∑ c ∈ C, ((row S inc c) \ U).card) ≤
            ∑ c ∈ C, (if c ∈ F then 0 else 1) := by
          apply Finset.sum_le_sum
          intro c hc
          by_cases hcf : c ∈ F
          · have hfullc := hfull c hc ((Finset.mem_filter.mp hcf).2)
            have hempty : (row S inc c) \ U = ∅ := Finset.sdiff_eq_empty.mpr hfullc
            simp [hcf, hempty]
          · have hsmallc : (row S inc c).card ≤ 3 := by
              have := hrow c hc
              have hne : (row S inc c).card ≠ 4 := by
                intro h
                exact hcf (Finset.mem_filter.mpr ⟨hc, h⟩)
              omega
            simpa [hcf] using hsmall c hc hsmallc
        _ = m - f := by
          simp [F, m, f, Finset.sum_ite]
    have hout :
        (∑ c ∈ C, ((row S inc c) \ U).card) =
          ∑ x ∈ S \ U, (C.filter (fun c => x ∈ row S inc c)).card := by
      simpa [row, Finset.mem_sdiff, Finset.filter_filter, and_comm, and_left_comm,
        and_assoc] using
        (sum_row_card_eq_sum_degree C (S \ U) (fun c x => x ∈ row S inc c))
    rw [hout] at hcnt
    calc
      3 * (S \ U).card = ∑ x ∈ S \ U, 3 := by simp
      _ ≤ ∑ x ∈ S \ U, (C.filter (fun c => x ∈ row S inc c)).card := by
        apply Finset.sum_le_sum
        intro x hx
        have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
        simpa [row] using hdegree x hxS
      _ ≤ m := hcnt.trans (by omega)
  have hSdecomp : S.card = (S ∩ U).card + (S \ U).card := by
    have := Finset.card_sdiff_add_card_inter S U
    simpa [Finset.inter_comm] using this.symm
  have hSU : (S ∩ U).card ≤ 5 :=
    (Finset.card_le_card Finset.inter_subset_right).trans hU
  have houter : m - 3 ≤ (S \ U).card := by
    dsimp [m] at *
    omega
  have hfinal : 3 * (m - 3) ≤ m := by omega
  omega

end SplitGraphKappaThreeHall

#print axioms SplitGraphKappaThreeHall.sum_row_card_eq_sum_degree
#print axioms SplitGraphKappaThreeHall.hall_deficit_one_of_common_triple
