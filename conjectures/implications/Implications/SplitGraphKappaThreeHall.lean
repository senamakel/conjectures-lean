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

/-- Three incidences per left vertex and a capacity-two upper bound imply the
deficit-one cut inequality. -/
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
