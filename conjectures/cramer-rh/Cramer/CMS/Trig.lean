import Cramer.CMS.Cells
import Cramer.CMS.Weight

/-!
# The transform of the weight at a zero is `(2 − 2cos θ)|Q(cos θ)|`

For `c` symmetric about `L` (`c_{2L−j} = c_j`, `J = 2L`, `c_0 = 0`), with `a_j` its second
differences:

* `‖Σ_j a_j e^{ijθ}‖ = |Σ_j a_j cos((j − L)θ)|` (`norm_sum_exp_eq`): factor `e^{iLθ}` and pair
  `j` with `2L − j`, which cancels the sines;
* `Σ_j a_j cos((j−L)θ) = (2cos θ − 2) Σ_j c_j cos((j−L)θ)` (summation by parts and
  `cos(u+θ) + cos(u−θ) = 2 cos u cos θ`);
* `cos(nθ) = Σ_i T_{n,i} cos^i θ` with the Chebyshev coefficients `tc n i`, so
  `Σ_j c_j cos((j−L)θ) = Q(cos θ)` once the coefficients of `Q` are
  `q_i = Σ_j c_j T_{|j−L|, i}` (`coefOK`, checked by `decide`).
-/

namespace Cramer.CMS

open Finset Complex Real

/-- The Chebyshev coefficients: `T_n(x) = Σ_i tc n i x^i`. -/
def tc : ℕ → ℕ → ℤ
  | 0, i => if i = 0 then 1 else 0
  | 1, i => if i = 1 then 1 else 0
  | n + 2, i => 2 * (if i = 0 then 0 else tc (n + 1) (i - 1)) - tc n i

lemma tc_add_two (n i : ℕ) :
    tc (n + 2) i = 2 * (if i = 0 then 0 else tc (n + 1) (i - 1)) - tc n i := rfl

lemma tc_eq_zero : ∀ n i, n < i → tc n i = 0
  | 0, i, h => by simp [tc]; omega
  | 1, i, h => by simp [tc]; omega
  | n + 2, i, h => by
    simp only [tc]
    rw [tc_eq_zero n i (by omega)]
    split_ifs with hi
    · omega
    · rw [tc_eq_zero (n + 1) (i - 1) (by omega)]; ring

/-- `cos(nθ) = Σ_{i ≤ D} tc n i cos^i θ` for `n ≤ D`. -/
lemma cos_nat_mul_eq (D : ℕ) : ∀ n, n ≤ D → ∀ θ : ℝ,
    Real.cos (n * θ) = ∑ i ∈ range (D + 1), (tc n i : ℝ) * Real.cos θ ^ i
  | 0, _, θ => by
    rw [sum_eq_single 0 (fun i _ hi => by simp [tc, hi]) (by simp)]; simp [tc]
  | 1, hD, θ => by
    rw [sum_eq_single 1 (fun i _ hi => by simp [tc, hi]) (by simp; omega)]; simp [tc]
  | n + 2, hD, θ => by
    have h1 := cos_nat_mul_eq D (n + 1) (by omega) θ
    have h0 := cos_nat_mul_eq D n (by omega) θ
    have hrec : Real.cos (((n + 2 : ℕ) : ℝ) * θ) =
        2 * Real.cos θ * Real.cos (((n + 1 : ℕ) : ℝ) * θ) - Real.cos ((n : ℝ) * θ) := by
      have a := Real.cos_add (((n + 1 : ℕ) : ℝ) * θ) θ
      have b := Real.cos_sub (((n + 1 : ℕ) : ℝ) * θ) θ
      have e1 : ((n + 2 : ℕ) : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      have e2 : (n : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      rw [e1, e2, a, b]; ring
    rw [hrec, h1, h0]
    -- `Σ (2[i≥1] tc(n+1)(i−1) − tc n i) x^i = 2x Σ tc(n+1) i x^i − Σ tc n i x^i`
    set x := Real.cos θ
    have hR : ∑ i ∈ range (D + 1), (tc (n + 2) i : ℝ) * x ^ i =
        2 * ∑ i ∈ range (D + 1), (if i = 0 then (0 : ℝ) else (tc (n + 1) (i - 1) : ℝ)) * x ^ i -
          ∑ i ∈ range (D + 1), (tc n i : ℝ) * x ^ i := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [tc_add_two]; push_cast; split_ifs <;> ring
    have hS : ∑ i ∈ range (D + 1), (if i = 0 then (0 : ℝ) else (tc (n + 1) (i - 1) : ℝ)) * x ^ i =
        x * ∑ i ∈ range (D + 1), (tc (n + 1) i : ℝ) * x ^ i := by
      rw [sum_range_succ', sum_range_succ, tc_eq_zero (n + 1) D (by omega), mul_add, mul_sum]
      simp only [if_true, zero_mul, add_zero, Int.cast_zero, mul_zero, Nat.add_sub_cancel,
        show ∀ i : ℕ, i + 1 ≠ 0 from fun i => by omega, ite_false]
      refine sum_congr rfl fun i _ => by ring
    rw [hR, hS]; ring

/-! ### Symmetric sums -/

/-- `‖Σ_j a_j e^{ijθ}‖ = |Σ_j a_j cos((j − L)θ)|` for `a` symmetric about `L`. -/
lemma norm_sum_exp_eq (a : ℕ → ℤ) (L : ℕ) (ha : ∀ j, j ≤ 2 * L → a (2 * L - j) = a j) (θ : ℝ) :
    ‖∑ j ∈ range (2 * L + 1), (a j : ℂ) * exp (I * (((j : ℝ) * θ : ℝ) : ℂ))‖ =
      |∑ j ∈ range (2 * L + 1), (a j : ℝ) * Real.cos (((j : ℝ) - L) * θ)| := by
  have e : ∑ j ∈ range (2 * L + 1), (a j : ℂ) * exp (I * (((j : ℝ) * θ : ℝ) : ℂ)) =
      exp (I * (((L : ℝ) * θ : ℝ) : ℂ)) *
        ∑ j ∈ range (2 * L + 1), (a j : ℂ) * exp (I * (((((j : ℝ) - L) * θ) : ℝ) : ℂ)) := by
    rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e, norm_mul,
    show I * (((L : ℝ) * θ : ℝ) : ℂ) = (((L : ℝ) * θ : ℝ) : ℂ) * I by ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  -- the sum is real
  have hsin : ∑ j ∈ range (2 * L + 1), (a j : ℝ) * Real.sin (((j : ℝ) - L) * θ) = 0 := by
    have hr := sum_range_reflect (fun j => (a j : ℝ) * Real.sin (((j : ℝ) - L) * θ)) (2 * L + 1)
    have : ∑ j ∈ range (2 * L + 1), (a (2 * L + 1 - 1 - j) : ℝ) *
        Real.sin ((((2 * L + 1 - 1 - j : ℕ) : ℝ) - L) * θ) =
        -∑ j ∈ range (2 * L + 1), (a j : ℝ) * Real.sin (((j : ℝ) - L) * θ) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hj' : j ≤ 2 * L := by have := mem_range.1 hj; omega
      rw [show 2 * L + 1 - 1 - j = 2 * L - j by omega, ha j hj', Nat.cast_sub hj']
      push_cast
      rw [show ((2 : ℝ) * L - j - L) * θ = -(((j : ℝ) - L) * θ) by ring, Real.sin_neg]; ring
    rw [this] at hr; linarith
  have hsplit : ∑ j ∈ range (2 * L + 1), (a j : ℂ) * exp (I * (((((j : ℝ) - L) * θ) : ℝ) : ℂ)) =
      ((∑ j ∈ range (2 * L + 1), (a j : ℝ) * Real.cos (((j : ℝ) - L) * θ) : ℝ) : ℂ) +
        ((∑ j ∈ range (2 * L + 1), (a j : ℝ) * Real.sin (((j : ℝ) - L) * θ) : ℝ) : ℂ) * I := by
    have e1 : ∀ u : ℝ, ∀ z : ℤ, (z : ℂ) * exp (I * (u : ℂ)) =
        (((z : ℝ) * Real.cos u : ℝ) : ℂ) + (((z : ℝ) * Real.sin u : ℝ) : ℂ) * I := by
      intro u z
      rw [mul_comm I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
    rw [sum_congr rfl fun j _ => e1 _ _, sum_add_distrib, ← sum_mul, Complex.ofReal_sum,
      Complex.ofReal_sum]
  rw [hsplit, hsin, Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs]

/-- `Σ_j a_j cos((j−L)θ) = (2cos θ − 2) Σ_j c_j cos((j−L)θ)`. -/
lemma sum_aco_cos (c : ℕ → ℤ) {J L : ℕ} (hc0 : c 0 = 0) (hcJ : ∀ j, J ≤ j → c j = 0) (θ : ℝ) :
    ∑ j ∈ range (J + 1), (aco c j : ℝ) * Real.cos (((j : ℝ) - L) * θ) =
      (2 * Real.cos θ - 2) * ∑ j ∈ range (J + 1), (c j : ℝ) * Real.cos (((j : ℝ) - L) * θ) := by
  rw [sum_aco_mul (R := ℝ) c hc0 hcJ, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hc0]
  · simp only [Nat.pos_iff_ne_zero.1 hj, if_false]
    rw [Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast
    have a := Real.cos_add (((j : ℝ) - L) * θ) θ
    have b := Real.cos_sub (((j : ℝ) - L) * θ) θ
    rw [show ((j : ℝ) + 1 - L) * θ = ((j : ℝ) - L) * θ + θ by ring,
      show ((j : ℝ) - 1 - L) * θ = ((j : ℝ) - L) * θ - θ by ring, a, b]
    ring

/-- The coefficient check: `q_i = Σ_j c_j T_{|j−L|, i}` for `i ≤ D`, and `qs` has length `D + 1`. -/
def coefOK (c : ℕ → ℤ) (J L D : ℕ) (qs : List ℤ) : Bool :=
  decide (qs.length = D + 1) &&
    (List.range (D + 1)).all fun i =>
      decide ((∑ j ∈ range (J + 1), c j * tc (Int.natAbs ((j : ℤ) - L)) i) = qs.getD i 0)

/-- `Σ_j c_j cos((j−L)θ) = Q(cos θ)` under the coefficient check. -/
lemma sum_c_cos_eq (c : ℕ → ℤ) {J L D : ℕ} {qs : List ℤ} (hJ : J ≤ 2 * L) (hLD : L ≤ D)
    (h : coefOK c J L D qs = true) (θ : ℝ) :
    ∑ j ∈ range (J + 1), (c j : ℝ) * Real.cos (((j : ℝ) - L) * θ) = Qv qs (Real.cos θ) := by
  simp only [coefOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hco⟩ := h
  unfold Qv
  rw [hlen]
  have e : ∀ j ∈ range (J + 1), (c j : ℝ) * Real.cos (((j : ℝ) - L) * θ) =
      ∑ i ∈ range (D + 1), (c j : ℝ) * (tc (Int.natAbs ((j : ℤ) - L)) i : ℝ) * Real.cos θ ^ i := by
    intro j hj
    have hjL : Int.natAbs ((j : ℤ) - L) ≤ D := by
      have := mem_range.1 hj; omega
    have hcos : Real.cos (((j : ℝ) - L) * θ) = Real.cos ((Int.natAbs ((j : ℤ) - L) : ℝ) * θ) := by
      rcases le_total L j with hle | hle
      · rw [show ((Int.natAbs ((j : ℤ) - L) : ℕ) : ℝ) = (j : ℝ) - L by
          rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
          rw [abs_of_nonneg (by have : (L : ℝ) ≤ j := by exact_mod_cast hle
                                linarith)]]
      · rw [show ((Int.natAbs ((j : ℤ) - L) : ℕ) : ℝ) = -((j : ℝ) - L) by
          rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
          rw [abs_of_nonpos (by have : (j : ℝ) ≤ L := by exact_mod_cast hle
                                linarith)], neg_mul, Real.cos_neg]
    rw [hcos, cos_nat_mul_eq D _ hjL θ, mul_sum]
    refine sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl e, sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_mul, ← hco i (mem_range.1 hi)]
  push_cast
  refine congrArg (· * _) (sum_congr rfl fun j _ => by ring)

/-- **The transform at a zero.** -/
theorem norm_sum_aco_exp (c : ℕ → ℤ) {L D : ℕ} {qs : List ℤ} (hc0 : c 0 = 0)
    (hcJ : ∀ j, 2 * L ≤ j → c j = 0) (hsym : ∀ j, j ≤ 2 * L → c (2 * L - j) = c j)
    (hLD : L ≤ D) (h : coefOK c (2 * L) L D qs = true) (θ : ℝ) :
    ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * exp (I * (((j : ℝ) * θ : ℝ) : ℂ))‖ =
      (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| := by
  have h0 : aco c (2 * L) = aco c 0 := by
    unfold aco
    rw [hcJ (2 * L + 1) (by omega), hcJ (2 * L) le_rfl, hc0]
    by_cases hL : 2 * L = 0
    · have : c 1 = 0 := hcJ 1 (by omega)
      simp [hL, this]
    · simp only [hL, if_false, if_true]
      rw [hsym 1 (by omega)]; ring
  have hasym : ∀ j, j ≤ 2 * L → aco c (2 * L - j) = aco c j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using h0
    · rcases Nat.lt_or_ge j (2 * L) with hjl | hjl
      · unfold aco
        simp only [show 2 * L - j ≠ 0 by omega, Nat.pos_iff_ne_zero.1 hj0, if_false]
        rw [show 2 * L - j + 1 = 2 * L - (j - 1) by omega, hsym (j - 1) (by omega),
          show 2 * L - j - 1 = 2 * L - (j + 1) by omega, hsym (j + 1) (by omega), hsym j hj]
        ring
      · have hj2 : j = 2 * L := le_antisymm hj hjl
        subst hj2
        rw [Nat.sub_self, h0]
  rw [norm_sum_exp_eq (aco c) L hasym θ, sum_aco_cos c hc0 hcJ θ,
    sum_c_cos_eq c le_rfl hLD h θ, abs_mul]
  rw [abs_of_nonpos (by linarith [Real.cos_le_one θ])]
  ring

end Cramer.CMS
