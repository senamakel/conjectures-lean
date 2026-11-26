import Mertens.FareyAlg

/-!
# `∫₀¹ {q x} {r x} dx = 1/4 + gcd(q, r)² / (12 q r)`

1. `integral_fract_add`: `∫₀¹ {x + a} dx = 1/2`.
2. `integral_fract_mul_fract`: `∫₀¹ {x + a}{x + b} dx = 1/4 + B₂({b - a})/2`.
3. `integral_fract_mul_fract_mul`: Hermite's identity for both factors reduces
   `∫₀¹ {q x}{r x} dx` to `1/4 + ½ ∑_{i<q, j<r} B₂({j/r - i/q})`, and the distribution relation and
   `sum_B2_fract_mul_div` evaluate the double sum as `gcd(q, r)²/(6qr)`.
-/

namespace Mertens

open Finset MeasureTheory intervalIntegral

/-- A bounded measurable function is interval integrable. -/
lemma intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (M := C) (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma measurable_fract_affine (c a : ℝ) : Measurable fun x : ℝ => Int.fract (c * x + a) :=
  measurable_fract.comp ((measurable_id.const_mul c).add_const a)

lemma abs_fract_le_one (x : ℝ) : |Int.fract x| ≤ 1 := by
  rw [abs_of_nonneg (Int.fract_nonneg x)]; exact (Int.fract_lt_one x).le

lemma ii_fract (c a s t : ℝ) : IntervalIntegrable (fun x : ℝ => Int.fract (c * x + a)) volume s t :=
  intervalIntegrable_of_bounded (measurable_fract_affine c a) (fun x => abs_fract_le_one _) s t

lemma ii_fract_mul (c a d b s t : ℝ) :
    IntervalIntegrable (fun x : ℝ => Int.fract (c * x + a) * Int.fract (d * x + b)) volume s t :=
  intervalIntegrable_of_bounded (f := fun x => Int.fract (c * x + a) * Int.fract (d * x + b))
    ((measurable_fract_affine c a).mul (measurable_fract_affine d b))
    (fun x => by
      rw [abs_mul]
      calc |Int.fract (c * x + a)| * |Int.fract (d * x + b)| ≤ 1 * 1 :=
            mul_le_mul (abs_fract_le_one _) (abs_fract_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1) s t

lemma ae_ne_real (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]
  simp

lemma ii_fract_mul' (s a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => Int.fract y * Int.fract (y + s)) volume a b := by
  simpa using ii_fract_mul 1 0 1 s a b

/-- `∫₀¹ {y}{y + s} dy = 1/4 + B₂(s)/2` for `0 ≤ s < 1`. -/
lemma integral_fract_mul_fract_shift {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∫ y in (0 : ℝ)..1, Int.fract y * Int.fract (y + s) = 1 / 4 + B2 s / 2 := by
  rw [← integral_add_adjacent_intervals (b := 1 - s) (ii_fract_mul' s 0 (1 - s))
    (ii_fract_mul' s (1 - s) 1)]
  have h1 : ∫ y in (0 : ℝ)..(1 - s), Int.fract y * Int.fract (y + s) =
      ∫ y in (0 : ℝ)..(1 - s), y * (y + s) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_real (1 - s)] with y hy hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    obtain ⟨h0, h1⟩ := hmem
    have hlt : y < 1 - s := lt_of_le_of_ne h1 hy
    rw [Int.fract_eq_self.2 ⟨h0.le, by linarith⟩, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
  have h2 : ∫ y in (1 - s)..1, Int.fract y * Int.fract (y + s) =
      ∫ y in (1 - s)..1, y * (y + s - 1) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_real 1] with y hy hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    obtain ⟨h0, h1⟩ := hmem
    have hlt : y < 1 := lt_of_le_of_ne h1 hy
    rw [Int.fract_eq_self.2 ⟨by linarith, hlt⟩]
    have : Int.fract (y + s) = y + s - 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, 1, by push_cast; ring⟩
    rw [this]
  have h3 : ∫ y in (0 : ℝ)..(1 - s), y * (y + s) =
      ((1 - s) ^ 3 / 3 + s * (1 - s) ^ 2 / 2) - (0 ^ 3 / 3 + s * 0 ^ 2 / 2) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun y => y ^ 3 / 3 + s * y ^ 2 / 2)
      (fun y _ => ?_) ((by fun_prop : Continuous fun y : ℝ => y * (y + s)).intervalIntegrable
        0 (1 - s))
    have := ((hasDerivAt_pow 3 y).div_const 3).add (((hasDerivAt_pow 2 y).const_mul s).div_const 2)
    convert this using 1
    try (push_cast; ring)
  have h4 : ∫ y in (1 - s)..1, y * (y + s - 1) =
      ((1 : ℝ) ^ 3 / 3 + (s - 1) * 1 ^ 2 / 2) - ((1 - s) ^ 3 / 3 + (s - 1) * (1 - s) ^ 2 / 2) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun y => y ^ 3 / 3 + (s - 1) * y ^ 2 / 2)
      (fun y _ => ?_) ((by fun_prop : Continuous fun y : ℝ => y * (y + s - 1)).intervalIntegrable
        (1 - s) 1)
    have := ((hasDerivAt_pow 3 y).div_const 3).add
      (((hasDerivAt_pow 2 y).const_mul (s - 1)).div_const 2)
    convert this using 1
    try (push_cast; ring)
  rw [h1, h2, h3, h4]
  unfold B2
  ring

lemma periodic_fract_mul_fract (t : ℝ) :
    Function.Periodic (fun y : ℝ => Int.fract y * Int.fract (y + t)) 1 := by
  intro y
  simp only
  rw [Int.fract_add_one, show y + 1 + t = (y + t) + 1 by ring, Int.fract_add_one]

/-- `∫₀¹ {x + a}{x + b} dx = 1/4 + B₂({b - a})/2`. -/
lemma integral_fract_mul_fract (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, Int.fract (x + a) * Int.fract (x + b) =
      1 / 4 + B2 (Int.fract (b - a)) / 2 := by
  have e1 : ∫ x in (0 : ℝ)..1, Int.fract (x + a) * Int.fract (x + b) =
      ∫ x in (0 : ℝ)..1, (fun y => Int.fract y * Int.fract (y + (b - a))) (x + a) := by
    refine integral_congr fun x _ => ?_
    simp only
    rw [show x + a + (b - a) = x + b by ring]
  rw [e1, intervalIntegral.integral_comp_add_right
    (fun y => Int.fract y * Int.fract (y + (b - a))) a, zero_add, add_comm 1 a,
    (periodic_fract_mul_fract (b - a)).intervalIntegral_add_eq a 0, zero_add]
  have e2 : ∫ y in (0 : ℝ)..1, Int.fract y * Int.fract (y + (b - a)) =
      ∫ y in (0 : ℝ)..1, Int.fract y * Int.fract (y + Int.fract (b - a)) := by
    refine integral_congr fun y _ => ?_
    congr 1
    conv_lhs => rw [← Int.floor_add_fract (b - a)]
    rw [show y + ((⌊b - a⌋ : ℝ) + Int.fract (b - a)) = (y + Int.fract (b - a)) + ⌊b - a⌋ by ring,
      Int.fract_add_intCast]
  rw [e2, integral_fract_mul_fract_shift (Int.fract_nonneg _) (Int.fract_lt_one _)]

/-- `∫₀¹ {x + a} dx = 1/2`. -/
lemma integral_fract_add (a : ℝ) : ∫ x in (0 : ℝ)..1, Int.fract (x + a) = 1 / 2 := by
  have hp : Function.Periodic (fun y : ℝ => Int.fract y) 1 := fun y => Int.fract_add_one y
  rw [integral_comp_add_right (fun y => Int.fract y), zero_add, add_comm 1 a,
    hp.intervalIntegral_add_eq a 0, zero_add]
  have : ∫ y in (0 : ℝ)..1, Int.fract y = ∫ y in (0 : ℝ)..1, y := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_real 1] with y hy hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    exact Int.fract_eq_self.2 ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hy⟩
  rw [this, integral_id]
  norm_num

lemma B2_fract_neg (t : ℝ) : B2 (Int.fract (-t)) = B2 (Int.fract t) := by
  by_cases h : Int.fract t = 0
  · rw [h, Int.fract_neg_eq_zero.2 h]
  · rw [Int.fract_neg h]; unfold B2; ring

lemma ii_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  have := IntervalIntegrable.sum s h
  convert this using 1
  funext x
  simp [Finset.sum_apply]

lemma ii_sum_fract (n : ℕ) (s t : ℝ) :
    IntervalIntegrable (fun x : ℝ => ∑ i ∈ range n, Int.fract (x + i / n)) volume s t := by
  refine ii_finset_sum (range n) (f := fun i x => Int.fract (x + i / n)) fun i _ => ?_
  simpa using ii_fract 1 ((i : ℝ) / n) s t

/-- **The key integral**: `∫₀¹ {q x}{r x} dx = 1/4 + gcd(q, r)²/(12 q r)`. -/
theorem integral_fract_mul_fract_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    ∫ x in (0 : ℝ)..1, Int.fract ((q : ℝ) * x) * Int.fract ((r : ℝ) * x) =
      1 / 4 + (Nat.gcd q r : ℝ) ^ 2 / (12 * q * r) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set Sq : ℝ → ℝ := fun x => ∑ i ∈ range q, Int.fract (x + i / q)
  set Sr : ℝ → ℝ := fun x => ∑ j ∈ range r, Int.fract (x + j / r)
  have hH : ∀ x, Int.fract ((q : ℝ) * x) * Int.fract ((r : ℝ) * x) =
      Sq x * Sr x - ((r : ℝ) - 1) / 2 * Sq x - ((q : ℝ) - 1) / 2 * Sr x +
        ((q : ℝ) - 1) * ((r : ℝ) - 1) / 4 := by
    intro x
    simp only [Sq, Sr]
    rw [sum_fract_add_div x hq, sum_fract_add_div x hr]
    ring
  have iq := ii_sum_fract q 0 1
  have ir := ii_sum_fract r 0 1
  have iqr : IntervalIntegrable (fun x => Sq x * Sr x) volume 0 1 := by
    have : (fun x => Sq x * Sr x) =
        fun x : ℝ => ∑ i ∈ range q, ∑ j ∈ range r,
          Int.fract (x + (i : ℝ) / q) * Int.fract (x + (j : ℝ) / r) := by
      funext x; simp only [Sq, Sr]; rw [sum_mul_sum]
    rw [this]
    refine ii_finset_sum (range q) (f := fun i x => ∑ j ∈ range r,
      Int.fract (x + (i : ℝ) / q) * Int.fract (x + (j : ℝ) / r)) fun i _ =>
      ii_finset_sum (range r) (f := fun j x =>
        Int.fract (x + (i : ℝ) / q) * Int.fract (x + (j : ℝ) / r)) fun j _ => ?_
    simpa using ii_fract_mul 1 ((i : ℝ) / q) 1 ((j : ℝ) / r) 0 1
  have hSq : ∫ x in (0 : ℝ)..1, Sq x = q / 2 := by
    simp only [Sq]
    rw [intervalIntegral.integral_finsetSum fun i _ => by simpa using ii_fract 1 ((i : ℝ) / q) 0 1]
    simp only [integral_fract_add, sum_const, card_range, nsmul_eq_mul]
    ring
  have hSr : ∫ x in (0 : ℝ)..1, Sr x = r / 2 := by
    simp only [Sr]
    rw [intervalIntegral.integral_finsetSum fun i _ => by simpa using ii_fract 1 ((i : ℝ) / r) 0 1]
    simp only [integral_fract_add, sum_const, card_range, nsmul_eq_mul]
    ring
  have hB : ∑ i ∈ range q, ∑ j ∈ range r, B2 (Int.fract ((j : ℝ) / r - i / q)) =
      (Nat.gcd q r : ℝ) ^ 2 / (6 * q * r) := by
    have h1 : ∀ i ∈ range q, ∑ j ∈ range r, B2 (Int.fract ((j : ℝ) / r - i / q)) =
        B2 (Int.fract ((r : ℝ) * i / q)) / r := by
      intro i _
      have := sum_B2_fract_add_div (-((i : ℝ) / q)) hr
      rw [show (r : ℝ) * -((i : ℝ) / q) = -((r : ℝ) * i / q) by ring, B2_fract_neg] at this
      rw [← this]
      refine sum_congr rfl fun j _ => ?_
      congr 2; ring
    rw [sum_congr rfl h1, ← sum_div, sum_B2_fract_mul_div r hq, Nat.gcd_comm]
    field_simp
  have hSqSr : ∫ x in (0 : ℝ)..1, Sq x * Sr x = q * r / 4 + (Nat.gcd q r : ℝ) ^ 2 / (12 * q * r) := by
    have : (fun x => Sq x * Sr x) =
        fun x : ℝ => ∑ i ∈ range q, ∑ j ∈ range r,
          Int.fract (x + (i : ℝ) / q) * Int.fract (x + (j : ℝ) / r) := by
      funext x; simp only [Sq, Sr]; rw [sum_mul_sum]
    rw [this, intervalIntegral.integral_finsetSum (s := range q)
      (f := fun (i : ℕ) (x : ℝ) => ∑ j ∈ range r,
        Int.fract (x + (i : ℝ) / q) * Int.fract (x + (j : ℝ) / r))
      (fun i _ => ii_finset_sum (range r) (f := fun j x =>
        Int.fract (x + (i : ℝ) / q) * Int.fract (x + (j : ℝ) / r)) fun j _ => by
          simpa using ii_fract_mul 1 ((i : ℝ) / q) 1 ((j : ℝ) / r) 0 1)]
    have h2 : ∀ i ∈ range q, ∫ x in (0 : ℝ)..1, ∑ j ∈ range r,
        Int.fract (x + i / q) * Int.fract (x + j / r) =
          ∑ j ∈ range r, (1 / 4 + B2 (Int.fract ((j : ℝ) / r - i / q)) / 2) := by
      intro i _
      rw [intervalIntegral.integral_finsetSum fun j _ => by
        simpa using ii_fract_mul 1 ((i : ℝ) / q) 1 ((j : ℝ) / r) 0 1]
      exact sum_congr rfl fun j _ => integral_fract_mul_fract _ _
    rw [sum_congr rfl h2]
    simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div]
    rw [hB]
    field_simp
    ring
  rw [integral_congr fun x _ => hH x]
  rw [integral_add (((iqr.sub (iq.const_mul _)).sub (ir.const_mul _))) intervalIntegrable_const,
    integral_sub ((iqr.sub (iq.const_mul _))) (ir.const_mul _), integral_sub iqr (iq.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hSqSr, hSq, hSr, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, one_mul]
  field_simp
  ring

end Mertens
