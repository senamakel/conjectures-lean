import Mathlib

/-!
# The residue sum for the gamma part, and its bound

`tau x m` is the contribution `(1/(2+m))(1 − 1/x) − Res(−m)` of the digamma pole at `−m`,
where `Res(w) = (1/2πi)∫ x^s/((s−w)s(s+1)) ds`. We show `|Σ_k tau x (2k+a)| ≤ log x + 1`.
-/

open Filter Topology

namespace Erdos985.Analytic.BoundsAux

/-- Contribution of the pole `w = −m` to the gamma part. -/
noncomputable def tau (x : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x)
  else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x)
  else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))

lemma core_ge (y p M K : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ y) (hK : 0 ≤ K) (hM : 2 * (K + 1) ≤ M) :
    -(1 / 2) * (1 / ((K + 1) * (K + 2))) ≤
      (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1)) := by
  have h1 : M - 1 ≠ 0 := by intro h; linarith
  have h2 : M ≠ 0 := by intro h; linarith
  have h3 : 2 + M ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1))
      - -(1 / 2) * (1 / ((K + 1) * (K + 2))) =
      ((M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) + (K + 1) * (K + 2) * (4 * M - 4) * y
        + 2 * (K + 1) * (K + 2) * (M + 2) * (y - p)) / (2 * M * (K + 1) * (K + 2) * (M - 1) * (2 + M)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  have hy : 0 ≤ y := hp0.trans hp
  apply div_nonneg
  · have : 0 ≤ M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K := by nlinarith
    have : 0 ≤ (M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) := mul_nonneg (by linarith) this
    have : 0 ≤ (K + 1) * (K + 2) * (4 * M - 4) * y :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) hy
    have : 0 ≤ 2 * (K + 1) * (K + 2) * (M + 2) * (y - p) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    linarith
  · have : 0 ≤ M - 1 := by linarith
    have : 0 ≤ M := by linarith
    positivity

lemma core_even (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + 2 * (K + 1)) - (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1))
      - y / (2 * (K + 1) - 1)) ≤ (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 1 ≠ 0 := by intro h; linarith
  have h1' : 2 * (K + 1) - 1 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + 2 * (K + 1)) -
      (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1)) - y / (2 * (K + 1) - 1))) =
      (K * p + 3 * K * y + 2 * p) / (2 * (K + 1) * (K + 2) * (2 * K + 1)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity

lemma core_odd (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + (2 * (K + 1) + 1)) - (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1))
      + 1 / (2 * (K + 1) + 1) - y / (2 * (K + 1) + 1 - 1))
      ≤ 3 * y / 4 * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 3 ≠ 0 := by intro h; linarith
  have h2 : 2 * K + 5 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : 3 * y / 4 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + (2 * (K + 1) + 1)) -
      (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1)) + 1 / (2 * (K + 1) + 1)
        - y / (2 * (K + 1) + 1 - 1))) =
      (4 * K ^ 2 * p + 8 * K ^ 2 + 18 * K * p + 6 * K * y + 24 * K + 20 * p + 9 * y + 16) /
        (4 * (K + 1) * (K + 2) * (2 * K + 3) * (2 * K + 5)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity

lemma tau_ge (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (m : ℕ) (hm : 2 * (k + 1) ≤ m) :
    -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ tau x m := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one (by linarith)]; exact hx
  exact core_ge _ _ _ _ (by positivity) (pow_le_of_le_one hy0.le hy1 hm0) (Nat.cast_nonneg k)
    (by exact_mod_cast hm)

lemma tau_le_even (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    tau x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) ≠ 0 := by omega
  have hm1 : 2 * (k + 1) ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := core_even (1 / x) ((1 / x) ^ (2 * (k + 1))) k (by positivity) hy0.le (Nat.cast_nonneg k)
  push_cast
  exact this

lemma tau_le_odd (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    tau x (2 * (k + 1) + 1) ≤ 3 * (1 / x) / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) + 1 ≠ 0 := by omega
  have hm1 : 2 * (k + 1) + 1 ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := core_odd (1 / x) ((1 / x) ^ (2 * (k + 1) + 1)) k (by positivity) hy0.le
    (Nat.cast_nonneg k)
  push_cast
  exact this

lemma hasSum_u : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      1 - 1 / ((n : ℝ) + 1) := by
    intro n
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + 1)) n
    simp only [Nat.cast_zero, zero_add, div_one, Nat.cast_add, Nat.cast_one] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
    ring
  simp_rw [hps]
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ)
  simpa using this

theorem tsum_tau_bound (x : ℝ) (hx : 1 ≤ x) (a : ℕ) (ha : a ≤ 1) :
    Summable (fun k : ℕ => tau x (2 * k + a)) ∧
      |∑' k : ℕ, tau x (2 * k + a)| ≤ Real.log x + 1 := by
  set y := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; exact hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL1 : 1 - y ≤ Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < x)
    rwa [hy, one_div]
  set u : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  -- B is the upper constant
  set B : ℝ := if a = 0 then (3 * y - 1) / 2 else 3 * y / 4 with hB
  have hup : ∀ k : ℕ, tau x (2 * (k + 1) + a) ≤ B * u k := by
    intro k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · simp only [hB, ↓reduceIte]; exact tau_le_even x hx k
    · simp only [hB, one_ne_zero, ite_false]; exact tau_le_odd x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * u k ≤ tau x (2 * (k + 1) + a) :=
    fun k => tau_ge x hx k _ (by omega)
  have hB1 : |B| ≤ 1 := by
    rw [hB]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hg : Summable (fun k : ℕ => tau x (2 * (k + 1) + a)) := by
    refine Summable.of_norm_bounded hasSum_u.summable (fun k => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hup k
    have h2 := hlo k
    have h3 : B * u k ≤ u k := by
      have := (abs_le.mp hB1).2
      nlinarith [hu0 k]
    constructor <;> nlinarith [hu0 k]
  have hS : Summable (fun k : ℕ => tau x (2 * k + a)) := by
    exact (summable_nat_add_iff 1).mp hg
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have e1 : (fun k : ℕ => tau x (2 * (k + 1) + a)) = fun k : ℕ => tau x (2 * (k + 1) + a) := rfl
  have hle : ∑' k : ℕ, tau x (2 * (k + 1) + a) ≤ B := by
    have := Summable.tsum_le_tsum hup hg (hasSum_u.summable.mul_left B)
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, tau x (2 * (k + 1) + a) := by
    have := Summable.tsum_le_tsum hlo (hasSum_u.summable.mul_left _) hg
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · simp only [hB, ite_true] at hle
    simp only [mul_zero, add_zero, tau, ite_true] at hle hge ⊢
    rw [← hy] at *
    rw [abs_le]; constructor <;> linarith
  · simp only [hB, one_ne_zero, ite_false] at hle
    simp only [mul_zero, zero_add, tau, ite_true, one_ne_zero, ite_false] at hle hge ⊢
    rw [← hy] at *
    have hyL : y * Real.log x ≤ Real.log x := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hy0.le hL]

end Erdos985.Analytic.BoundsAux
