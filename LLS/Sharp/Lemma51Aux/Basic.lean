import LLS.Sharp.Defs
import Robin.Mertens.Abelian.Zeta

/-!
# Auxiliary lemmas for LLS Lemma 5.1

* `l1Sum1_add_P2sum`: `l1Sum1 x + P2sum x / log x = Σ_{n ≤ x} Λ(n)(1/(n log n) − 1/(x log x))`;
* `per_prime`: the contribution of the powers of one prime `p ≤ √x`;
* `bZ_two`, `summable_bZ_two`, `tail_bZ_two_le`: the Euler product of `ζ(2)` in log form and
  its tail beyond `N`.
-/

namespace LLS.Sharp.L51

open Real
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt

/-- The full prime-power series at `p` with coefficient `z`. -/
lemma hasSum_pp {p : ℝ} (hp : 1 < p) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ => (1 + (z ^ (k + 1)).re) / ((k + 1) * p ^ (k + 1)))
      (-Real.log (1 - 1 / p) - Real.log ‖1 - z / p‖) := by
  have hp0 : 0 < p := by linarith
  have h1 : ‖((1 / p : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one hp0).2 hp
  have h2 : ‖z / (p : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    exact (div_lt_one hp0).2 (lt_of_le_of_lt hz hp)
  have hs := ((Complex.hasSum_taylorSeries_neg_log h1).add
    (Complex.hasSum_taylorSeries_neg_log h2)).mapL Complex.reCLM
  have hs' := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton] at hs'
  convert hs' using 1
  · funext k
    simp only [Complex.reCLM_apply]
    have : ((1 / p : ℝ) : ℂ) ^ (k + 1) / ((k + 1 : ℕ) : ℂ) + (z / p) ^ (k + 1) / ((k + 1 : ℕ) : ℂ)
        = ((1 / ((k + 1) * p ^ (k + 1)) : ℝ) : ℂ) * (1 + z ^ (k + 1)) := by
      push_cast
      field_simp
      simp only [div_pow, one_pow]
      ring
    rw [this, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
    ring
  · simp only [Complex.reCLM_apply, Complex.add_re, Complex.neg_re, Complex.log_re]
    simp only [pow_zero, Nat.cast_zero, div_zero, add_zero, Complex.zero_re, sub_zero]
    have : (1 : ℂ) - ((1 / p : ℝ) : ℂ) = ((1 - 1 / p : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by rw [sub_pos]; exact (div_lt_one hp0).2 hp)]
    ring


lemma re_pow_bounds {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    0 ≤ 1 + (z ^ k).re ∧ 1 + (z ^ k).re ≤ 2 := by
  have h1 : ‖z ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have h2 := Complex.abs_re_le_norm (z ^ k)
  constructor <;> linarith [abs_le.1 (h2.trans h1)]

/-- The prime-by-prime estimate. -/
lemma per_prime {p x : ℕ} (hp : p.Prime) (hpx : p ^ 2 ≤ x) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    -Real.log (1 - 1 / (p : ℝ) ^ 2) - 10 / 3 / x ≤
      ∑ k ∈ Finset.range (Nat.log p x),
        ((1 + (z ^ (k + 1)).re) / ((k + 1) * (p : ℝ) ^ (k + 1))
          - (1 + (z ^ (k + 1)).re) * Real.log p / (x * Real.log x)) := by
  set K := Nat.log p x with hKdef
  have hp1 : 1 < p := hp.one_lt
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hpx; have : 0 < p ^ 2 := by positivity
    omega
  have hK2 : 2 ≤ K := Nat.le_log_of_pow_le hp1 hpx
  have hpK : p ^ K ≤ x := Nat.pow_log_le_self p hx0
  have hxK : x < p ^ (K + 1) := Nat.lt_pow_succ_log_self hp1 x
  set q : ℝ := (p : ℝ) with hq
  have hq1 : (1 : ℝ) < q := by rw [hq]; exact_mod_cast hp1
  have hq2 : (2 : ℝ) ≤ q := by rw [hq]; exact_mod_cast hp.two_le
  have hq0 : 0 < q := by linarith
  have hxr : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hx0
  have hx4 : (4 : ℝ) ≤ x := by
    have : 4 ≤ x := le_trans (by nlinarith [hp.two_le]) hpx
    exact_mod_cast this
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  set a : ℕ → ℝ := fun k => (1 + (z ^ (k + 1)).re) / ((k + 1) * q ^ (k + 1)) with ha
  have hs := hasSum_pp hq1 hz
  have hsplit := hs.summable.sum_add_tsum_nat_add K
  rw [hs.tsum_eq] at hsplit
  -- the full sum
  have hL : -Real.log (1 - 1 / q ^ 2) ≤ -Real.log (1 - 1 / q) - Real.log ‖1 - z / q‖ := by
    have hzq : ‖z / (q : ℂ)‖ ≤ 1 / q := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
      exact div_le_div_of_nonneg_right hz hq0.le
    have hzq1 : 1 / q < 1 := (div_lt_one hq0).2 hq1
    have hn1 : ‖1 - z / (q : ℂ)‖ ≤ 1 + 1 / q := by
      calc ‖1 - z / (q : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖z / (q : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 / q := by rw [norm_one]; linarith
    have hn0 : 0 < ‖1 - z / (q : ℂ)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (z / (q : ℂ))
      rw [norm_one] at this
      linarith
    have hlog := Real.log_le_log hn0 hn1
    have hm : Real.log (1 - 1 / q ^ 2) = Real.log (1 - 1 / q) + Real.log (1 + 1 / q) := by
      rw [← Real.log_mul (by linarith) (by positivity)]
      congr 1; ring
    linarith
  -- the tail
  have htail : ∑' i, a (i + K) ≤ 4 / 3 / x := by
    have hg : Summable fun i : ℕ => 2 / 3 * (1 / q) ^ (K + 1) * (1 / q) ^ i :=
      (summable_geometric_of_lt_one (by positivity) ((div_lt_one hq0).2 hq1)).mul_left _
    have hle : ∀ i, a (i + K) ≤ 2 / 3 * (1 / q) ^ (K + 1) * (1 / q) ^ i := by
      intro i
      simp only [ha]
      obtain ⟨_, h2⟩ := re_pow_bounds hz (i + K + 1)
      have hk3 : (3 : ℝ) ≤ (i + K : ℕ) + 1 := by
        have : (2 : ℝ) ≤ (i + K : ℕ) := by exact_mod_cast (hK2.trans (Nat.le_add_left _ _))
        linarith
      have hpow : (1 / q) ^ (K + 1) * (1 / q) ^ i = 1 / q ^ (i + K + 1) := by
        rw [← pow_add, one_div_pow]; ring_nf
      rw [mul_assoc, hpow]
      have hqp : 0 < q ^ (i + K + 1) := by positivity
      rw [div_le_iff₀ (by positivity)]
      calc 1 + (z ^ (i + K + 1)).re ≤ 2 := h2
        _ ≤ 2 / 3 * (1 / q ^ (i + K + 1)) * (((i + K : ℕ) : ℝ) + 1) * q ^ (i + K + 1) := by
          field_simp
          linarith
        _ = _ := by push_cast; ring
    refine (hs.summable.comp_injective (add_left_injective K)).tsum_le_tsum hle hg |>.trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ((div_lt_one hq0).2 hq1)]
    have hu : (1 / q) ^ (K + 1) ≤ 1 / x := by
      rw [one_div_pow]
      apply one_div_le_one_div_of_le hxr
      rw [hq]; exact_mod_cast hxK.le
    have ht : (1 - 1 / q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by rw [sub_pos]; exact (div_lt_one hq0).2 hq1) (by norm_num)]
      rw [le_sub_comm, div_le_iff₀ hq0]; linarith
    have ht0 : 0 ≤ (1 - 1 / q)⁻¹ := (inv_pos.2 (sub_pos.2 ((div_lt_one hq0).2 hq1))).le
    calc 2 / 3 * (1 / q) ^ (K + 1) * (1 - 1 / q)⁻¹ ≤ 2 / 3 * (1 / x) * 2 := by
          gcongr
      _ = 4 / 3 / x := by ring
  have htail0 : 0 ≤ ∑' i, a (i + K) := by
    refine tsum_nonneg fun i => ?_
    simp only [ha]
    exact div_nonneg (re_pow_bounds hz _).1 (by positivity)
  -- the linear part
  have hlin : ∑ k ∈ Finset.range K, (1 + (z ^ (k + 1)).re) * Real.log q / (x * Real.log x)
      ≤ 2 / x := by
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1.le
    calc _ ≤ ∑ k ∈ Finset.range K, 2 * Real.log q / (x * Real.log x) := by
          refine Finset.sum_le_sum fun k _ => ?_
          gcongr
          exact (re_pow_bounds hz _).2
      _ = 2 * (K * Real.log q) / (x * Real.log x) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 2 * Real.log x / (x * Real.log x) := by
          gcongr
          rw [← Real.log_pow]
          apply Real.log_le_log (by positivity)
          rw [hq]; exact_mod_cast hpK
      _ = 2 / x := by field_simp
  rw [Finset.sum_sub_distrib]
  have : ∑ k ∈ Finset.range K, (1 + (z ^ (k + 1)).re) / ((k + 1) * q ^ (k + 1))
      = ∑ k ∈ Finset.range K, a k := rfl
  rw [this]
  have e : (10 : ℝ) / 3 / x = 4 / 3 / x + 2 / x := by ring
  rw [e]
  linarith


lemma two_le_of_vonMangoldt_ne_zero {n : ℕ} (h : (Λ n : ℝ) ≠ 0) : 2 ≤ n := by
  by_contra hn
  interval_cases n <;> simp at h

/-- `l1Sum1 x + P2sum x / log x = Σ_{n ≤ x} Λ(n) (1/(n log n) − 1/(x log x))`. -/
lemma l1Sum1_add_P2sum (x : ℕ) (hx : 2 ≤ x) :
    l1Sum1 x + P2sum x / Real.log x =
      ∑ n ∈ Finset.range (x + 1),
        (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n) - 1 / ((x : ℝ) * Real.log x)) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hl : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hP : P2sum x = ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) / n * (1 - (n : ℝ) / x) := by
    rw [P2sum, Finset.sum_range_succ, div_self hx0.ne', sub_self, mul_zero, add_zero]
  rw [hP, Finset.sum_div, l1Sum1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : (Λ n : ℝ) = 0
  · simp [h]
  have hn := two_le_of_vonMangoldt_ne_zero h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [Real.log_div hx0.ne' hn0.ne']
  field_simp
  ring


lemma re_Wsum_eq {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) :
    (Wsum χ x).re = ∑ n ∈ Finset.range (x + 1),
      (Λ n : ℝ) * (χ n).re * (1 / ((n : ℝ) * Real.log n) - 1 / ((x : ℝ) * Real.log x)) := by
  rw [Wsum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]


lemma bZ_two (n : ℕ) :
    Robin.bZ 2 n = if n.Prime then -Real.log (1 - 1 / (n : ℝ) ^ 2) else 0 := by
  simp only [Robin.bZ]
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, inv_eq_one_div]

lemma neg_log_one_sub_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) :
    -Real.log (1 - u) ≤ 4 / 3 * u := by
  have hpos : 0 < 1 - u := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have : (1 - u)⁻¹ - 1 ≤ 4 / 3 * u := by
    rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
    nlinarith
  linarith

lemma bZ_two_bounds (n : ℕ) : 0 ≤ Robin.bZ 2 n ∧ Robin.bZ 2 n ≤ 4 / 3 * (1 / (n : ℝ) ^ 2) := by
  rw [bZ_two]
  split_ifs with hn
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hu0 : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have hu1 : 1 / (n : ℝ) ^ 2 ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    refine ⟨?_, neg_log_one_sub_le hu0 hu1⟩
    rw [neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  · exact ⟨le_rfl, by positivity⟩

lemma summable_bZ_two : Summable (Robin.bZ 2) :=
  Summable.of_nonneg_of_le (fun n => (bZ_two_bounds n).1) (fun n => (bZ_two_bounds n).2)
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (4 / 3))

lemma sum_inv_sq_shift_le {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    ∑ i ∈ Finset.range m, 1 / ((i + N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N + m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have key : 1 / ((m + N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (N + m : ℕ) - 1 / (N + (m + 1) : ℕ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma tail_bZ_two_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' i, Robin.bZ 2 (i + (N + 1)) ≤ 4 / 3 / N := by
  refine Real.tsum_le_of_sum_range_le (fun i => (bZ_two_bounds _).1) fun m => ?_
  calc ∑ i ∈ Finset.range m, Robin.bZ 2 (i + (N + 1))
      ≤ ∑ i ∈ Finset.range m, 4 / 3 * (1 / ((i + N + 1 : ℕ) : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [show i + N + 1 = i + (N + 1) by ring]
        exact (bZ_two_bounds _).2
    _ = 4 / 3 * ∑ i ∈ Finset.range m, 1 / ((i + N + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 4 / 3 * (1 / N - 1 / (N + m : ℕ)) := by gcongr; exact sum_inv_sq_shift_le hN m
    _ ≤ 4 / 3 / N := by
        have : 0 ≤ 1 / ((N + m : ℕ) : ℝ) := by positivity
        linarith [show 4 / 3 * (1 / (N : ℝ)) = 4 / 3 / N by ring]

end LLS.Sharp.L51
