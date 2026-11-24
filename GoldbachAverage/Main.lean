import GoldbachAverage.Sum
import Schoenfeld.Main

/-!
# The average number of Goldbach representations under RH

Under Mathlib's `RiemannHypothesis`:

* `goldbachAverageSharp_of_RH : GoldbachAverageSharp 4000`:
  `|Σ_{n ≤ x} G(n) − x²/2| ≤ 4000 x^{3/2} log² x` for `x ≥ 2`;
* `goldbachAverage_of_RH : GoldbachAverageBound`: `Σ_{n ≤ x} G(n) = x²/2 + O(x^{3/2+ε})`.

Route: `S(N) = Σ_a Λ(a) ψ(N − a)`, and `Σ_a Λ(a)(N − a) = Σ_{k<N} ψ(k)`. Writing
`ψ(u) = u + e(u)` with `|e(u)| ≤ (1/8)√N log² N + 400` for `u ≤ N` (Schoenfeld's
`psiBound_of_RH` from `u ≥ 74`, Chebyshev's `ψ ≤ 5.4 u` below), the main term is `N²/2` and the
error is at most `N/2 + 6.4 N · max |e|`.
-/

namespace GoldbachAverage

open ArithmeticFunction Chebyshev Filter Asymptotics

lemma log_four_le : Real.log 4 ≤ 1.4 := by
  have h := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  linarith

/-- `ψ(u) ≤ 5.4 u`. -/
lemma psi_le_five (u : ℝ) (hu : 0 ≤ u) : ψ u ≤ 5.4 * u := by
  refine (psi_le_const_mul_self hu).trans ?_
  have := log_four_le
  nlinarith

/-- The uniform bound on `e(k) = ψ(k) − k` for `k ≤ N`. -/
lemma abs_psi_sub_le (hRH : RiemannHypothesis) (N k : ℕ) (hk : k ≤ N) :
    |ψ (k : ℝ) - k| ≤ 1 / 8 * (Real.sqrt N * Real.log N ^ 2) + 400 := by
  have hpos : 0 ≤ 1 / 8 * (Real.sqrt N * Real.log N ^ 2) := by positivity
  by_cases h : (k : ℝ) < 73.2
  · have h1 : ψ (k : ℝ) ≤ 5.4 * k := psi_le_five _ (Nat.cast_nonneg _)
    have h2 := psi_nonneg (k : ℝ)
    rw [abs_le]
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · rw [not_lt] at h
    have := Schoenfeld.psiBound_of_RH hRH (k : ℝ) h
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by linarith
    have hs : Real.sqrt k ≤ Real.sqrt N := Real.sqrt_le_sqrt hkN
    have hl0 : 0 ≤ Real.log k := Real.log_nonneg hk1
    have hl : Real.log k ≤ Real.log N := Real.log_le_log (by linarith) hkN
    have hl2 : Real.log k ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ hl0 hl 2
    have : Real.sqrt k * Real.log k ^ 2 ≤ Real.sqrt N * Real.log N ^ 2 :=
      mul_le_mul hs hl2 (by positivity) (Real.sqrt_nonneg _)
    linarith

lemma sum_range_cast (N : ℕ) : ∑ k ∈ Finset.range N, (k : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem goldbach_sharp_nat (hRH : RiemannHypothesis) (N : ℕ) (hN : 2 ≤ N) :
    |goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2| ≤
      3900 * ((N : ℝ) * Real.sqrt N * Real.log N ^ 2) := by
  set Bd : ℝ := 1 / 8 * (Real.sqrt N * Real.log N ^ 2) + 400 with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  set e : ℕ → ℝ := fun k => ψ (k : ℝ) - k with he
  have hE : ∀ k ≤ N, |e k| ≤ Bd := fun k hk => abs_psi_sub_le hRH N k hk
  -- decomposition
  have hS : goldbachSum (N : ℝ) =
      ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ((N : ℝ) - a) +
        ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a) := by
    rw [goldbachSum_eq_convolution, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have haN : a ≤ N := by simpa [Nat.lt_succ_iff] using ha
    simp only [he, Nat.cast_sub haN]
    ring
  have hA : ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ((N : ℝ) - a) =
      (N : ℝ) * (N - 1) / 2 + ∑ k ∈ Finset.range N, e k := by
    rw [sum_vonMangoldt_mul_sub, ← sum_range_cast, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [he]
  have h1 : |∑ k ∈ Finset.range N, e k| ≤ N * Bd := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range N, |e k| ≤ ∑ _k ∈ Finset.range N, Bd :=
          Finset.sum_le_sum fun k hk => hE k (Finset.mem_range.mp hk).le
      _ = N * Bd := by simp
  have h2 : |∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a)| ≤ 5.4 * N * Bd := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a ∈ Finset.range (N + 1), |(Λ a : ℝ) * e (N - a)|
        ≤ ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * Bd := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Λ a)]
          exact mul_le_mul_of_nonneg_left (hE _ (Nat.sub_le _ _)) (by positivity)
      _ = ψ (N : ℝ) * Bd := by rw [← Finset.sum_mul, psi_natCast]
      _ ≤ 5.4 * N * Bd := by
          exact mul_le_mul_of_nonneg_right (psi_le_five _ (Nat.cast_nonneg _)) hBd0
  have hS' : goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2 =
      -(N : ℝ) / 2 + ∑ k ∈ Finset.range N, e k +
        ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a) := by
    rw [hS, hA]; ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (1.41 : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le; linarith
  have hl : (0.69 : ℝ) ≤ Real.log N := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    linarith
  have hl2 : (0.4761 : ℝ) ≤ Real.log N ^ 2 := by nlinarith
  have hP : (0.67 : ℝ) ≤ Real.sqrt N * Real.log N ^ 2 := by nlinarith
  have hNpos : (0 : ℝ) ≤ N := by positivity
  rw [hS']
  have habs : |-(N : ℝ) / 2| = N / 2 := by
    rw [abs_div, abs_neg, abs_of_nonneg hNpos]; norm_num
  calc _ ≤ |-(N : ℝ) / 2| + |∑ k ∈ Finset.range N, e k| +
        |∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a)| := abs_add_three _ _ _
    _ ≤ N / 2 + N * Bd + 5.4 * N * Bd := by rw [habs]; linarith
    _ ≤ _ := by
      rw [hBd]
      set P := Real.sqrt N * Real.log N ^ 2 with hPdef
      have : (N : ℝ) * P ≥ 0.67 * N := by nlinarith
      nlinarith

/-- `|Σ_{n ≤ x} G(n) − x²/2| ≤ 4000 x^{3/2} log² x` for `x ≥ 2`, under RH. -/
theorem goldbachAverageSharp_of_RH (hRH : RiemannHypothesis) : GoldbachAverageSharp 4000 := by
  intro x hx
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hN : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hS : goldbachSum x = goldbachSum (N : ℝ) := by
    unfold goldbachSum; rw [Nat.floor_natCast]
  have h := goldbach_sharp_nat hRH N hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : (1.41 : ℝ) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le; linarith
  have hl : (0.69 : ℝ) ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    linarith
  have hl2 : (0.4761 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
  have hP : (0.67 : ℝ) ≤ Real.sqrt x * Real.log x ^ 2 := by nlinarith
  have hQ : (N : ℝ) * Real.sqrt N * Real.log N ^ 2 ≤ x * Real.sqrt x * Real.log x ^ 2 := by
    have h1 : Real.sqrt N ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
    have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have h2 : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) hNx
    have h3 : Real.log N ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ hl0 h2 2
    have hx0 : (0 : ℝ) ≤ x := by linarith
    calc (N : ℝ) * Real.sqrt N * Real.log N ^ 2 ≤ x * Real.sqrt x * Real.log N ^ 2 := by
          gcongr
      _ ≤ _ := by gcongr
  have hx1 : x ≤ x * (Real.sqrt x * Real.log x ^ 2) * (100 / 67) := by
    nlinarith
  have hdiff : |(N : ℝ) ^ 2 / 2 - x ^ 2 / 2| ≤ x := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [hS]
  calc |goldbachSum (N : ℝ) - x ^ 2 / 2|
      = |(goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2) + ((N : ℝ) ^ 2 / 2 - x ^ 2 / 2)| := by ring_nf
    _ ≤ |goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2| + |(N : ℝ) ^ 2 / 2 - x ^ 2 / 2| := abs_add_le _ _
    _ ≤ 3900 * (x * Real.sqrt x * Real.log x ^ 2) + x * (Real.sqrt x * Real.log x ^ 2) * (100 / 67) := by
        linarith
    _ ≤ _ := by
        have hxP : 0 ≤ x * (Real.sqrt x * Real.log x ^ 2) := by
          have : (0 : ℝ) ≤ x := by linarith
          have : (0 : ℝ) ≤ Real.sqrt x * Real.log x ^ 2 := by linarith
          positivity
        have e : x * Real.sqrt x * Real.log x ^ 2 = x * (Real.sqrt x * Real.log x ^ 2) := by ring
        rw [e]
        linarith

/-- The target: `Σ_{n ≤ x} G(n) = x²/2 + O(x^{3/2+ε})` for every `ε > 0`, under RH. -/
theorem goldbachAverage_of_RH (hRH : RiemannHypothesis) : GoldbachAverageBound := by
  intro ε hε
  have hsharp := goldbachAverageSharp_of_RH hRH
  have h1 : (fun x : ℝ => goldbachSum x - x ^ 2 / 2) =O[atTop]
      fun x : ℝ => x * Real.sqrt x * Real.log x ^ 2 := by
    refine IsBigO.of_bound 4000 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    have hnn : 0 ≤ x * Real.sqrt x * Real.log x ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hsharp x hx
  have h2 : (fun x : ℝ => x ^ ((3 : ℝ) / 2) * Real.log x ^ (2 : ℝ)) =O[atTop]
      fun x : ℝ => x ^ ((3 : ℝ) / 2) * x ^ ε :=
    (isBigO_refl _ _).mul (isLittleO_log_rpow_rpow_atTop 2 hε).isBigO
  have h3 : (fun x : ℝ => x * Real.sqrt x * Real.log x ^ 2) =ᶠ[atTop]
      fun x : ℝ => x ^ ((3 : ℝ) / 2) * Real.log x ^ (2 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_two, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
      Real.rpow_one, Real.sqrt_eq_rpow]
  have h4 : (fun x : ℝ => x ^ ((3 : ℝ) / 2) * x ^ ε) =ᶠ[atTop]
      fun x : ℝ => x ^ ((3 : ℝ) / 2 + ε) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_add hx]
  exact h1.trans ((h3.trans_isBigO h2).trans (h4.isBigO))

end GoldbachAverage
