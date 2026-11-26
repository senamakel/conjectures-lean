import Mertens.Littlewood

/-!
# Step G: discrete Abel summation against a weight

With `S(n) = ∑_{k ≤ n} c(k)`, `∑_{n ≤ N} c(n) w(n) = S(N) w(N) - ∑_{n < N} S(n) (w(n+1) - w(n))`.
If `|S(n)| ≤ K (n+1)^β`, the partial sums of `(n+1)^β |w(n+1) - w(n)|` are at most `B`, and
`(n+1)^β w(n) → 0`, then `∑ c(n) w(n)` converges and its sum is at most `K B` in absolute value.

The weight differences are bounded by interpolating two mean-value bounds
(`le_rpow_mul_rpow`), which turns `min(A x^{p₁} n^{q₁}, B x^{p₂} n^{q₂})` into a single
monomial `x^P n^{-(1+η)}`; the sum over `n` is then at most `x^P ζ(1+η)`.
-/

namespace Mertens

open Filter Topology Finset

/-- Abel's summation identity. -/
lemma abel_identity (c w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), c n * w n =
      (∑ k ∈ range (N + 1), c k) * w N -
        ∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun n => (∑ k ∈ range (n + 1), c k) *
      (w (n + 1) - w n)), sum_range_succ c (N + 1)]
    ring

/-- **Abel summation bound.** -/
theorem abel_tendsto {c w : ℕ → ℝ} {K β B : ℝ} (hK : 0 ≤ K)
    (hS : ∀ n : ℕ, |∑ k ∈ range (n + 1), c k| ≤ K * ((n : ℝ) + 1) ^ β)
    (hB : ∀ N : ℕ, ∑ n ∈ range N, ((n : ℝ) + 1) ^ β * |w (n + 1) - w n| ≤ B)
    (hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ β * |w n|) atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ range N, c n * w n) atTop (𝓝 L) ∧ |L| ≤ K * B := by
  set a : ℕ → ℝ := fun n => (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n) with ha
  have hpow : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ β := fun n => by positivity
  have habs : ∀ n, |a n| ≤ K * (((n : ℝ) + 1) ^ β * |w (n + 1) - w n|) := fun n => by
    rw [ha]; simp only
    rw [abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hS n) (abs_nonneg _)
  have hsumabs : ∀ N, ∑ n ∈ range N, |a n| ≤ K * B := fun N =>
    (sum_le_sum fun n _ => habs n).trans (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hB N) hK)
  have hsa : Summable fun n => |a n| := summable_of_sum_range_le (fun n => abs_nonneg _) hsumabs
  have hs : Summable a := hsa.of_abs
  refine ⟨-∑' n, a n, ?_, ?_⟩
  · rw [← tendsto_add_atTop_iff_nat 1]
    have h1 : Tendsto (fun N : ℕ => (∑ k ∈ range (N + 1), c k) * w N) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun N => ?_) (by simpa using hlim.const_mul K)
      rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hS N) (abs_nonneg _)
    have h2 := hs.hasSum.tendsto_sum_nat
    have := h1.sub h2
    rw [zero_sub] at this
    refine this.congr fun N => ?_
    rw [abel_identity]
  · rw [abs_neg]
    have hsa' : Summable fun n => ‖a n‖ := by
      simp_rw [Real.norm_eq_abs]; exact hsa
    have h := norm_tsum_le_tsum_norm hsa'
    simp_rw [Real.norm_eq_abs] at h
    calc |∑' n, a n| ≤ ∑' n, |a n| := h
      _ ≤ K * B := Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hsumabs

/-- Monomial algebra: `(c x^p n^q)^θ = c^θ x^{pθ} n^{qθ}`. -/
lemma monomial_rpow {c x n p q θ : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hn : 0 < n) :
    (c * x ^ p * n ^ q) ^ θ = c ^ θ * x ^ (p * θ) * n ^ (q * θ) := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hc (by positivity),
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hn.le]

/-- Interpolation of two monomial bounds on `|Δ|`, with the factor `(n+1)^β ≤ 2 n^β`. -/
lemma interp_term {Δ D₁ D₂ p₁ q₁ p₂ q₂ θ β x : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx : 0 < x)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h₁ : |Δ| ≤ D₁ * x ^ p₁ * (n : ℝ) ^ q₁) (h₂ : |Δ| ≤ D₂ * x ^ p₂ * (n : ℝ) ^ q₂) :
    ((n : ℝ) + 1) ^ β * |Δ| ≤
      2 * D₁ ^ θ * D₂ ^ (1 - θ) * x ^ (p₁ * θ + p₂ * (1 - θ)) *
        (n : ℝ) ^ (β + (q₁ * θ + q₂ * (1 - θ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hI := le_rpow_mul_rpow (by positivity) (by positivity) h₁ h₂ hθ0 hθ1
  rw [monomial_rpow hD₁ hx hn0, monomial_rpow hD₂ hx hn0] at hI
  have hpow : ((n : ℝ) + 1) ^ β ≤ 2 * (n : ℝ) ^ β := by
    calc ((n : ℝ) + 1) ^ β ≤ (2 * (n : ℝ)) ^ β :=
          Real.rpow_le_rpow (by positivity) (by linarith [(by exact_mod_cast hn : (1 : ℝ) ≤ n)]) hβ0
      _ = 2 ^ β * (n : ℝ) ^ β := Real.mul_rpow (by norm_num) hn0.le
      _ ≤ 2 * (n : ℝ) ^ β := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num) hβ1
  calc ((n : ℝ) + 1) ^ β * |Δ| ≤ (2 * (n : ℝ) ^ β) *
        (D₁ ^ θ * x ^ (p₁ * θ) * (n : ℝ) ^ (q₁ * θ) *
          (D₂ ^ (1 - θ) * x ^ (p₂ * (1 - θ)) * (n : ℝ) ^ (q₂ * (1 - θ)))) :=
        mul_le_mul hpow hI (abs_nonneg _) (by positivity)
    _ = 2 * D₁ ^ θ * D₂ ^ (1 - θ) * (x ^ (p₁ * θ) * x ^ (p₂ * (1 - θ))) *
          ((n : ℝ) ^ β * ((n : ℝ) ^ (q₁ * θ) * (n : ℝ) ^ (q₂ * (1 - θ)))) := by ring
    _ = _ := by
        rw [← Real.rpow_add hx, ← Real.rpow_add hn0, ← Real.rpow_add hn0]

/-- Partial sums of `A x^P n^{-(1+η)}` over `n ≥ 1`, plus a term at `n = 0`. -/
lemma sum_range_le_of_terms {f : ℕ → ℝ} {A₀ A P η x : ℝ} (hη : 0 < η) (hA : 0 ≤ A)
    (hx : 0 < x) (hA₀ : 0 ≤ A₀)
    (h0 : f 0 ≤ A₀) (hf : ∀ n, 1 ≤ n → f n ≤ A * x ^ P * (n : ℝ) ^ (-(1 + η))) (N : ℕ) :
    ∑ n ∈ range N, f n ≤
      A₀ + A * x ^ P * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + η)) := by
  have hZ : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 + η)) := by
    have := Real.summable_nat_rpow.2 (show -(1 + η) < -1 by linarith)
    have := (summable_nat_add_iff 1).2 this
    simpa using this
  have hZ0 : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + η)) := tsum_nonneg fun n => by positivity
  have hxP : 0 ≤ x ^ P := by positivity
  rcases N with _ | N
  · simp only [range_zero, sum_empty]
    positivity
  · rw [sum_range_succ']
    have h1 : ∑ i ∈ range N, f (i + 1) ≤ ∑ i ∈ range N, A * x ^ P * ((i : ℝ) + 1) ^ (-(1 + η)) :=
      sum_le_sum fun i _ => by
        have := hf (i + 1) (by omega)
        simpa using this
    have h2 : ∑ i ∈ range N, ((i : ℝ) + 1) ^ (-(1 + η)) ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + η)) :=
      hZ.sum_le_tsum _ (fun i _ => by positivity)
    rw [← mul_sum] at h1
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ A * x ^ P by positivity)
    linarith

end Mertens
