import Mertens.Littlewood

/-!
# Step F: assembly of Littlewood's theorem `RH ⇒ M(x) = O(x^{1/2+ε})`
-/

namespace Mertens

open Complex MeasureTheory Filter Set Topology Asymptotics

/-- Under RH, for `0 < ε ≤ 1/4`: `|M(N)| ≤ K (N+1)^{1/2+3ε}` for all `N ≥ 1`. -/
theorem abs_mertens_nat_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N →
      |(mertens N : ℝ)| ≤ K * ((N : ℝ) + 1) ^ (1 / 2 + 3 * ε) := by
  set σ₀ : ℝ := 1 / 2 + ε with hσ₀
  have h1 : 1 / 2 < σ₀ := by linarith
  have h2 : σ₀ < 2 := by linarith
  obtain ⟨K, hK0, hK⟩ := norm_diff_F_le hRH hε (by linarith) (θ := 2 * ε) (by linarith)
    (by linarith) h1 h2
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(1 + ε)) with hJ
  have hint : Integrable fun t : ℝ => (1 + |t|) ^ (-(1 + ε)) := by
    simpa using Erdos985.Analytic.PerronAux.integrable_one_add_abs_rpow
      (show (1 : ℝ) < 1 + ε by linarith) 0
  have hJ0 : 0 ≤ J := integral_nonneg fun t => by positivity
  refine ⟨1 / (2 * Real.pi) * K * J + 1, by positivity, fun N hN => ?_⟩
  have hpos : ∀ M : ℕ, 1 ≤ M → (0 : ℝ) < M := fun M hM => by exact_mod_cast hM
  have e := mertens_nat_eq N
  have hi1 : Integrable fun t : ℝ =>
      ((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) :=
    (integrable_F_line hRH (hpos _ (by omega)) h1 h2 le_rfl h2.le).const_mul _
  have hi2 : Integrable fun t : ℝ => (N : ℂ) * F N ((σ₀ : ℂ) + t * I) :=
    (integrable_F_line hRH (hpos _ hN) h1 h2 le_rfl h2.le).const_mul _
  rw [cesA_eq hRH h1 h2 (N + 1) (by omega), cesA_eq hRH h1 h2 N hN, ← mul_sub,
    ← integral_sub hi1 hi2] at e
  have hnorm : |(mertens N : ℝ)| = ‖((mertens N : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
  set β : ℝ := 1 / 2 + 3 * ε
  have hβ : σ₀ + 2 * ε = β := by rw [hσ₀]; ring
  have hexp : ε - 2 * ε - 1 = -(1 + ε) := by ring
  have hbound : ‖∫ t : ℝ, (((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
      (N : ℂ) * F N ((σ₀ : ℂ) + t * I))‖ ≤ K * ((N : ℝ) + 1) ^ β * J := by
    rw [hJ, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun t => ?_)
    have := hK N hN t
    rwa [hβ, hexp] at this
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hnorm, e, norm_mul, hpi]
  have hP : 0 ≤ ((N : ℝ) + 1) ^ β := by positivity
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, (((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
        (N : ℂ) * F N ((σ₀ : ℂ) + t * I))‖
      ≤ 1 / (2 * Real.pi) * (K * ((N : ℝ) + 1) ^ β * J) := by gcongr
    _ = (1 / (2 * Real.pi) * K * J) * ((N : ℝ) + 1) ^ β := by ring
    _ ≤ (1 / (2 * Real.pi) * K * J + 1) * ((N : ℝ) + 1) ^ β := by nlinarith

/-- **Littlewood (1912)**: under RH, `M(x) = O(x^{1/2+ε})` for every `ε > 0`. -/
theorem mertens_of_RH (hRH : RiemannHypothesis) : MertensBound := by
  intro ε' hε'
  set ε := min (ε' / 3) (1 / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε3 : 3 * ε ≤ ε' := by have := min_le_left (ε' / 3) (1 / 4); linarith
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  obtain ⟨K, hK0, hK⟩ := abs_mertens_nat_le hRH hε0 hε4
  refine IsBigO.of_bound (4 * K) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hm : mertens x = mertens (N : ℝ) := by
    rw [mertens, mertens, Nat.floor_natCast]
  set β : ℝ := 1 / 2 + 3 * ε with hβdef
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _), hm]
  have h1 := hK N hN
  have h2 : ((N : ℝ) + 1) ^ β ≤ (2 * x) ^ β :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have h3 : (2 * x) ^ β = 2 ^ β * x ^ β := Real.mul_rpow (by norm_num) hx0.le
  have h4 : (2 : ℝ) ^ β ≤ 4 := by
    calc (2 : ℝ) ^ β ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hβdef]; linarith)
      _ = 4 := by norm_num
  have h5 : x ^ β ≤ x ^ (1 / 2 + ε') := Real.rpow_le_rpow_of_exponent_le hx (by rw [hβdef]; linarith)
  have hxβ : 0 ≤ x ^ β := by positivity
  calc |(mertens (N : ℝ) : ℝ)| ≤ K * ((N : ℝ) + 1) ^ β := h1
    _ ≤ K * (2 ^ β * x ^ β) := by rw [← h3]; gcongr
    _ ≤ K * (4 * x ^ (1 / 2 + ε')) := by gcongr
    _ = 4 * K * x ^ (1 / 2 + ε') := by ring

end Mertens
