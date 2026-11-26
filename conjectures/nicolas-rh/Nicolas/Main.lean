import Nicolas.Statement
import Nicolas.Primorial
import Nicolas.Analytic
import Nicolas.Check.Sound
import Robin.RH.Bach

/-!
# Nicolas' theorem: RH implies `N_k/φ(N_k) > e^γ log log N_k` for every `k ≥ 1`

Write `N_k = q#` with `q = p_k` (`kthPrimorial_succ_eq`). Then `log N_k = θ(q)` and
`N_k/φ(N_k) = exp(Σ_{p≤q} c_p)` (`Nicolas/Primorial.lean`), so the claim is
`e^γ log θ(q) < exp(Σ_{p≤q} c_p)`.

* `q = 2`: `log log 2 < 0`.
* `3 ≤ q ≤ 10^5`: the finite check (`Nicolas.Check.finite_range`, one `native_decide`).
* `q > 10^5`: `γ + log log θ(q) < Σ_{p≤q} c_p` (`sum_cp_gt_large`), which uses RH through
  robin-rh's `psi1NatBound_of_RH`.
-/

namespace Nicolas

open Real Chebyshev Robin

lemma exp_gamma_mul_log_lt {x : ℝ} (hx : 3 ≤ x)
    (h : Real.eulerMascheroniConstant + Real.log (Real.log (θ x)) < primeSum cp x) :
    Real.exp Real.eulerMascheroniConstant * Real.log (θ x) < Real.exp (primeSum cp x) := by
  have hθ := one_lt_theta hx
  have hl : 0 < Real.log (θ x) := Real.log_pos hθ
  have := Real.exp_lt_exp.mpr h
  rwa [Real.exp_add, Real.exp_log hl] at this

/-- **Nicolas' theorem** (1983): under RH, `N_k/φ(N_k) > e^γ log log N_k` for every `k ≥ 1`. -/
theorem nicolas_of_RH (hRH : RiemannHypothesis) : NicolasStatement := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [kthPrimorial_succ_eq]
  set q := Nat.nth Nat.Prime j
  have hq : q.Prime := Nat.prime_nth_prime j
  rw [primorial_div_totient, log_primorial]
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · have hq2 : q = 2 := by have := hq.two_le; omega
    rw [hq2]
    have hθ2 : θ ((2 : ℕ) : ℝ) = Real.log 2 := by
      rw [← log_primorial]; norm_num
    rw [hθ2]
    have hl2 : Real.log (Real.log 2) < 0 := by
      apply Real.log_neg (Real.log_pos (by norm_num))
      have := Real.log_two_lt_d9; linarith
    have : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log 2) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) hl2
    linarith [Real.exp_pos (primeSum cp ((2 : ℕ) : ℝ))]
  rcases Nat.lt_or_ge q 100001 with hqB | hqB
  · exact Check.finite_range hq hq3 (by omega)
  · apply exp_gamma_mul_log_lt (by exact_mod_cast hq3)
    apply sum_cp_gt_large (psi1NatBound_of_RH hRH)
    have : (100001 : ℝ) ≤ q := by exact_mod_cast hqB
    linarith

end Nicolas
