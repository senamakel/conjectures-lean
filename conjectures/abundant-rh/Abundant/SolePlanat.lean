import Abundant.Statement

/-!
# Solé–Planat from Nicolas' inequality

Solé–Planat, Proposition 5 and Theorem 1: for every `n ≥ 1`,
`φ(n) Ψ(n) = n² ∏_{p ∣ n} (1 − p⁻²) ≥ n²/ζ(2)`, so
`R(N) = (N/φ(N)) ∏_{p ∣ N}(1 − p⁻²) / log log N > e^γ/ζ(2)` whenever Nicolas' inequality
`N/φ(N) > e^γ log log N` holds at `N`.

The bound `∏_{p ∈ s} (1 − p⁻²)⁻¹ ≤ ζ(2)` is Mathlib's Euler product for the completely
multiplicative function `n ↦ n⁻²` over the `s`-factored numbers, compared with `∑ n⁻² = π²/6`.
-/

namespace Abundant

open Real Finset

/-- `ζ(2) = π²/6`, real part. -/
lemma riemannZeta_two_re : (riemannZeta 2).re = π ^ 2 / 6 := by
  rw [riemannZeta_two]
  have : ((π : ℂ) ^ 2 / 6) = ((π ^ 2 / 6 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- The completely multiplicative function `n ↦ n⁻²`. -/
noncomputable def invSq : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_pow, mul_inv]

lemma invSq_apply (n : ℕ) : invSq n = ((n : ℝ) ^ 2)⁻¹ := rfl

lemma summable_invSq : Summable (fun n : ℕ ↦ invSq n) := by
  have := hasSum_zeta_two.summable
  simpa [invSq_apply, one_div] using this

lemma tsum_invSq : ∑' n : ℕ, invSq n = π ^ 2 / 6 := by
  have := hasSum_zeta_two.tsum_eq
  simpa [invSq_apply, one_div] using this

/-- Finite Euler product of `ζ(2)`: `∏_{p ∈ s prime} (1 − p⁻²)⁻¹ ≤ π²/6`. -/
lemma prod_inv_one_sub_invSq_le (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, (1 - invSq p)⁻¹ ≤ π ^ 2 / 6 := by
  rw [EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers summable_invSq s,
    ← tsum_invSq]
  exact summable_invSq.tsum_subtype_le (fun n ↦ invSq n) _ (fun n ↦ by
    rw [invSq_apply]; positivity)

lemma one_sub_invSq_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - invSq p := by
  rw [invSq_apply, sub_pos]
  have : (1 : ℝ) < (p : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  exact inv_lt_one_of_one_lt₀ this

/-- `∏_{p ∣ n} (1 − p⁻²) ≥ 1/ζ(2) = 6/π²`. -/
lemma inv_pi_sq_le_prod (n : ℕ) :
    (π ^ 2 / 6)⁻¹ ≤ ∏ p ∈ n.primeFactors, (1 - invSq p) := by
  have hfilt : (n.primeFactors.filter Nat.Prime) = n.primeFactors :=
    Finset.filter_true_of_mem fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have h := prod_inv_one_sub_invSq_le n.primeFactors
  rw [hfilt, Finset.prod_inv_distrib] at h
  have hP : 0 < ∏ p ∈ n.primeFactors, (1 - invSq p) :=
    Finset.prod_pos fun p hp ↦ one_sub_invSq_pos (Nat.prime_of_mem_primeFactors hp)
  exact inv_le_of_inv_le₀ hP h

/-- Euler's product for `φ`, over `ℝ`. -/
lemma totient_eq_mul_prod_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at this
  exact this

/-- Solé–Planat, Proposition 5: `φ(n) Ψ(n) = n² ∏_{p ∣ n} (1 − p⁻²)`. -/
lemma totient_mul_dedekindPsi (n : ℕ) :
    (Nat.totient n : ℝ) * dedekindPsi n = (n : ℝ) ^ 2 * ∏ p ∈ n.primeFactors, (1 - invSq p) := by
  rw [totient_eq_mul_prod_real, dedekindPsi]
  have : ∏ p ∈ n.primeFactors, (1 - invSq p)
      = (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [invSq_apply]; ring
  rw [this]; ring

/-- The `k`-th primorial is at least `2^k`. -/
lemma two_pow_le_kthPrimorial (k : ℕ) : 2 ^ k ≤ Nicolas.kthPrimorial k := by
  unfold Nicolas.kthPrimorial
  have := Finset.pow_card_le_prod (Finset.range k) (fun i ↦ Nat.nth Nat.Prime i) 2
    (fun i _ ↦ (Nat.prime_nth_prime i).two_le)
  simpa using this

/-- Nicolas' inequality at one `N ≥ 3` implies Solé–Planat's at `N`. -/
lemma solePlanat_of_nicolas_at {N : ℕ} (hN : 3 ≤ N)
    (h : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N)
      < (N : ℝ) / (Nat.totient N : ℝ)) :
    Real.exp Real.eulerMascheroniConstant / (riemannZeta 2).re < solePlanatRatio N := by
  set g := Real.exp Real.eulerMascheroniConstant
  set L := Real.log (Real.log N)
  set P := ∏ p ∈ N.primeFactors, (1 - invSq p)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hφ : (0 : ℝ) < Nat.totient N := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hL : 0 < L := by
    apply Real.log_pos
    have : Real.exp 1 < N := by
      have := Real.exp_one_lt_d9
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log N := Real.log_lt_log (Real.exp_pos 1) this
  have hP : 0 < P :=
    Finset.prod_pos fun p hp ↦ one_sub_invSq_pos (Nat.prime_of_mem_primeFactors hp)
  have hg : 0 < g := Real.exp_pos _
  have hpsi : dedekindPsi N = (N : ℝ) ^ 2 * P / Nat.totient N := by
    rw [eq_div_iff hφ.ne', mul_comm, totient_mul_dedekindPsi]
  have hR : solePlanatRatio N = ((N : ℝ) / Nat.totient N) * P / L := by
    rw [solePlanatRatio, hpsi]
    field_simp
  rw [hR, riemannZeta_two_re]
  have h1 : g / (π ^ 2 / 6) ≤ g * P := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_pi_sq_le_prod N) hg.le
  have h2 : g * P < ((N : ℝ) / Nat.totient N) * P / L := by
    rw [lt_div_iff₀ hL]
    have := mul_lt_mul_of_pos_right h hP
    linarith [this]
  linarith

/-- **Solé–Planat** from Nicolas' inequality (their Theorem 1, the RH direction). -/
theorem solePlanat_of_nicolas (h : Nicolas.NicolasStatement) : SolePlanatStatement := by
  intro n hn
  have hN : 3 ≤ Nicolas.kthPrimorial n := by
    have := two_pow_le_kthPrimorial n
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  exact solePlanat_of_nicolas_at hN (h n (by omega))

end Abundant
