import Mathlib

/-!
# Mertens' first theorem (von Mangoldt form) and prime-reciprocal sums over blocks

* `abs_R_sub_log_le`: `|Σ_{n ≤ N} Λ(n)/n - log N| ≤ log 4 + 4` for `N ≥ 1`.
  Proof: `Σ_{n ≤ N} log n = Σ_{d ≤ N} Λ(d) ⌊N/d⌋` (the Dirichlet identity `Λ * ζ = log`, as in
  the Mertens file of T. Tao et al., mathlib4 PR #41394), Stirling's lower bound for `log N!`,
  `log N! ≤ N log N` and Chebyshev's `ψ(N) ≤ (log 4 + 4) N` (Mathlib).
* `sum_inv_shell_le'`: for a set `S` of primes in `(2^u, 2^v]`,
  `Σ_{ℓ∈S} 1/ℓ ≤ ((v - u) log 2 + 2 C₀) / (u log 2)`, `C₀ = log 4 + 4`.
* `sum_inv_blockM_le`: splitting `(2^u, 2^v]` into shells of width `w`,
  `Σ_{ℓ∈S} 1/ℓ ≤ log (v/u) + w (v - u) / (2 u²) + ((v - u)/w + 1) · 2 C₀/(u log 2)`.
-/

namespace Shoup.Sieve

open Finset Real ArithmeticFunction Chebyshev

/-- The constant in Mertens' first theorem as proved here. -/
noncomputable def C₀ : ℝ := Real.log 4 + 4

lemma C₀_pos : 0 < C₀ := by
  unfold C₀; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith

/-- `R N = Σ_{0 < n ≤ N} Λ(n)/n`. -/
noncomputable def R (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, (Λ n : ℝ) / n

lemma sum_log_eq_sum_vonMangoldt (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n = ∑ d ∈ Ioc 0 N, (Λ d : ℝ) * ((N / d : ℕ) : ℝ) := by
  have h := sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
  rw [vonMangoldt_mul_zeta] at h
  simpa using h

lemma R_le (N : ℕ) (hN : 1 ≤ N) : R N ≤ Real.log N + C₀ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * R N ≤ ∑ n ∈ Ioc 0 N, Real.log n + ∑ d ∈ Ioc 0 N, (Λ d : ℝ) := by
    rw [sum_log_eq_sum_vonMangoldt, R, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hΛ : (0 : ℝ) ≤ Λ d := vonMangoldt_nonneg
    -- `N/d ≤ ⌊N/d⌋ + 1`
    have hfl : (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := N) hd0
      rw [div_le_iff₀ hdR]
      have : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      linarith
    calc (N : ℝ) * ((Λ d : ℝ) / d) = (Λ d : ℝ) * ((N : ℝ) / d) := by ring
      _ ≤ (Λ d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hfl hΛ
      _ = _ := by ring
  have h2 : ∑ n ∈ Ioc 0 N, Real.log n ≤ N * Real.log N := by
    have := Real.sum_log_le' (x := (N : ℝ)) (by exact_mod_cast hN)
    simpa using this
  have h3 : ∑ d ∈ Ioc 0 N, (Λ d : ℝ) ≤ (Real.log 4 + 4) * N := by
    -- direct bound: `Σ_{d ≤ N} Λ d = ψ N ≤ (log 4 + 4) N`
    have hψ := psi_le_const_mul_self (x := (N : ℝ)) hNR.le
    have hψeq : ψ (N : ℝ) = ∑ d ∈ Ioc 0 N, (Λ d : ℝ) := by
      rw [Chebyshev.psi]; simp
    linarith
  have : (N : ℝ) * R N ≤ N * (Real.log N + C₀) := by
    unfold C₀; nlinarith
  exact le_of_mul_le_mul_left this hNR

lemma le_R (N : ℕ) (hN : 1 ≤ N) : Real.log N - 1 ≤ R N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ n ∈ Ioc 0 N, Real.log n ≤ (N : ℝ) * R N := by
    rw [sum_log_eq_sum_vonMangoldt, R, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hΛ : (0 : ℝ) ≤ Λ d := vonMangoldt_nonneg
    have hfl : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
      rw [le_div_iff₀ hdR]; exact_mod_cast Nat.div_mul_le_self N d
    calc (Λ d : ℝ) * ((N / d : ℕ) : ℝ) ≤ (Λ d : ℝ) * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left hfl hΛ
      _ = (N : ℝ) * ((Λ d : ℝ) / d) := by ring
  have h2 : (N : ℝ) * Real.log N - N ≤ ∑ n ∈ Ioc 0 N, Real.log n := by
    rw [sum_log_eq_log_factorial]
    have := Stirling.le_log_factorial_stirling (n := N) (by omega)
    have h0 : 0 ≤ Real.log N / 2 := by
      have := Real.log_natCast_nonneg N; linarith
    have hπ : 0 ≤ Real.log (2 * π) / 2 := by
      have : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
      have := Real.log_nonneg this; linarith
    linarith
  have : (N : ℝ) * (Real.log N - 1) ≤ N * R N := by nlinarith
  exact le_of_mul_le_mul_left this hNR

theorem abs_R_sub_log_le (N : ℕ) (hN : 1 ≤ N) : |R N - Real.log N| ≤ C₀ := by
  have := R_le N hN
  have := le_R N hN
  rw [abs_le]
  constructor <;> [skip; linarith]
  unfold C₀
  have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

lemma R_sub_R_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    R b - R a ≤ Real.log b - Real.log a + 2 * C₀ := by
  have h1 := abs_le.mp (abs_R_sub_log_le b (ha.trans hab))
  have h2 := abs_le.mp (abs_R_sub_log_le a ha)
  linarith [h1.2, h2.1]

lemma R_sub_R_eq {a b : ℕ} (hab : a ≤ b) :
    R b - R a = ∑ n ∈ Ioc a b, (Λ n : ℝ) / n := by
  unfold R
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

/-- Prime reciprocals in a shell `(2^u, 2^v]`. -/
theorem sum_inv_shell_le' (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (u v : ℕ) (hu : 1 ≤ u)
    (huv : u ≤ v) (hrange : ∀ ℓ ∈ S, 2 ^ u < ℓ ∧ ℓ ≤ 2 ^ v) :
    ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ ((v - u : ℝ) * Real.log 2 + 2 * C₀) / (u * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  set c : ℝ := u * Real.log 2 with hc
  have hcpos : 0 < c := by positivity
  have hpow : 2 ^ u ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) huv
  have hsub : S ⊆ Ioc (2 ^ u) (2 ^ v) := fun ℓ h => Finset.mem_Ioc.mpr (hrange ℓ h)
  have hterm : ∀ ℓ ∈ S, (1 : ℝ) / ℓ ≤ ((Λ ℓ : ℝ) / ℓ) / c := by
    intro ℓ h
    have hℓ := hS ℓ h
    have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
    rw [vonMangoldt_apply_prime hℓ]
    have : c ≤ Real.log ℓ := by
      rw [hc, ← Real.log_pow]
      refine Real.log_le_log (by positivity) ?_
      exact_mod_cast (hrange ℓ h).1.le
    rw [div_div, div_le_div_iff₀ hℓR (by positivity)]
    nlinarith
  calc ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ ∑ ℓ ∈ S, ((Λ ℓ : ℝ) / ℓ) / c := Finset.sum_le_sum hterm
    _ = (∑ ℓ ∈ S, (Λ ℓ : ℝ) / ℓ) / c := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Ioc (2 ^ u) (2 ^ v), (Λ n : ℝ) / n) / c := by
        refine div_le_div_of_nonneg_right ?_ hcpos.le
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
    _ = (R (2 ^ v) - R (2 ^ u)) / c := by rw [R_sub_R_eq hpow]
    _ ≤ (Real.log ((2 ^ v : ℕ) : ℝ) - Real.log ((2 ^ u : ℕ) : ℝ) + 2 * C₀) / c := by
        gcongr; exact R_sub_R_le Nat.one_le_two_pow hpow
    _ = _ := by
        push_cast
        rw [Real.log_pow, Real.log_pow]
        ring

/-- `w/s ≤ log((s+w)/s) + w²/s²`, from `log y ≥ 1 - 1/y`. -/
lemma div_le_log_add_sq {s w : ℝ} (hs : 0 < s) (hw : 0 ≤ w) :
    w / s ≤ Real.log ((s + w) / s) + w ^ 2 / s ^ 2 := by
  have hsw : 0 < s + w := by linarith
  have h1 : 1 - s / (s + w) ≤ Real.log ((s + w) / s) := by
    have := Real.log_le_sub_one_of_pos (show 0 < s / (s + w) by positivity)
    rw [Real.log_div hs.ne' hsw.ne'] at this
    rw [Real.log_div hsw.ne' hs.ne']
    linarith
  have h2 : w / s = (1 - s / (s + w)) + w ^ 2 / (s * (s + w)) := by
    field_simp; ring
  have h3 : w ^ 2 / (s * (s + w)) ≤ w ^ 2 / s ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  linarith


/-- `c₁ = 2 C₀ / log 2`, the per-shell error. -/
noncomputable def c₁ : ℝ := 2 * C₀ / Real.log 2

lemma c₁_pos : 0 < c₁ := by
  unfold c₁; have := C₀_pos; have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity

/-- One shell, in the form used by the block lemma. -/
lemma sum_inv_shell_le'' (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (u v : ℕ) (hu : 1 ≤ u)
    (huv : u ≤ v) (hrange : ∀ ℓ ∈ S, 2 ^ u < ℓ ∧ ℓ ≤ 2 ^ v) :
    ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ (v - u : ℝ) / u + c₁ / u := by
  have h := sum_inv_shell_le' S hS u v hu huv hrange
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  refine h.trans (le_of_eq ?_)
  unfold c₁
  field_simp

/-- **Block lemma.** Splitting `(2^u, 2^v]` into shells of width `w`. -/
theorem sum_inv_blockM_le (w : ℕ) (hw : 1 ≤ w) :
    ∀ (n u v : ℕ), v - u = n → ∀ (S : Finset ℕ), (∀ ℓ ∈ S, ℓ.Prime) → 1 ≤ u → u ≤ v →
      (∀ ℓ ∈ S, 2 ^ u < ℓ ∧ ℓ ≤ 2 ^ v) →
      ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ Real.log v - Real.log u + (w : ℝ) * (v - u) / (u : ℝ) ^ 2
        + c₁ * ((v - u : ℝ) / w + 1) / u := by
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hc := c₁_pos
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v hn S hS hu huv hrange
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (u : ℝ) ≤ v := by exact_mod_cast huv
  by_cases hsmall : v ≤ u + w
  · -- one shell
    have h1 := sum_inv_shell_le'' S hS u v hu huv hrange
    have hd : (v - u : ℝ) ≤ w := by
      have : (v : ℝ) ≤ u + w := by exact_mod_cast hsmall
      linarith
    have h2 := div_le_log_add_sq (s := (u : ℝ)) (w := (v - u : ℝ)) (by linarith) (by linarith)
    rw [show (u : ℝ) + (v - u) = v by ring, Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))] at h2
    have h3 : (v - u : ℝ) ^ 2 / (u : ℝ) ^ 2 ≤ (w : ℝ) * (v - u) / (u : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have h4 : c₁ / u ≤ c₁ * ((v - u : ℝ) / w + 1) / u := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ (v - u : ℝ) / w := div_nonneg (by linarith) (by positivity)
      nlinarith
    linarith
  · push Not at hsmall
    set S₁ := S.filter fun ℓ => ℓ ≤ 2 ^ (u + w) with hS₁
    set S₂ := S.filter fun ℓ => ¬ ℓ ≤ 2 ^ (u + w) with hS₂
    have hsplit : ∑ ℓ ∈ S, (1 : ℝ) / ℓ = ∑ ℓ ∈ S₁, (1 : ℝ) / ℓ + ∑ ℓ ∈ S₂, (1 : ℝ) / ℓ :=
      (Finset.sum_filter_add_sum_filter_not S _ _).symm
    have h1 := sum_inv_shell_le'' S₁ (fun ℓ h => hS ℓ (Finset.mem_filter.mp h).1) u (u + w) hu
      (by omega) fun ℓ h => ⟨(hrange ℓ (Finset.mem_filter.mp h).1).1, (Finset.mem_filter.mp h).2⟩
    have h2 := ih (v - (u + w)) (by omega) (u + w) v rfl S₂
      (fun ℓ h => hS ℓ (Finset.mem_filter.mp h).1) (by omega) (by omega)
      fun ℓ h => ⟨not_le.mp (Finset.mem_filter.mp h).2, (hrange ℓ (Finset.mem_filter.mp h).1).2⟩
    push_cast at h1 h2
    have hu0 : (0 : ℝ) < u := by linarith
    have h5 := div_le_log_add_sq (s := (u : ℝ)) (w := (w : ℝ)) hu0 (by linarith)
    rw [Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))] at h5
    have hvw : (u : ℝ) + w < v := by exact_mod_cast hsmall
    -- compare the remainder's error terms with the target's
    have e1 : (w : ℝ) * (v - (u + w)) / ((u : ℝ) + w) ^ 2 ≤ (w : ℝ) * (v - (u + w)) / (u : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by nlinarith) (by positivity)
      nlinarith
    have e2 : c₁ * ((v - (u + w) : ℝ) / w + 1) / ((u : ℝ) + w) ≤ c₁ * ((v - u : ℝ) / w) / u := by
      have : (v - (u + w) : ℝ) / w + 1 = (v - u : ℝ) / w := by field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_left (by positivity) hu0 (by linarith)
    have e3 : (w : ℝ) / u = (w : ℝ) / u := rfl
    have hfin : (w : ℝ) * (v - u) / (u : ℝ) ^ 2 = (w : ℝ) ^ 2 / (u : ℝ) ^ 2
        + (w : ℝ) * (v - (u + w)) / (u : ℝ) ^ 2 := by field_simp; ring
    have hfin2 : c₁ * ((v - u : ℝ) / w + 1) / u = c₁ / u + c₁ * ((v - u : ℝ) / w) / u := by
      field_simp; ring
    rw [hsplit, hfin, hfin2]
    have : ((u : ℝ) + w - u) / u = (w : ℝ) / u := by ring
    rw [this] at h1
    linarith

end Shoup.Sieve
