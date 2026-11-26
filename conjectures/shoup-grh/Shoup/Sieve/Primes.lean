import Mathlib

/-!
# Elementary prime estimates for the sieve

* `sum_inv_shell_le`: `Σ_{2^k < ℓ ≤ 2^{k+1}} 1/ℓ ≤ 4/k` over any set of primes, from Chebyshev's
  `θ(x) ≤ x log 4` (Mathlib).
* `sum_inv_block_le`: `Σ_{2^a < ℓ ≤ 2^{2a}} 1/ℓ ≤ 4` for `a ≥ 1`.
* `card_block_add_one_le`: at most `2^{2a} - 1` integers lie in `(2^a, 2^{2a}]`.
* `prod_one_sub_inv_ge`: `∏_{ℓ∈P}(1 - 1/ℓ) ≥ 1/(|P|+1)` for any finite set of integers `≥ 2`.
-/

namespace Shoup.Sieve

open Finset Real Chebyshev

lemma sum_log_le_theta (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (N : ℕ) (hN : ∀ ℓ ∈ S, ℓ ≤ N) :
    ∑ ℓ ∈ S, Real.log ℓ ≤ θ N := by
  rw [theta_eq_sum_primesLE_log]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ h => ?_) fun ℓ _ _ =>
    Real.log_natCast_nonneg ℓ
  rw [Nat.primesLE, Nat.mem_primesBelow]
  exact ⟨Nat.lt_succ_of_le (hN ℓ h), hS ℓ h⟩

/-- Reciprocals of the primes in a dyadic shell. -/
theorem sum_inv_shell_le (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (k : ℕ) (hk : 1 ≤ k)
    (hrange : ∀ ℓ ∈ S, 2 ^ k < ℓ ∧ ℓ ≤ 2 ^ (k + 1)) :
    ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ 4 / k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  set c : ℝ := k * Real.log 2 * 2 ^ k with hc
  have hcpos : 0 < c := by positivity
  have hterm : ∀ ℓ ∈ S, (1 : ℝ) / ℓ ≤ Real.log ℓ / c := by
    intro ℓ h
    obtain ⟨h1, _⟩ := hrange ℓ h
    have hℓ : (2 : ℝ) ^ k < ℓ := by exact_mod_cast h1
    have hℓpos : (0 : ℝ) < ℓ := hpow.trans hℓ
    have hlogℓ : k * Real.log 2 ≤ Real.log ℓ := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hℓ.le
    rw [div_le_div_iff₀ hℓpos hcpos, one_mul, hc]
    have : k * Real.log 2 * 2 ^ k ≤ Real.log ℓ * 2 ^ k :=
      mul_le_mul_of_nonneg_right hlogℓ hpow.le
    have : Real.log ℓ * 2 ^ k ≤ Real.log ℓ * ℓ :=
      mul_le_mul_of_nonneg_left hℓ.le (Real.log_natCast_nonneg ℓ)
    linarith
  calc ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ ∑ ℓ ∈ S, Real.log ℓ / c := Finset.sum_le_sum hterm
    _ = (∑ ℓ ∈ S, Real.log ℓ) / c := by rw [Finset.sum_div]
    _ ≤ θ ((2 ^ (k + 1) : ℕ) : ℝ) / c := by
        gcongr
        exact sum_log_le_theta S hS _ fun ℓ h => (hrange ℓ h).2
    _ ≤ Real.log 4 * 2 ^ (k + 1) / c := by
        gcongr
        have := theta_le_log4_mul_x (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by positivity)
        push_cast at this ⊢
        exact this
    _ = 4 / k := by
        rw [hc, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        field_simp
        ring

/-- Reciprocals of the primes in `(2^a, 2^{2a}]`. -/
theorem sum_inv_block_le (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (a : ℕ) (ha : 1 ≤ a)
    (hrange : ∀ ℓ ∈ S, 2 ^ a < ℓ ∧ ℓ ≤ 2 ^ (2 * a)) :
    ∑ ℓ ∈ S, (1 : ℝ) / ℓ ≤ 4 := by
  have hmaps : ∀ ℓ ∈ S, Nat.log 2 (ℓ - 1) ∈ Ico a (2 * a) := by
    intro ℓ h
    obtain ⟨h1, h2⟩ := hrange ℓ h
    have := Nat.one_le_two_pow (n := a)
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    · exact Nat.log_lt_of_lt_pow (by omega) (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Ico a (2 * a), ∑ ℓ ∈ S with Nat.log 2 (ℓ - 1) = k, (1 : ℝ) / ℓ
      ≤ ∑ k ∈ Ico a (2 * a), (4 : ℝ) / a := by
        refine Finset.sum_le_sum fun k hk => ?_
        obtain ⟨hk1, _⟩ := Finset.mem_Ico.mp hk
        refine (sum_inv_shell_le _ (fun ℓ h => hS ℓ (Finset.mem_filter.mp h).1) k (by omega)
          fun ℓ h => ?_).trans ?_
        · obtain ⟨hℓS, hlog⟩ := Finset.mem_filter.mp h
          obtain ⟨h1, _⟩ := hrange ℓ hℓS
          have hpos : ℓ - 1 ≠ 0 := by have := Nat.one_le_two_pow (n := a); omega
          have hA := Nat.pow_log_le_self 2 hpos
          have hB := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (ℓ - 1)
          rw [hlog] at hA hB
          omega
        · have : (a : ℝ) ≤ k := by exact_mod_cast hk1
          have : (0 : ℝ) < a := by exact_mod_cast ha
          exact div_le_div_of_nonneg_left (by norm_num) this (by assumption)
    _ = 4 := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have : (0 : ℝ) < a := by exact_mod_cast ha
        rw [show 2 * a - a = a by omega]
        field_simp

theorem card_block_add_one_le (S : Finset ℕ) (a : ℕ)
    (hrange : ∀ ℓ ∈ S, 2 ^ a < ℓ ∧ ℓ ≤ 2 ^ (2 * a)) :
    S.card + 1 ≤ 2 ^ (2 * a) := by
  have hsub : S ⊆ Finset.Ioc (2 ^ a) (2 ^ (2 * a)) := fun ℓ h => Finset.mem_Ioc.mpr (hrange ℓ h)
  have := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at this
  have h1 := Nat.one_le_two_pow (n := a)
  have h2 : 2 ^ a ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `∏_{ℓ∈P}(1 - 1/ℓ) ≥ 1/(|P|+1)` for distinct integers `ℓ ≥ 2`. -/
theorem prod_one_sub_inv_ge (P : Finset ℕ) (hP : ∀ ℓ ∈ P, 2 ≤ ℓ) :
    1 / ((P.card : ℝ) + 1) ≤ ∏ ℓ ∈ P, (1 - 1 / (ℓ : ℝ)) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert x s hlt ih =>
    have hxs : x ∉ s := fun h => lt_irrefl x (hlt x h)
    have ih' := ih fun ℓ h => hP ℓ (Finset.mem_insert_of_mem h)
    rw [Finset.prod_insert hxs, Finset.card_insert_of_notMem hxs]
    -- `x ≥ |s| + 2`: the elements of `insert x s` are distinct integers in `[2, x]`
    have hcard : s.card + 2 ≤ x := by
      have hsub : insert x s ⊆ Finset.Icc 2 x := by
        intro ℓ h
        rw [Finset.mem_Icc]
        refine ⟨hP ℓ h, ?_⟩
        rcases Finset.mem_insert.mp h with rfl | h
        · exact le_rfl
        · exact (hlt ℓ h).le
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hxs, Nat.card_Icc] at this
      omega
    have hxR : ((s.card : ℝ) + 2) ≤ x := by exact_mod_cast hcard
    have hn : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    have hfac : ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2) ≤ 1 - 1 / (x : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      have hx0 : (0 : ℝ) < x := by linarith
      have : 1 / (x : ℝ) ≤ 1 / ((s.card : ℝ) + 2) :=
        one_div_le_one_div_of_le (by linarith) hxR
      have : 1 / ((s.card : ℝ) + 2) * ((s.card : ℝ) + 2) = 1 := by field_simp
      nlinarith
    have hpos : (0 : ℝ) ≤ ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2) := by positivity
    push_cast
    calc 1 / ((s.card : ℝ) + 1 + 1) = ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2) *
          (1 / ((s.card : ℝ) + 1)) := by field_simp; ring
      _ ≤ (1 - 1 / (x : ℝ)) * ∏ ℓ ∈ s, (1 - 1 / (ℓ : ℝ)) :=
          mul_le_mul hfac ih' (by positivity) (hpos.trans hfac)

end Shoup.Sieve
