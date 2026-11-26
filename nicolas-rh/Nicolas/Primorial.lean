import Nicolas.Statement
import Robin.Defs

/-!
# Primorials, `θ` and Mertens' product

For a prime `q = p_k`: `N_k = primorial q`, `log N_k = θ(q)` and
`N_k/φ(N_k) = ∏_{p ≤ q} p/(p−1) = exp(Σ_{p≤q} c_p)` with `c_p = −log(1 − 1/p)`.
-/

namespace Nicolas

open Real Chebyshev Robin

lemma primesLE_nth (k : ℕ) :
    Nat.primesLE (Nat.nth Nat.Prime k) = (Finset.range (k + 1)).image (Nat.nth Nat.Prime) := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hle, hp⟩
    refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hp⟩
    have h := Nat.nth_count hp
    rw [Nat.lt_succ_iff, ← Nat.nth_le_nth Nat.infinite_setOfPred_prime, h]
    exact hle
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (by omega), Nat.prime_nth_prime i⟩

theorem kthPrimorial_succ_eq (k : ℕ) :
    kthPrimorial (k + 1) = primorial (Nat.nth Nat.Prime k) := by
  rw [primorial_eq_prod_primesLE, primesLE_nth, Finset.prod_image]
  · rfl
  · intro a _ b _ h
    exact Nat.nth_injective Nat.infinite_setOfPred_prime h

lemma primeSum_eq_primesLE (f : ℕ → ℝ) (n : ℕ) :
    primeSum f n = ∑ p ∈ Nat.primesLE n, f p := by
  unfold primeSum
  rw [Nat.floor_natCast]
  congr 1
  ext p; simp [Nat.mem_primesLE]

lemma cp_eq_log {p : ℕ} (hp : 2 ≤ p) : cp p = Real.log ((p : ℝ) / (p - 1)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold cp
  rw [← Real.log_inv]
  congr 1
  field_simp

/-- `n#/φ(n#) = exp(Σ_{p≤n} c_p)`. -/
theorem primorial_div_totient (n : ℕ) :
    (primorial n : ℝ) / (Nat.totient (primorial n) : ℝ) = Real.exp (primeSum cp n) := by
  have h := Nat.totient_mul_prod_primeFactors (primorial n)
  rw [primeFactors_primorial] at h
  have hP : ∀ p ∈ Nat.primesLE n, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primesLE hp).two_le
  have hR : ((Nat.totient (primorial n) : ℕ) : ℝ) * ∏ p ∈ Nat.primesLE n, (p : ℝ)
      = (primorial n : ℝ) * ∏ p ∈ Nat.primesLE n, ((p : ℝ) - 1) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (by linarith [hP p hp])]; simp
  have hpos1 : 0 < ∏ p ∈ Nat.primesLE n, ((p : ℝ) - 1) :=
    Finset.prod_pos fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
      linarith
  have hpos2 : 0 < ∏ p ∈ Nat.primesLE n, (p : ℝ) :=
    Finset.prod_pos fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
      linarith
  have hφ : (0 : ℝ) < Nat.totient (primorial n) := by
    exact_mod_cast Nat.totient_pos.mpr (primorial_pos n)
  rw [primeSum_eq_primesLE, Real.exp_sum]
  have hq : ∏ p ∈ Nat.primesLE n, Real.exp (cp p)
      = (∏ p ∈ Nat.primesLE n, (p : ℝ)) / ∏ p ∈ Nat.primesLE n, ((p : ℝ) - 1) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
    rw [cp_eq_log (hP p hp), Real.exp_log (by apply div_pos <;> linarith)]
  rw [hq, div_eq_div_iff hφ.ne' hpos1.ne']
  linarith [hR]

theorem log_primorial (n : ℕ) : Real.log (primorial n) = θ n := by
  rw [theta_eq_log_primorial, Nat.floor_natCast]

end Nicolas
