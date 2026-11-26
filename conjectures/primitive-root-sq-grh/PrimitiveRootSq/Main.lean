import PrimitiveRootSq.Statement
import PrimitiveRootSq.Lift
import PrimitiveRootSq.Bach
import PrimitiveRootSq.Indicator
import PrimitiveRootSq.Theta
import PrimitiveRootSq.Numerics
import PrimitiveRootSq.Compute
import Erdos985.Analytic.Principal

/-!
# Prime primitive roots modulo `p²` and modulo every `p ^ k`, from GRH

For `p < 10^8` the verified computation (`PrimitiveRootSq.small_primes_good`) gives the witness.
For `p ≥ 10^8`, if no prime `q < p` were a primitive root modulo `p` with
`q ^ (p - 1) ≢ 1 (mod p²)`, `key_inequality` would hold with Bach's bounds at modulus `p` and
`p²`, the principal bound `bach_principal_of_GRH` and `θ ≥ c₂₉ (28/29)^ω` (`theta_ge`); `numerics`
shows that it does not. `Lift.lean` turns the witness into a primitive root modulo every `p ^ k`.
-/

namespace PrimitiveRootSq

open ArithmeticFunction Erdos985

/-- Under GRH, every odd prime `p` has a prime `q < p` that is a primitive root modulo `p` with
`q ^ (p - 1) ≢ 1 (mod p²)`. -/
theorem exists_good_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  by_cases hlt : p < 10 ^ 8
  · exact small_primes_good p hp hp2 hlt
  have hpf : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  have hno : ∀ q, q.Prime → q < p → orderOf (q : ZMod p) = p - 1 →
      (q : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
    intro q hq hqp ho
    by_contra h
    exact hcon ⟨q, hq, hqp, ho, h⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set B₁ : ℝ := (√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6
    with hB₁
  set B₂ : ℝ := (√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (2 * Real.log p + 5 / 3))
    + (Real.log p + 1) + 0.6 with hB₂
  have hb₁ : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ p‖ ≤ B₁ := fun χ hχ =>
    bach_primitive_of_GRH hGRH (isPrimitive_of_prime hp hχ) hχ p hp1
  have hb₂ : ∀ χ : DirichletCharacter ℂ (p ^ 2), χ.IsPrimitive → χ ≠ 1 → ‖bachSum χ p‖ ≤ B₂ := by
    intro χ hprim hχ
    have h := bach_primitive_of_GRH hGRH hprim hχ p hp1
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
  have key := key_inequality p B₁ B₂ hb₁ hb₂ hno
  set θ := ∏ ℓ ∈ (p - 1).primeFactors, (1 - 1 / (ℓ : ℝ)) with hθ
  have hθ0 := theta_ge (p - 1)
  have hnum := numerics p (not_lt.mp hlt) θ hθ0
  rw [← hB₁, ← hB₂] at hnum
  have hθpos : 0 ≤ θ := (lt_of_lt_of_le (by positivity) hθ0).le
  set S₀ := ∑ n ∈ Finset.range p, (Λ n : ℝ) * (1 - (n : ℝ) / p) with hS₀
  have hprin := Analytic.bach_principal_of_GRH hGRH p hp1
  obtain ⟨hlo, hhi⟩ := abs_le.mp hprin
  have hB₂0 : 0 ≤ B₂ := by
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
    positivity
  -- left side: `θ (S₀ - (X-1) B₁) ≥ θ (p/2 - √p/20 - 3 - (X-1) B₁)`
  have h1 : θ * ((p : ℝ) / 2 - (√(p : ℝ) / 20 + 3)
      - ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B₁)
      ≤ θ * (S₀ - ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B₁) :=
    mul_le_mul_of_nonneg_left (by linarith) hθpos
  -- right side: `(S₀ + (p-1) B₂)/p ≤ (p/2 + √p/20 + 3)/p + B₂`
  have h2 : (S₀ + (p - 1) * B₂) / p ≤ ((p : ℝ) / 2 + (√(p : ℝ) / 20 + 3)) / p + B₂ := by
    rw [div_add' _ _ _ hpR.ne', div_le_div_iff_of_pos_right hpR]
    nlinarith
  linarith

/-- **Main theorem (GRH).** Every odd prime `p` has a prime `q < p` that is a primitive root
modulo `p²`. -/
theorem primitiveRootSq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    PrimitiveRootSqStatement := by
  intro p hp hp2
  obtain ⟨q, hq, hqp, ho, hs⟩ := exists_good_of_GRH hGRH p hp hp2
  exact ⟨q, hq, hqp, orderOf_prime_sq hp hp2 ho hs⟩

/-- **Main theorem (GRH), all powers.** Every odd prime `p` has a prime `q < p` that is a
primitive root modulo `p ^ k` for every `k ≥ 1`. -/
theorem primitiveRootPow_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    PrimitiveRootPowStatement := by
  intro p hp hp2
  obtain ⟨q, hq, hqp, ho, hs⟩ := exists_good_of_GRH hGRH p hp hp2
  exact ⟨q, hq, hqp, fun k hk => orderOf_prime_pow hp hp2 ho hs hk⟩

end PrimitiveRootSq
