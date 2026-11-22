import Artin.Statement

/-!
# The two halves of Hooley's proof

`docs/BLUEPRINT.md` explains the plan. The proof splits at one elementary statement,
`EffectiveKummerChebotarev a`: for squarefree `k`, the number of primes `p < x` that split
completely in the Kummer field `K_k = ℚ(ζ_k, a^{1/k})` is `π(x)/[K_k : ℚ] + O(√x log(kx))`.

* Analytic half (`effectiveKummerChebotarev_of_hooley`): RH for `ζ_{K_k}` gives that count.
* Sieve half (`artin_of_effectiveKummerChebotarev`, in `Artin/SieveHalf.lean`): Hooley's sieve over `k` turns the counts
  into the density of primes for which `a` is a primitive root, and Kummer theory shows that
  density is positive.

A prime `p ∤ a` splits completely in `K_k` exactly when `p ≡ 1 (mod k)` and `a` is a `k`-th
power mod `p`, that is `a^((p-1)/k) = 1` in `ZMod p`. `kummerCount` counts primes by that
congruence condition, so the interface never mentions prime ideals.
-/

namespace Artin

open ArtinPrimitiveRootsConjecture Polynomial

/-- `[K_k : ℚ]` for the Kummer field `K_k`, the splitting field of `X^k - a` over `ℚ`. -/
noncomputable def kummerDegree (a : ℤ) (k : ℕ) : ℕ :=
  Module.finrank ℚ (X ^ k - C (a : ℚ)).SplittingField

/-- The number of primes `p < x` with `p ∤ a`, `k ∣ p - 1` and `a^((p-1)/k) = 1` in `ZMod p`:
the primes below `x` that split completely in `K_k`. -/
noncomputable def kummerCount (a : ℤ) (k x : ℕ) : ℕ :=
  ((Finset.range x).filter fun p : ℕ =>
    p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1).card

/-- Effective Chebotarev for the Kummer fields of `a`, in Hooley's form (Hooley 1967, §3):
`kummerCount a k x = π(x) / [K_k : ℚ] + O(√x log(k x))`, uniformly in squarefree `k`. -/
def EffectiveKummerChebotarev (a : ℤ) : Prop :=
  ∃ C : ℝ, ∀ k x : ℕ, Squarefree k → 2 ≤ x →
    |(kummerCount a k x : ℝ) - (Nat.primeCounting x : ℝ) / kummerDegree a k|
      ≤ C * Real.sqrt x * Real.log (k * x)

/-- Analytic half: RH for the Dedekind zeta functions of the Kummer fields gives effective
Chebotarev for them. -/
theorem effectiveKummerChebotarev_of_hooley (a : ℤ) (ha : a ≠ 0) (h : HooleyHypothesis a) :
    EffectiveKummerChebotarev a := by
  sorry

/-! The sieve half, `artin_of_effectiveKummerChebotarev (a : ℤ) (ha : ¬IsSquare a)
(ha' : a ≠ -1) (h : EffectiveKummerChebotarev a) : ∃ x > 0, (S a).HasDensity x {p | p.Prime}`,
is stated and proved in `Artin/SieveHalf.lean`: its proof uses the sieve (`Artin/Sieve/`) and
Kummer theory (`Artin/Kummer/`), and both import this file, so it cannot live here. -/

end Artin
