import Artin.Interfaces

/-!
# The Kummer-theory inputs to the sieve half (blueprint B5, B6)

The sieve assembly in `Artin/Sieve/Assembly.lean` needs two facts about the degrees
`[K_k : ℚ] = kummerDegree a k` of the Kummer fields `K_k = ℚ(ζ_k, a^{1/k})`. They are stated here
as hypotheses (`Prop`s), not as axioms or sorried theorems; `Artin/Kummer/` proves them, and
`Artin/SieveHalf.lean` discharges them there (`kummerDegreeLowerBound_of_ne`,
`kummerDensityPos_of_not_isSquare`).

* `KummerDegreeLowerBound a` (blueprint B5): `k φ(k) ≤ c · [K_k : ℚ]` for squarefree `k ≥ 1`.
  True for every `a ∉ {0, 1, -1}`: writing `a = ± b^h` with `h` maximal,
  `[K_k : ℚ] = k φ(k) / ε(k)` with `ε(k) ∣ 2h`, so `c = 2h` works.
* `KummerDensityPos a` (blueprint B6): `δ(a) = Σ_k μ(k) / [K_k : ℚ] > 0`. True for `a` not a
  square and `a ≠ -1` (Hooley 1967; exact form in Lenstra–Moree–Stevenhagen, arXiv:1112.4816).

The sum in `KummerDensityPos` is a `tsum`. Its summability is not assumed: the assembly derives
it from `KummerDegreeLowerBound` (`Artin.summable_moebius_div_kummerDegree`), since
`Σ 1/(k φ(k))` converges.
-/

namespace Artin

open scoped ArithmeticFunction.Moebius

/-- **Blueprint B5.** The Kummer degrees grow like `k φ(k)`: there is `c > 0` with
`k φ(k) ≤ c · [K_k : ℚ]` for every squarefree `k ≥ 1`. -/
def KummerDegreeLowerBound (a : ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, Squarefree k → 0 < k →
    ((k : ℝ) * (Nat.totient k : ℝ)) ≤ c * (kummerDegree a k : ℝ)

/-- **Blueprint B6.** The Artin density `δ(a) = Σ_{k ≥ 1} μ(k) / [K_k : ℚ]` is positive. -/
def KummerDensityPos (a : ℤ) : Prop :=
  0 < ∑' k : ℕ, (μ k : ℝ) / (kummerDegree a k : ℝ)

end Artin
