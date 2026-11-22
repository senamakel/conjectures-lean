import Artin.Kummer.Degree

/-!
# The analytic interface: `ψ_K(x) = x + O(√x (log d_K + n_K log x) log x)`

This file fixes the statement that the analytic core of blueprint part A (Hadamard product for
the completed `ζ_K`, zero counting, explicit formula under RH; steps A1–A4) is to prove, and
that the arithmetic steps A5–A7 (`Artin/Analytic/Splitting.lean`, `Discriminant.lean`,
`Counting.lean`) turn into `EffectiveKummerChebotarev`. Nothing here is assumed: the two
statements are plain `Prop`s.

For a number field `K` and a rational prime `p`, `primesAbove K p` is the finite set of prime
ideals of `𝓞 K` dividing `p 𝓞 K`. The Chebyshev function of `K` is
`ψ_K(x) = ∑_{𝔭, m ≥ 1, N𝔭^m < x} log N𝔭`, the sum over nonzero prime ideals `𝔭` of `𝓞 K` and
exponents `m ≥ 1`. Grouping the pairs `(𝔭, m)` by the ideal `𝔞 = 𝔭^m`, this is
`∑_{N𝔞 < x} Λ_K(𝔞)` with `Λ_K(𝔭^m) = log N𝔭`, the coefficients of `-ζ_K'/ζ_K`, which is the
form the explicit formula produces. We write it with the rational prime `p` under `𝔭` made
explicit, so that the sum is visibly finite: `N𝔭 ≥ p`, so `p ≤ x`, and `N𝔭 ≥ 2`, so `m ≤ x`.

`PsiKBound K C` is `|ψ_K(x) - x| ≤ C √x (log |d_K| + n_K log x) log x` for real `x ≥ 2`. This is
the Lagarias–Odlyzko bound under RH for `ζ_K` (J. C. Lagarias, A. M. Odlyzko, *Effective
versions of the Chebotarev density theorem*, 1977, Theorem 9.2 for the trivial class; see also
Serre, *Quelques applications du théorème de densité de Chebotarev*, 1981, §2.4, Théorème 4),
with an absolute constant `C`. Blueprint step A3 gives the smoothed sum with error
`≪ √x (log d + n log x)`; unsmoothing (A4) costs the last factor `log x`. Hooley needs exactly
this shape: with `log |d_{K_k}| ≪ n_k log(k |a|)` (A6) the error divided by `n_k` is
`√x log x log(k x)`, and partial summation turns that into `√x log(k x)` for the count of
primes (A7, `Counting.lean`).

`KummerPsiBounds a` asks for one constant `C` that works for every Kummer field `K_k`, `k`
squarefree. The `k = 1` field is `ℚ` itself, where the bound is the classical
`ψ(x) = x + O(√x log² x)` under RH; `Counting.lean` uses that instance in place of a separate
hypothesis on `π(x) - li(x)`.
-/

namespace Artin.Analytic

open NumberField Polynomial

/-- The Kummer field `K_k` is a number field. This is the instance `HooleyHypothesis` uses
(`NumberField.of_module_finite`), made global for the analytic files. -/
noncomputable instance instNumberFieldKField (a : ℤ) (k : ℕ) : NumberField (Kummer.KField a k) :=
  NumberField.of_module_finite ℚ _

section

variable (K : Type*) [Field K] [NumberField K]

/-- The prime ideals of `𝓞 K` above the rational prime `p`: the prime factors of `p 𝓞 K`.
For `p` prime this is `IsDedekindDomain.primesOverFinset (span {p}) (𝓞 K)`, see
`mem_primesAbove`. -/
noncomputable def primesAbove (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.factors
    ((Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)))).toFinset

/-- The Chebyshev function of `K`: `ψ_K(x) = ∑_{𝔭, m ≥ 1, N𝔭^m < x} log N𝔭`, the sum running
over nonzero prime ideals `𝔭` of `𝓞 K` (grouped by the rational prime `p` below them) and
exponents `m ≥ 1`. Equivalently `∑_{N𝔞 < x} Λ_K(𝔞)`. -/
noncomputable def psiK (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
    ∑ P ∈ primesAbove K p,
      ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
        if ((Ideal.absNorm P : ℕ) : ℝ) ^ m < x then Real.log (Ideal.absNorm P) else 0

/-- **The analytic interface.** RH for `ζ_K` in Lagarias–Odlyzko form:
`|ψ_K(x) - x| ≤ C √x (log |d_K| + n_K log x) log x` for all real `x ≥ 2`. -/
def PsiKBound (C : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    |psiK K x - x| ≤
      C * Real.sqrt x * (Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log x) * Real.log x

end

/-- The hypothesis bundle for Hooley's theorem: `PsiKBound` with one constant for all the Kummer
fields `K_k = ℚ(ζ_k, a^{1/k})`, `k` squarefree. -/
def KummerPsiBounds (a : ℤ) : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, Squarefree k → PsiKBound (Kummer.KField a k) C

end Artin.Analytic
