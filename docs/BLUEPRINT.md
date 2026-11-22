# Blueprint: Artin's conjecture under Hooley's hypothesis

Target: `conditional_artin_primitive_roots.parts.i` (formal-conjectures). For an integer `a`
that is not a square and not `-1`, assuming RH for `ζ_K` for every Kummer field
`K_k = ℚ(ζ_k, a^{1/k})` with `k` squarefree, the primes `p` for which `a` is a primitive root
have a positive density among the primes.

Source: C. Hooley, *On Artin's conjecture*, J. reine angew. Math. 225 (1967), 209–220. A
readable modern account is P. Moree, *Artin's primitive root conjecture: a survey*,
arXiv:math/0412262, §3.

## What is and is not covered by the riemann-hypothesis repository

leanprover-community/riemann-hypothesis proves RH for ζ and GRH for Dirichlet L-functions
(`DirichletLNonvanishingRightOfHalf`). `K_k` is not abelian over ℚ for `k > 2`, so `ζ_{K_k}`
is not a product of Dirichlet L-functions, and that repository does not discharge
`HooleyHypothesis`. As far as we can tell it proves nothing about zeros of `ζ_K` beyond the
functional equation and the pole at `s = 1`. The result here therefore stays conditional,
unlike `erdos_985`. The `k = 1` instance of `HooleyHypothesis` is RH itself.

## Split

`Artin/Interfaces.lean` fixes one elementary statement between the halves:

```
EffectiveKummerChebotarev a :
  ∃ C, ∀ k x, Squarefree k → 2 ≤ x →
    |kummerCount a k x − π(x) / [K_k : ℚ]| ≤ C √x log(kx)
```

where `kummerCount a k x` counts primes `p < x`, `p ∤ a`, `k | p − 1`,
`a^((p−1)/k) = 1 (mod p)`. These are exactly the primes below `x` that split completely in
`K_k` (Dedekind–Kummer for `X^k − a` at `p ∤ ka`; primes dividing `k` are `O(log k)` in
number).

### A. Analytic half: `HooleyHypothesis a → EffectiveKummerChebotarev a`

For `K = K_k`, `n = [K : ℚ]`, `d = |disc K|`:

1. **Completed `ζ_K`** has order 1 and a Hadamard product. The functional equation
   (Hecke) is in the riemann-hypothesis repo (`completedDedekindZeta_one_sub`) but not in
   our Mathlib pin. Either port it (check licences) or prove it.
2. **Zero counting**: `#{ρ : |γ − T| ≤ 1} ≪ log d + n log(|T| + 2)`.
3. **Explicit formula** for `ψ_K(x) = Σ_{N𝔞 < x} Λ_K(𝔞)` with weight `(1 − N𝔞/x)`, as
   erdos-985 does for Dirichlet L-functions (`Erdos985/Analytic/ExplicitFormula*`,
   `Perron`, `Hadamard`, `XiGrowth`). Under RH the zero sum is `≪ √x (log d + n log x)`.
4. **Unsmoothing** the weight by differencing at `x` and `x(1 + δ)`.
5. **From ideals to rational primes**: primes that split completely contribute `n log p`.
   Prime powers and primes of residue degree ≥ 2 contribute `O(n √x log x)`.
6. **Discriminant bound** (Serre / Hensel): `log d ≤ n · log(n · k · |a|) + O(n)`, using
   that ramified primes divide `k a`.
7. **π(x) − li(x) = O(√x log x)** from the `k = 1` case, which is RH.

This is the largest part. Steps 1–3 generalise the erdos-985 analytic library from Dirichlet
L-functions to `ζ_K`.

### B. Sieve half: `EffectiveKummerChebotarev a → density > 0`

Write `N(x)` for the number of primes `p < x`, `p ∤ a`, with `a` a primitive root mod `p`.
`a` is a primitive root mod `p` iff no prime `q | p − 1` has `a^((p−1)/q) = 1`. Let
`ξ₁ = (1/6) log x`, `ξ₂ = √x / log² x` and `ξ₃ = √x log x`.

1. **Small primes** (`q ≤ ξ₁`): inclusion–exclusion over `k | ∏_{q ≤ ξ₁} q`, so
   `k ≤ x^{1/6 + o(1)}`, gives `Σ μ(k) kummerCount a k x = π(x) Σ μ(k)/[K_k:ℚ] + O(x^{2/3+ε})`.
   Done in `Artin/Sieve/Assembly.lean`, with `ξ₁ = ⌊(1/6) log x⌋`: `ξ₁# ≤ 4^{ξ₁} ≤ x^{1/3}`, so
   the error is `≤ x^{1/3} · C√x log(x^{4/3}) = o(π(x))`; the truncated density tends to `δ(a)`
   since `Σ μ(k)/[K_k:ℚ]` converges absolutely (from B5 and `n ≤ 2φ(n)²`).
2. **Medium primes** (`ξ₁ < q ≤ ξ₂`): `kummerCount a q x ≪ π(x)/q² + √x log x`, summed:
   `o(π(x))`. Needs `[K_q : ℚ] ≫ q²`. Done in `Artin/Sieve/Assembly.lean` (`medium_le`): the
   `π(x)/[K_q:ℚ]` terms sum to `≤ c π(x) Σ_{q > ξ₁} 1/(q φ(q)) = o(π(x))`, and the error terms
   to `π(ξ₂) · 2C√x log x ≪ x / log² x` by Chebyshev's `π(y) ≤ (log 4 + 1) y / log y`.
3. **Large primes** (`ξ₂ < q ≤ ξ₃`): Brun–Titchmarsh `π(x; q, 1) ≪ x/(q log(x/q))`, summed:
   `O(x log log x / log² x)`. Done: `Artin/Sieve/BrunTitchmarsh.lean` proves Brun–Titchmarsh
   with constant 20000 from the Selberg sieve vendored from PrimeNumberTheoremAnd, and
   `Artin/Sieve/BrunTitchmarshLargePrimes.lean` sums it, using Chebyshev's `θ(y) ≤ y log 4` on
   dyadic blocks for `∑ 1/q`.
4. **Huge primes** (`q > ξ₃`): `a^m ≡ 1 (mod p)` with `m = (p−1)/q < √x / log x`, so `p`
   divides `∏_{m < √x/log x} (a^m − 1)`, which has `O(x / log² x)` prime factors. Elementary.
5. **Kummer degrees**: `[K_k : ℚ] = k φ(k) / ε(k)`, with `ε(k) | 2h` where `a = ± b^h`.
   We need `[K_k : ℚ] ≥ c_a k φ(k)` for steps 1–2 and the tail of `Σ μ(k)/[K_k:ℚ]`.
   Stated as `KummerDegreeLowerBound a` in `Artin/Sieve/KummerInputs.lean`.
   Mathlib has `FieldTheory/KummerExtension.lean` and `KummerPolynomial.lean`.
6. **Positivity** of `δ(a) = Σ_k μ(k)/[K_k:ℚ]` for `a` not a square and not `−1`. This needs
   exact degrees, including the entanglement when `√a ∈ ℚ(ζ_k)`. Reference: Lenstra–Moree–
   Stevenhagen, *Character sums for primitive root densities*, arXiv:1112.4816.
   Stated as `KummerDensityPos a` in `Artin/Sieve/KummerInputs.lean`; the sieve half
   (`artin_of_effectiveKummerChebotarev_of_kummer`) is proved from B5, B6 and
   `EffectiveKummerChebotarev`.
7. **Density**: `N(x) = δ(a) π(x) + o(π(x))`, and `π(x) → ∞`, give `HasDensity δ(a)`
   relative to the primes. Primes dividing `a` are finitely many.

## Order of work

B4, B7 and the elementary lemma "primitive root iff no `a^((p−1)/q) = 1`" are unconditional
and small, so start there. Then B5/B6 (Kummer theory) and B3 (Brun–Titchmarsh) in parallel,
then B1/B2. Then A, which is the long pole and reuses erdos-985.
