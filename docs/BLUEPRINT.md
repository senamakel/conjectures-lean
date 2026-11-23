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

0. **Hecke's continuation, as a hypothesis.** `HooleyHypothesis` constrains every `Z` that
   continues `ζ_K` to `ℂ ∖ {1}`, but using it needs such a `Z`. The continuation and functional
   equation (Hecke) are in the riemann-hypothesis repo (`completedDedekindZeta_one_sub`,
   `differentiableAt_completedDedekindZeta`, `continuedDedekindZeta_eq`), which has no licence,
   and are not in Mathlib. So `Artin/Analytic/Continuation.lean` defines
   `DedekindContinuation K`: a `Z` with `IsDedekindZeta K Z` and an entire `ξ` with
   `ξ(s) = s(s−1) |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} Z(s)` for `Re s > 0`, `s ≠ 1`,
   `ξ(1−s) = ξ(s)`, and `‖ξ(s)‖ ≤ M (1+‖s‖)²` for `1/2 ≤ Re s ≤ 2` (Hecke's theta integral
   bounds `Λ_K` in vertical strips away from its poles). The target becomes
   `conditional_artin_primitive_roots.parts.i_of_continuation` (`Artin/MainContinuation.lean`),
   which additionally assumes `DedekindContinuation (K_k)` for squarefree `k`. The original
   `effectiveKummerChebotarev_of_hooley` (`Artin/Interfaces.lean`) stays sorried: it is true but
   unprovable here without the continuation.
1. **Completed `ζ_K`** has order 1 and a Hadamard product. Order 1 is derived from the strip
   bound, the functional equation, and Stirling plus the Euler product for `Re s ≥ 2`.
2. **Zero counting**: `#{ρ : |γ − T| ≤ 1} ≪ log d + n log(|T| + 2)`.
3. **Explicit formula** for `ψ_K(x) = Σ_{N𝔞 < x} Λ_K(𝔞)` with weight `(1 − N𝔞/x)`, as
   erdos-985 does for Dirichlet L-functions (`Erdos985/Analytic/ExplicitFormula*`,
   `Perron`, `Hadamard`, `XiGrowth`). Under RH the zero sum is `≪ √x (log d + n log x)`.
4. **Unsmoothing** the weight by differencing at `x` and `x(1 + δ)`.
5. **From ideals to rational primes**: primes that split completely contribute `n log p`.
   Prime powers and primes of residue degree ≥ 2 contribute `O(n √x log x)`.
   *Done* (`Artin/Analytic/Splitting.lean`, `Counting.lean`, sorry-free). For `p ∤ k a`,
   `p` splits completely in `K_k` iff `k ∣ p − 1` and `a^((p−1)/k) = 1` mod `p`
   (`kummerCond_iff_exists_absNorm_eq`, `split_of_kummerCond`). Dedekind–Kummer needs a
   monogenic order of index prime to `p`, which `K_k` need not have, so the proof uses the
   decomposition group instead: under the condition every root of `X^k − a` is congruent to
   an integer mod `𝔓`, so an element of the decomposition group fixes the roots (they stay
   distinct mod `𝔓` since `p ∤ k a`), hence is trivial, and `|D| = e f` (Mathlib's
   `Ideal.card_stabilizer_eq`) gives `e = f = 1`. Counting (`psiK_sub_theta`):
   `0 ≤ ψ_K(x) − n θ_k(x) ≤ n log x (2 log(k|a|) + √x)`, where `θ_k(x)` is `kummerCount`
   weighted by `log p`.
6. **Discriminant bound** (Serre / Hensel): `log d ≤ n · log(n · k · |a|) + O(n)`, using
   that ramified primes divide `k a`.
   *Done* (`Artin/Analytic/Discriminant.lean`, sorry-free) in the form
   `log |d_{K_k}| ≤ 4 n log(k |a|)` (`log_abs_discr_le`). Serre's route needs the exponent
   bound for the different, which Mathlib lacks; instead some monomials `ζ^i α^j` (`i, j < k`)
   form a `ℚ`-basis of algebraic integers whose discriminant is a nonzero integer square
   times `d_K`, and Hadamard's inequality bounds it by `(n! |a|^n)²`, with `n ≤ k²`.
7. **π(x) − li(x) = O(√x log x)** from the `k = 1` case, which is RH.
   *Done without `li`* (`Artin/Analytic/Counting.lean`): the `k = 1` Kummer field is `ℚ`, so
   `KummerPsiBounds` already contains `θ(x) = x + O(√x log² x)`. Partial summation against
   `1 / log p` (discrete, `abs_sum_le_of_abs_sum_log_le`) applied to `θ_k(x) − θ_1(x)/n`
   compares `kummerCount a k x` with `kummerCount a 1 x / n` directly, and
   `kummerCount a 1 x = π(x) + O(log |a|)`.

The arithmetic steps 5–7 are assembled in `effectiveKummerChebotarev_of_kummerPsiBounds`:
`KummerPsiBounds a → EffectiveKummerChebotarev a` for `a ≠ 0` (sorry-free). The analytic core
(steps 1–4) has to prove `KummerPsiBounds a` from `HooleyHypothesis a` and
`DedekindContinuation (K_k)` (`kummerPsiBounds_of_hooley_of_continuation`), that is, for each
`K_k` the bound `PsiKBound` of `Artin/Analytic/Interface.lean`:
`|ψ_K(x) − x| ≤ C √x (log |d_K| + n log x) log x` for real `x ≥ 2`, with
`ψ_K(x) = Σ_{𝔭, m ≥ 1, N𝔭^m < x} log N𝔭` and one constant `C` for all squarefree `k`.

This is the largest part. Steps 1–3 generalise the erdos-985 analytic library from Dirichlet
L-functions to `ζ_K`.

#### Status of the analytic core (`Artin/Analytic/Core/`)

The chain `psiKBound_of_continuation → kummerPsiBounds_of_hooley_of_continuation →
conditional_artin_primitive_roots.parts.i_of_continuation` is assembled and builds. These are
proved: the explicit formula (A3), `Σ m_ρ/|ρ(ρ+1)| ≤ log |d_K| + 6n` and the local zero count (A2),
Hadamard and the zero locations (A1), `ψ_K = Σ Λ_K`, and the whole unsmoothing argument (A4)
except its two increment estimates. The remaining `sorry`s are each small, standard and
documented with a reference in their docstrings:

| Lemma | Statement | Route |
|---|---|---|
| `vonMangoldtK_le` | `Λ_K(n) ≤ [K:ℚ] Λ(n)` | `Σ_{𝔭∣p} f_𝔭 ≤ Σ e f = n` |
| `LSeries_vonMangoldtK` | `Σ Λ_K(n) n^{-s} = −ζ_K'/ζ_K(s)`, `Re s > 1` | Euler product over prime ideals |
| `dedekindZeta_ne_zero` | `ζ_K(s) ≠ 0`, `Re s > 1` | Euler product |
| `Z_ne_zero_of_re_eq_one` | `ζ_K(1+it) ≠ 0`, `t ≠ 0` | Mertens' `3 + 4 cos θ + cos 2θ ≥ 0` |
| `xi_growth` | `‖ξ_K(s)‖ ≤ C exp(C‖s‖ log(‖s‖+2))` | strip bound, functional equation, Stirling for `Re s ≥ 2` |
| `re_digamma_le` | `Re ψ(w) ≤ log(‖w‖+1)`, `Re w ≥ 1` | digamma series or Stirling |
| `gammaDiff_le` | `‖(y+h)Γ_K(y+h) − yΓ_K(y)‖ ≤ n h (log(y+h) + 8)` | explicit `tau` terms |
| `zeroDiff_le` | `Σ m_ρ ‖(y+h) zeroTerm(y+h) − y zeroTerm(y)‖ ≪ h √y (log\|d_K\| + n log(y+2)) log(y+2)` | `zeroSum_le` plus `zeroCount_le` on unit windows, split at `\|Im ρ\| = y/h` |

`effectiveKummerChebotarev_of_hooley` (without the continuation hypothesis) stays sorried in
`Artin/Interfaces.lean`.

### B. Sieve half: `EffectiveKummerChebotarev a → density > 0`

Write `N(x)` for the number of primes `p < x`, `p ∤ a`, with `a` a primitive root mod `p`.
`a` is a primitive root mod `p` iff no prime `q | p − 1` has `a^((p−1)/q) = 1`. Let
`ξ₁ = (1/6) log x`, `ξ₂ = √x / log² x` and `ξ₃ = √x log x`.

1. **Small primes** (`q ≤ ξ₁`): inclusion–exclusion over `k | ∏_{q ≤ ξ₁} q`, so
   `k ≤ x^{1/6 + o(1)}`, gives `Σ μ(k) kummerCount a k x = π(x) Σ μ(k)/[K_k:ℚ] + O(x^{2/3+ε})`.
   *Done* in `Artin/Sieve/Assembly.lean`, with `ξ₁ = ⌊(1/6) log x⌋`: `ξ₁# ≤ 4^{ξ₁} ≤ x^{1/3}`, so
   the error is `≤ x^{1/3} · C√x log(x^{4/3}) = o(π(x))`; the truncated density tends to `δ(a)`
   since `Σ μ(k)/[K_k:ℚ]` converges absolutely (from B5 and `n ≤ 2φ(n)²`).
2. **Medium primes** (`ξ₁ < q ≤ ξ₂`): `kummerCount a q x ≪ π(x)/q² + √x log x`, summed:
   `o(π(x))`. Needs `[K_q : ℚ] ≫ q²`. *Done* in `Artin/Sieve/Assembly.lean` (`medium_le`): the
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
   *Done* (`Artin/Kummer/Degree.lean`): `kummerDegree_le` (`≤ k φ(k)`),
   `exists_mul_totient_le_kummerDegree` (`k φ(k) ≤ 4^|a| [K_k:ℚ]` for `a ∉ {0, ±1}`, `k`
   squarefree), the exact `kummerDegree_mul_kummerEps` for `a` not a perfect power, with
   `ε(k)` stated as "`k` even and `√a ∈ ℚ(ζ_k)`", and the exact degree for every `a ≠ 0`,
   `kummerDegree_mul_kummerM` (`[K_k:ℚ] m(k) = k φ(k)`, `m(k)` the product of the primes
   `q ∣ k` for which `a` is a `q`-th power in `ℚ(ζ_k)`). The conductor of `ℚ(√a)` is
   `Artin/Kummer/Conductor.lean`: for `a = a₀ c²` and `k` squarefree, `√a ∈ ℚ(ζ_k)` iff
   `a₀ ≡ 1 (mod 4)` and `|a₀| ∣ k` (`exists_sq_cyclotomicField_iff` in `Density.lean`). `⇐` is
   quadratic Gauss sums; `⇒` uses Mathlib's `𝓞(ℚ(ζ_n)) = ℤ[ζ_n]` and the separability of
   `Φ_n` mod `p ∤ n` (no ramification theory needed).
6. **Positivity** of `δ(a) = Σ_k μ(k)/[K_k:ℚ]` for `a` not a square and not `−1`. This needs
   exact degrees, including the entanglement when `√a ∈ ℚ(ζ_k)`. Reference: Lenstra–Moree–
   Stevenhagen, *Character sums for primitive root densities*, arXiv:1112.4816.
   *Done* (`Artin/Kummer/Density.lean`, sorry-free): `kummerDensity_pos` for `a` not a perfect
   power, and `kummerDensity_pos_of_not_isSquare` for every `a` not a square and not `−1`
   (perfect powers included), via the exact degree, the conductor of `ℚ(√a)`, and an Euler
   factorisation over the finitely many primes where the local factor differs from
   `1 − 1/(q(q−1))`. Positivity only, not the closed form.
7. **Density**: `N(x) = δ(a) π(x) + o(π(x))`, and `π(x) → ∞`, give `HasDensity δ(a)`
   relative to the primes. Primes dividing `a` are finitely many.
   *Done*: `Artin/Sieve/Density.lean`; the whole of part B is assembled in
   `Artin/Sieve/Assembly.lean` (from B5/B6 as hypotheses) and `Artin/SieveHalf.lean`
   (`artin_of_effectiveKummerChebotarev`, sorry-free, B5/B6 discharged by `Artin/Kummer/`).
   The target theorem now depends only on part A (`effectiveKummerChebotarev_of_hooley`).

## Order of work

B4, B7 and the elementary lemma "primitive root iff no `a^((p−1)/q) = 1`" are unconditional
and small, so start there. Then B5/B6 (Kummer theory) and B3 (Brun–Titchmarsh) in parallel,
then B1/B2. Then A, which is the long pole and reuses erdos-985.
