# Scoping: ternary Goldbach under GRH (DETZ 1997) in Lean

Written 2026-11-24, before and during the first build. Every rate below was measured on this
box (95 cores, shared with other jobs; load 30–190 during the runs) with the checkers in
`GoldbachCheck.lean` compiled to native code and run by `native_decide`.

## The paper

Deshouillers, Effinger, te Riele, Zinoviev, *A complete Vinogradov 3-primes theorem under the
Riemann hypothesis*, Electron. Res. Announc. AMS 3 (1997) 99–104. Under GRH every odd `n > 5`
is a sum of three primes. The proof has three parts:

1. **Zinoviev's theorem** (J. Number Theory 65 (1997) 334–358): under GRH every odd
   `n > 10²⁰` is a sum of three primes. Circle method, all of `[0, 1)` treated as major arcs.
2. **A prime-gap lemma**: under GRH (in fact RH), for `6 ≤ n ≤ 10²⁰` there is a prime `p` with
   `4 ≤ n − p ≤ 1.615·10¹²`. It comes from Schoenfeld's bound
   `|θ(x) − x| < (1/8π) √x (log x − 2) log x` (for `x ≥ 2.3·10⁹`), which gives a prime in every
   interval of length `(1/4π) √x (log x − 2) log x + 2 log x`.
3. **A computation**: binary Goldbach for every even `4 ≤ m ≤ 10¹³` (Deshouillers–te Riele–
   Saouter up to `4·10¹¹`, extended to `10¹³` for this paper with a ladder of strong-pseudoprime
   primes certified by Jaeschke's bounds; about 53 CPU-hours on a Cray C98).

Unconditionally, Helfgott (2013, arXiv:1312.7748, 1501.05438) proved ternary Goldbach for every
odd `n > 5`; his analytic part covers `n ≥ 10²⁷`, the rest comes from Helfgott–Platt's prime
ladder and Oliveira e Silva–Herzog–Pardi's binary verification to `4·10¹⁸`.

## (a) The circle-method half

### What exists in Lean

| Project | Licence, toolchain | What it proves | What it assumes |
|---|---|---|---|
| Mathlib `fc4f59e5` | Apache-2.0, v4.36.0 | Dirichlet L-functions, their continuation and functional equation for primitive `χ` (`completedLFunction_one_sub`), Gauss sums (`norm_gaussSum_stdAddChar`), Dirichlet's theorem (`PrimesInAP`), a weak PNT | nothing: there is **no** circle method, no exponential sums over primes, no singular series |
| [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) | Apache-2.0, **v4.35.0**; needs [Garald1/RSBounds](https://github.com/Garald1/RSBounds) (Apache-2.0/MIT) | Helfgott's proof, no `sorry`, standard axioms only. `ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) : TernaryGoldbachFrom (10^27)`; the full statement with `BinaryGoldbachInput` added | `PlattGRH` (Platt's finite GRH check: zeros of `L(s, χ)`, `χ` primitive of conductor `q ≤ 4·10⁵`, height `≤ 10⁸/q`, lie on the line) and `BinaryGoldbachInput` (binary Goldbach to `4·10¹⁸`, OeSHP 2014). Its own Proth ladder to `10²⁷` (gap `< 4·10¹⁸`) is kernel-checked. About 13.4k build jobs, 8.5 h on 4 cores |
| [gersh/ternary-goldbach-lean](https://github.com/gersh/ternary-goldbach-lean) | Apache-2.0, v4.32.1 | Helfgott route, `ternary_goldbach` stated for odd `n ≥ 7` | 93 named external/source atoms (cited numerical and literature inputs) beyond the standard three |
| [subfish-zhou/liu-wang-ternary-goldbach-lean](https://github.com/subfish-zhou/liu-wang-ternary-goldbach-lean) | Apache-2.0, v4.33.0-rc1 | Liu–Wang route (`n ≥ e^3100`), in progress, says itself the main theorem is not proved | two open mathematical inputs |
| zzrice/TernaryGoldbach-Lean4 | none | skeleton of Helfgott's minor arcs with `sorry` | — |

No Lean project formalises a GRH circle method (Hardy–Littlewood 1923, Zinoviev 1997). The
riemann-hypothesis checkout (`507a75d91d`, 149k source files) has no circle method either: no
file mentions Goldbach, Vinogradov or the circle method, so a tier-U₀ discharge of the analytic
half is not available. It does contain explicit-formula material for Dirichlet characters
(`Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNT*.lean`), which might
shorten step 2 below; not examined further.

**The bounded route to the analytic half is not Zinoviev but calr3.** `PlattGRH` is a finite
part of GRH. With riemann-hypothesis's `DirichletLNonvanishingRightOfHalf`, a zero with
`1/2 < Re ρ < 1` is excluded directly, and a zero with `0 < Re ρ < 1/2` is excluded by the
functional equation for primitive `χ` (Mathlib's `completedLFunction_one_sub`; the Gamma factor
has no zeros there). So `DirichletLNonvanishingRightOfHalf → PlattGRH` is a short lemma, and
calr3 would give `TernaryGoldbachFrom (10^27)` at tier U. Two things block it today: calr3 is on
Lean v4.35.0 with a different Mathlib, so it cannot be a Lake dependency of a v4.36.0 /
`fc4f59e5` project without porting its ~2,500 RSBounds modules and its own tree; and its range
`n < 10²⁷` still rests on `BinaryGoldbachInput` (see (b)).

### The GRH proof, step by step, against the erdos-985 toolkit

Let `S(α) = Σ_{n ≤ N} Λ(n) e(nα)` (or with a smooth weight `w(n/N)`), so that
`R(N) = Σ_{n₁+n₂+n₃=N} Λ(n₁)Λ(n₂)Λ(n₃) = ∫₀¹ S(α)³ e(−Nα) dα`.

| Step | Content | In erdos-985 / Mathlib? |
|---|---|---|
| 1 | For `α = a/q + β` (Dirichlet, `q ≤ Q`, `\|β\| ≤ 1/(qQ)`), expand `e(na/q)` in characters mod `q`: `S(α) = (1/φ(q)) Σ_χ τ(χ̄) χ(a) Σ_n Λ(n) χ(n) e(nβ)` plus prime powers dividing `q` | Gauss sums and `\|τ(χ)\| = √q` for primitive `χ`: Mathlib. The reduction from imprimitive characters: not there |
| 2 | Explicit formula for `ψ(x, χ)` under GRH, **uniform in `q`**: `\|ψ(x, χ) − δ_χ x\| ≤ c₁ √x log²(qx)` for every `q` up to `Q` | erdos-985 has Bach's **weighted** sums `Σ_{n<x} Λ(n)χ(n)(1 − n/x)` with explicit constants (`bach_nonprincipal_of_GRH`, `bach_principal_of_GRH`), via Hadamard factorisation of `Λ(s, χ)`, a Perron formula with kernel `x^s/(s(s+1))`, and the zero sum at `s = 3/2`. The unweighted `ψ(x, χ)` (truncated Perron, kernel `x^s/s`, zero counting `N(T, χ)` in windows) is **not** there |
| 3 | Partial summation against `e(nβ)`: `Σ Λ(n)χ(n)e(nβ) = δ_χ T(β) + O(c₁ √N log²(qN)(1 + 2π\|β\|N))` | elementary once step 2 is in hand; not there |
| 4 | Every `α` is a major arc: the error in `S(α) − (μ(q)/φ(q)) T(β)` is `≤ √q · c₁ √N log²(qN)(1 + 2πN\|β\|)`, maximised over the Dirichlet box with `Q ≈ (2πN)^{2/3}`: about `2 c₁ (2πN)^{1/3} √N log² N = O(N^{5/6} log² N)` | not there |
| 5 | Main term: `∫ (μ(q)/φ(q))³ T(β)³ e(−Nβ)` summed over `q`, giving `𝔖(N) N²/2 + O(…)`, with the singular series `𝔖(N) = ∏_{p∣N}(1 − 1/(p−1)²) ∏_{p∤N}(1 + 1/(p−1)³) ≥ 1.32` for odd `N`, and the tail `Σ_{q > Q} φ(q)^{-2}` | Ramanujan sums, the Euler product and its lower bound: not there (all elementary) |
| 6 | Error: `\|∫ (S³ − main)\| ≤ 3 max\|E\| ∫ \|S\|² = 3 max\|E\| · Σ Λ(n)² ≤ 3 max\|E\| N log N` (Parseval) | Parseval on `AddCircle`: Mathlib has it; `Σ Λ² ≤ N log N`: easy |
| 7 | Remove prime powers (`O(√N log² N)` per factor) and conclude `R(N) > 0` with three primes | elementary |

**Threshold this would give.** Step 6 requires `𝔖(N) N²/2 > 3 · 2c₁(2π)^{1/3} N^{5/6} log² N ·
N log N`, i.e. `N^{1/6} > C log³ N` with `C ≈ 9·2c₁(2π)^{1/3}/1.32`. With `c₁ ≈ 1/2` that is
`C ≈ 13`, solved by `log N ≈ 100`, so **`N₀ ≈ 10⁴³`**. A Cesàro-weighted `S(α)` (to use
erdos-985's weighted formula directly) changes constants, not the exponent `5/6`. Zinoviev
reaches `10²⁰` by a much more careful treatment (smoothing, separate large-`q` estimates,
`q`-dependent Dirichlet boxes, sharp zero-sum constants). Getting a Lean circle method below
about `10²⁴` (see (b)) means formalising Zinoviev's paper essentially line by line, plus the
uniform unweighted explicit formula of step 2 for every modulus up to `Q ≈ 10¹⁶`. That is a
multi-month project; nothing in this repository attempts it.

## (b) The finite half

### Design

The cheapest sound certificate, as built here:

* **Binary Goldbach up to `G`**: an odd-only segmented sieve of Eratosthenes (`markFrom`,
  `sieve`), base primes produced by the same sieve, and for each even `m` a search over the odd
  primes `p ≤ 9999` for an unmarked `m − p`. Soundness (`sieve_spec`, `prime_of_unmarked`,
  `goldbachChunk_sound`) is proved once; an unmarked odd `x ≤ B²` is prime because every odd
  prime `≤ B` is in the sieving list.
* **A prime ladder up to `X`** with consecutive gaps `≤ G − 4`: each rung is a prime
  `c = k·p^e + 1` (`p ∈ {2, 3, 5, 7}`, `p^{2e} > c`) certified by **Pocklington's criterion**
  (`a^{c−1} ≡ 1`, `gcd(a^{(c−1)/p} − 1, c) = 1`; proved as `prime_of_pockOK` from Mathlib's
  `orderOf_eq_prime_pow` and `ZMod.orderOf_dvd_card_sub_one`). The search for the next rung
  is untrusted; the checker re-verifies the certificate and the gap of each rung.
* Odd `n ≤ G + 3` is `3 + (n − 3)`. For larger odd `n ≤ X`, the ladder gives a prime `q` with
  `4 ≤ n − q ≤ G`, and `n − q` is even.

Using only Proth's base `2` failed the probability check: at `c ≈ 10²⁰` the base forces
`2^e ≥ 2^34`, so a window of `2·10¹²` holds only about 116 candidates (about 5 primes), and
some of the `~1.4·10⁷` windows near the top would be empty. With the four bases `2, 3, 5, 7`
a window holds about 17 primes on average.

**The GRH Miller test** from `../miller-grh` is the other sound primality test available, and
it would be legitimate in the main library with GRH as a hypothesis. It is far too slow here:
with Bach's constant as proved there (`21/5`) it needs every base up to `(21/5)·log² n`, about
9,000 modular exponentiations for `n ≈ 10²⁰`, against 1–3 for Pocklington. It would also make
the finite range conditional, which Pocklington does not.

### Measured rates

| Check | Rate (one core, native, shared box) |
|---|---|
| Binary Goldbach, sieve segments of `10⁶`, near `10¹²` | `1.05·10⁹` even-range span in 23 s: about **`4.5·10⁷` per second** |
| Ladder near `10¹⁹–10²⁰` (Nat arithmetic beyond `2⁶⁴`, GMP) | `10⁵` rungs in 30 s: about **`0.3–0.4 ms` per rung** (search plus re-check) |

### What fits

For a ladder to `X` with gap `G`, the cost is about `G/r + (X/G)·t` with
`r = 4.5·10⁷ s⁻¹`, `t = 4·10⁻⁴ s`; the optimum `G = √(X t r)` costs `2√(X t / r)`.

| Target | `G` | Binary cost | Ladder | Total | On 95 cores |
|---|---|---|---|---|---|
| DETZ's `X = 10²⁰` (built here) | `2·10¹²` | `4.4·10⁴` s | `5·10⁷` rungs, about `2·10⁴` s | about 18 CPU-hours | about 15 min idle box |
| One day on 95 cores (`8.2·10⁶` CPU-s) | `1.8·10¹⁴` | `4·10⁶` s | `10¹⁰` rungs, `4·10⁶` s | 1 day | **`X ≈ 2·10²⁴`** |
| Helfgott's `X = 10²⁷` | `4·10¹⁵` | `10⁸` s | `2.4·10¹¹` rungs, `10⁸` s | about `1.9·10⁸` s | about 23 days; about 7 days if rungs get 10× cheaper (calr3 batches 32 Proth checks per modular product) |

(The rates degrade slowly with height: the sieve's base-prime overhead grows like `√G`, so the
last two rows are optimistic by perhaps a factor 2.)

RH prime gaps instead of a ladder (Schoenfeld, which `../schoenfeld-rh` targets): a prime in
every `(x − (1/4π)√x log² x, x]` needs `G ≥ (1/4π)√x log² x`, which is `1.7·10¹²` at `x = 10²⁰`
but `10¹⁶` at `x = 10²⁷`. Below `10²⁰` the ladder is cheaper and needs no RH at all, so the
finite range here is tier D.

### Compared with (a)

The finite half reaches DETZ's `10²⁰` cheaply and could reach about `10²⁴` in a day. A circle
method assembled from the erdos-985 toolkit plausibly gives `N₀ ≈ 10⁴³`: a gap of about 19
orders of magnitude, which no computation closes (the cost grows like `√X`: `10⁴³` would be
about `10¹⁰` days). Only a Zinoviev-quality analytic part (`N₀ ≤ 10²⁴`) meets the computation.

## (c) Verdict

* **Tier U for the full statement is not reachable in this push.** The finite half is done and
  cheap; the analytic half needs an explicit GRH circle method with `N₀ ≤ 10²⁴`, which does
  not exist in any Lean library and would take months to formalise.
* **Realistic end state, built here:**
  * `ternary_goldbach_upTo : TernaryGoldbachUpTo (10^20)` — tier D, standard axioms plus 300
    documented `native_decide`.
  * `ternary_goldbach_of_GRH (hGRH) (hZ : ZinovievTheorem)` — tier C + H, Zinoviev's theorem
    as a named `Prop`. Its `Unconditional/` form `ternary_goldbach_of_zinoviev` is tier U + H.
* **Most promising next step for a tier-U result (not in this repo's scope):** port calr3
  (Helfgott) to Lean v4.36.0 / Mathlib `fc4f59e5`, prove `DirichletLNonvanishingRightOfHalf →
  PlattGRH` with Mathlib's functional equation, and replace `BinaryGoldbachInput` by the
  ladder and sieve of this repository extended to `10²⁷` (one to three weeks on 95 cores, see the table in (b)). That would
  give ternary Goldbach at tier U with no cited hypothesis at all, through Helfgott rather than
  DETZ.
