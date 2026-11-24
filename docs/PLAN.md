# Plan: from `AnkenyTypeStatement` to `WangStatement` / `ShoupStatement`

## Done

`Shoup.ankenyType_of_GRH`: `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` under GRH, from erdos-985's
indicator expansion and Bach's weighted bounds (MTT Lemma 1).

## Inputs already available

For every squarefree `d | p − 1` let `E_d(x) = Σ_{n<x} Λ(n)(1 − n/x) 1[n is a d-th power mod p]`.
Since `1[d-th power] = (1/d) Σ_{χ^d = 1} χ`, erdos-985's bounds give, under GRH,
`|E_d(x) − S(x)/d| ≤ c(p,x) √x log p ≤ 13 √x log p` uniformly in `d` (one error term per `d`,
total non-principal coefficient `(d − 1)/d < 1`). This is the sieve axiom
`|S_d − A/d| ≤ B` of Iwaniec's shifted sieve as Shoup uses it (§6), with `A = S(x)`,
`B = 13 √x log p`, and the sifted set is `{n : gcd(ind n, p − 1) = 1}`.

## Missing: a lower-bound sieve with polynomially many terms

Shoup's §6 states: `T ≥ c₁ A / (log r + 1)² − c₂ r² B` (Iwaniec's shifted sieve), which with
`A ≈ x/2`, `B ≈ √x log p` gives `x ≍ r⁴ (log r + 1)⁴ log² p`. Wang's `r⁶` comes from a weaker
combinatorial sieve. Options, by cost:

1. **Brun's sieve** (Halberstam–Richert, *Sieve Methods*, Thm 2.1 in its combinatorial form):
   a lower bound with level `D = z^{O(1)}` over the primes `ℓ ≤ z` dividing `p − 1`, plus the
   Vinogradov split for primes `> z`. Gives `r^{O(1)} log² p`; matching Wang's exponent 6 needs
   care with the parameters. Needs: Bonferroni/Brun truncation inequalities over finite sets of
   primes (not in Mathlib), Mertens' product `∏_{ℓ ≤ z}(1 − 1/ℓ) ≫ 1/log z` (Mathlib has
   Chebyshev bounds; the product bound may be in mertens-rh / robin-rh). Estimate: 1500–3000
   lines.
2. **Iwaniec's shifted sieve / Rosser–Iwaniec linear sieve**: Shoup's exponent. Considerably
   heavier (Buchstab iteration with the `F`, `f` functions). Not recommended first.

Cheaper truncations do not reach a polynomial (sized 2026-11-24):

* Vinogradov split at `L ≈ 2ω` plus full inclusion–exclusion below `L`: `exp(O(ω / log ω))`.
* Brun's pure sieve (one Bonferroni depth `k ≈ e² log log ω`): `ω^{O(log log ω)}`.

No finite computation is needed for either target: the constant is existential, and every
odd prime is covered by the fallback "some primitive root is `< p`" when the bound exceeds `p`.
