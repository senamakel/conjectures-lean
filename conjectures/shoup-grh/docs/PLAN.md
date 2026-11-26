# Plan: from `PolyOmegaStatement 136` to `WangStatement` / `ShoupStatement`

## Done

* `Shoup.ankenyType_of_GRH`: `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` under GRH (full
  inclusion–exclusion, erdos-985's indicator expansion and Bach's weighted bounds).
* `Shoup.polyOmega_of_GRH : PolyOmegaStatement 136`: a Brun–Hooley lower-bound sieve over the
  primes dividing `p − 1` (`Shoup/Sieve/`), fed by the per-divisor count
  `|Σ_{n<x} w(n) 1[n is a d-th power] − S(x)/d| ≤ 13 √x log p` (`Sieve/Transfer.lean`).

## Where the exponent 136 comes from

Cost `M` = number of character sums (mass of the sieve weights); the bound is
`x ≤ 1089 (2 (J+1) M log p / θ)²` with `θ = ∏_{ℓ | p−1}(1 − 1/ℓ) ≥ 1/(r+1)`, `J + 1 ≤ 19 r`.

| Block | primes | level | `Σ 1/ℓ` bound | mass |
|---|---|---|---|---|
| top | `ℓ > 2^{2^t} ≥ 16 r` | 1 | `≤ 1/16` | `r + 1` |
| middle `i = t−1` | `(2^{2^{t−1}}, 2^{2^t}]` | 19 | `4` | `(r+1)^{19}` |
| middle `i < t−1` | `(2^{2^i}, 2^{2^{i+1}}]` | `2(t−1−i)+19` | `4` | `(2^{2^{i+1}})^{level}` |
| bottom | `ℓ = 2` | 3 (exact) | – | `8` |

The lower middle blocks multiply to `2^{46·2^{t−1}} < (16 r)^{46}`, so `M ≲ r^{66}`, and with the
`(J+1)/θ ≲ r²` factor, `x ≲ r^{136} log² p`.

## Levers, by cost

1. **Mertens-quality block sums.** With `Σ_{Y<ℓ≤Y²} 1/ℓ ≤ log 2 + c/log Y` instead of `4`, levels
   `≈ 5`–`7` suffice (`(eσ/m)^m e^{2σ}` small), giving `A` in the 30s–40s. Needs Mertens' first
   theorem two-sided (`log n! = Σ v_ℓ(n!) log ℓ`, Legendre) and discrete partial summation,
   about 300–500 lines. A cheaper half-step: `θ(2y) − θ(y) ≤ y log 4` (primes in `(y, 2y]` divide
   `C(2y, y)`) halves the shell bound to `2/k`, giving `σ ≤ 2` and `A ≈ 88`.
2. **Thresholds tied to `r`** instead of `2^{2^i}`: removes the doubling of the second block's
   size (`A` drops by about a third), at the price of rounding in the shell decomposition.
3. **`WangStatement` (`A = 6`).** Cost `≈ r³` is out of reach of this Brun–Hooley scheme with any
   constant-level blocks: Wang's own combinatorial argument would have to be transcribed (his
   1959 paper was not read; the exponent is as quoted by Shoup).
4. **`ShoupStatement`.** Shoup's §6 uses Iwaniec's shifted sieve,
   `T ≥ c₁ A/(log r + 1)² − c₂ r² B`, i.e. a linear lower-bound sieve with level `≈ z²`. That is
   the Rosser–Iwaniec theory (Buchstab iteration, the `F`, `f` delay-differential functions):
   several thousand lines, not started.

No finite computation is needed for any of these: the constant is existential, and every
odd prime is covered by the fallback "some primitive root is `< p`" when the bound exceeds `p`.
