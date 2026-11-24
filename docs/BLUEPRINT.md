# Blueprint: a prime in `(x, x + 2√x log x]` under RH

Notation: `Λ` von Mangoldt, `Ψ₁(n) = Σ_{k<n} Λ(k)(n − k)`, `ξ = xiZeta` (erdos-985), `m_ρ` the
multiplicity of a zero `ρ` of `ξ`, `L(s) = 1/s + 1/(s−1) + ½ log(s/2) − ½ log π`.
Every step below is a Lean theorem; the file is given in brackets.

## Step 1. Second difference of `Ψ₁` against the von Mangoldt mass  [`Cramer/Psi1.lean`]

`psi1N_second_diff_le`: for all naturals `a, h`,
`Ψ₁(a+2h) − 2Ψ₁(a+h) + Ψ₁(a) ≤ h · Σ_{a ≤ k < a+2h} Λ(k)`.

Termwise: `max(a+2h−k, 0) − 2 max(a+h−k, 0) + max(a−k, 0)` is `0` for `k < a` and at most `h`
for `a ≤ k < a+2h`. No analysis.

## Step 2. Second difference of one zero term  [`Cramer/SecondDiff.lean`]

For `Re ρ = 1/2`, `a > 0`, `h ≥ 0`, `g(t) = t^{ρ+1}/((ρ+1)ρ)` and
`D_ρ = g(a+2h) − 2g(a+h) + g(a)`:

* (b) `‖D_ρ‖ ≤ h² a^{−1/2}` (`norm_second_diff_gρ_le`): two mean-value steps, `g'' = t^{ρ−1}`,
  `|t^{ρ−1}| = t^{−1/2} ≤ a^{−1/2}`;
* (a) `‖D_ρ‖ ≤ 4(a+2h)^{3/2}/‖ρ(ρ+1)‖` (`norm_second_diff_gρ_le'`): triangle inequality.

## Step 3. Weighted zero sum under RH  [`Cramer/ZeroSum.lean`]

`weighted_zeroSum_le`: if `0 ≤ w(ρ) ≤ min(A, B/‖ρ(ρ+1)‖)`, `0 ≤ B ≤ Aσ²`, `σ > 3/2`, then
`Σ_ρ m_ρ w(ρ) ≤ 2Aσ (L(1/2+σ) + 1/40)`.

* Pointwise (`weight_le`, RH puts `ρ = 1/2 + iγ`): `min(A, B/(¼+γ²)) ≤ 2Aσ²/(σ²+γ²)
  = 2Aσ Re 1/(s−ρ)` with `s = 1/2 + σ`; and `Re 1/ρ > 0`.
* Hadamard (`zeroSum_re_le`, erdos-985's `hadamard_logDeriv` at `s` and at `0`):
  `Σ m Re(1/(s−ρ) + 1/ρ) = Re ξ'/ξ(s) − Re ξ'/ξ(0)`.
* `Re ξ'/ξ(s) ≤ L(s)` for real `s > 2` (`re_logDeriv_xi_le`): `Re ζ'/ζ(s) ≤ 0`, and
  `ψ(s/2) ≤ log(s/2)` (erdos-985's `rD_bounds`, convexity of `log Γ`).
* `−Re ξ'/ξ(0) = Re Λ₀(1) = (2 + γ − log 4π)/2 < 1/40` (`neg_re_logDeriv_xi_zero_lt`).

The choice of weight is optimal for this method: `min(1, 1/t) ≤ α/(1 + t/β)` forces
`α√β ≥ 2`, which is where the asymptotic constant `2` of the headline comes from.

## Step 4. The explicit formula, differenced  [`Cramer/Identity.lean`]

`psi1N_formula`: `n ×` erdos-985's `explicit_formula_zeta` gives
`Ψ₁(n) = Re Σ m_ρ n·zeroTerm(n,ρ) + n(Re gammaPart(n) + log n) + n²/2 − 7n/2 + 3 − (n−1) Re ζ'/ζ(2)`.

`V_second_diff`: the second difference of `n·zeroTerm(n,ρ)` is exactly `−D_ρ` (the affine
parts `(n−1)/(2−ρ)`, `n/ρ`, `1/(1+ρ)` cancel).

`psi1N_second_diff_ge` (RH): for `a, h ≥ 1`, `σ > 3/2`, `4(a+2h)^{3/2} ≤ h² a^{−1/2} σ²`,
`Ψ₁(a+2h) − 2Ψ₁(a+h) + Ψ₁(a) ≥ h² − 2h²a^{−1/2} σ (L(1/2+σ) + 1/40) − 3`
(`n²/2` gives `h²`; `n(Re gammaPart + log n) ∈ [n − 3/2, n]` gives `≥ −3`; Steps 2–3 bound
the zero part).

## Step 5. Prime powers  [`Cramer/PrimePowers.lean`]

`sum_vonMangoldt_not_prime_le`: for `1 ≤ a ≤ b ≤ 2a`,
`Σ_{a ≤ k < b, k ∉ P} Λ(k) ≤ log b · ((√b − √a + 1) + (b^{1/3} + 1))`.
`k ↦ minFac k` is injective on proper prime powers in `[a, b)` (as `b ≤ 2a`), with image in
`{p : a ≤ p² < b} ∪ {p : p³ < b}`.

## Step 6. A prime in `[a, a+2h)`  [`Cramer/Interval.lean`]

`exists_prime_Ico_of_RH`: with `σ = 2b/h` (`b = a+2h`), Steps 1, 4, 5 give: if `1 ≤ h`,
`2h ≤ a` and `IntervalCondition a h`, i.e.
`log b ((√b−√a+1) + (b^{1/3}+1)) < h − (4b/√a)(L(1/2 + 2b/h) + 1/40) − 3/h`,
then some prime lies in `[a, a+2h)`.

## Step 7. The range `x ≥ 10^6`  [`Cramer/Large.lean`]

`exists_prime_of_RH_large`: `a = ⌊x⌋ + 1`, `h = ⌈√x log x⌉ − 1`. With `x = t⁶`, `t ≥ 10`,
`ℓ = log x ∈ [13, 6.48 + 0.75t]` (`key_ineq`):
`√b − √a ≤ ℓ`, `log b ≤ ℓ + 0.7`, `b^{1/3} ≤ 1.26t²`, `L + 1/40 ≤ ℓ/4 − 1.46`,
`4b/√a ≤ 4t³ + 4/t³ + 8ℓ`; the condition reduces to
`(ℓ+0.7)(ℓ+2+1.26t²) + 2ℓ² + 3 < 5.84t³` (`poly_final`).

## Step 8. The range `2 ≤ x < 10^6`  [`Cramer/Small.lean`]

`exists_prime_small` (no hypothesis): a chain of 99 primes `2 = q₀ < … < q₉₈ = 1005161`
with `(q_{i+1} − q_i)² · 10⁶ ≤ 4 q_i (693 ⌊log₂ q_i⌋)²`, checked by `decide`
(kernel reduction, no `native_decide`); each `q_i` is proved prime by `norm_num`.
`gap_le` turns the check into `q_{i+1} ≤ q_i + 2√q_i log q_i`, and `x ↦ x + 2√x log x` is
monotone.

## Step 9. Assembly  [`Cramer/Main.lean`]

`primeInShortInterval_of_RH : PrimeInShortInterval 2` (Steps 7 + 8),
`primeGapExplicit_of_RH : PrimeGapExplicit 2` (take `x = p_n`; the next prime is at most any
larger prime), `cramer_of_RH : CramerGapBound` (`IsBigO.of_bound 2`).

## Numbers worth keeping

* The exact (unsimplified) Step-6 condition holds for `c = 2` from `x ≈ 1.9·10^3` on; the
  simplified bounds of Step 7 need `x ≥ 10^6`, which costs nothing because the chain check is
  tiny.
* Asymptotically the margin is `≈ 2√x log(π log x)`: the constant `2` is sharp for this weight,
  and `c < 2` fails for `x ≳ 10^{52}` (`c = 1.8`) with this argument.
* Carneiro–Milinovich–Soundararajan's `22/25` uses Fourier optimisation (Beurling–Selberg
  majorants and the Guinand–Weil formula), which is out of reach of erdos-985's toolkit.
