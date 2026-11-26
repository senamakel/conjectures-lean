# Sun's Conjecture 3.25 (OEIS A243164) under GRH: feasibility

Date: 2026-11-26. Scope: Phase 0 of the `sun-a243164-grh` brief, plus the start of Phase 1.

**Target.** Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641
(v12; also Proc. 7th China–Japan Seminar, World Sci. 2015, 169–187), Conjecture 3.25, first
part (dated 2014-06-01): *for every integer `n > 6` there is a prime `q < n` such that `q·n` is a
primitive root modulo `p_n`*, the `n`-th prime. OEIS A243164 ("Conjecture: (i) a(n) > 0 for all
n > 6"). Sun checked it for `n ≤ 2·10^5`. The second part (`q(n − q)` a primitive root, A243403)
is a binary problem and is out of scope.

**Verdict.** Feasible, mostly by reusing what is already in the workspace. With the
McGown–Treviño–Trudgian sieve that grosswald-grh already proves in Lean, and Mathlib's
unconditional bound `π(N) ≥ N log 2 / log N`, the GRH argument closes for **every prime
`p ≥ 10^8`, whatever `ω(p − 1)` is**. The finite range is therefore erdos-985's range: all
5,761,455 primes below `10^8`. The checker is erdos-985's checker plus an exact prime count.
Estimated cost: about 0.5 CPU-hours. Without the sieve the threshold depends on `ω` and goes up
to `4.5·10^10` (scout's numbers confirmed). Literature label: *RH-consequence*. No proof was
found anywhere (search below).

## 1. The analytic inequality

Notation. `P = p_n` prime, `n = π(P)`, `x = n` (search length), `a = n mod P` (a unit, since
`n < P`), `S₀(x) = Σ_{m<x} Λ(m)(1 − m/x)`, `S_χ(x) = bachSum χ x`, `ω = ω(P − 1)`.

Erdos-985 inputs (exact Lean names, all for any `x ≥ 1`):

- `Erdos985.Analytic.bach_nonprincipal_of_GRH hGRH P χ hχ x hx :
  ‖bachSum χ x‖ ≤ bachC P x * √x * Real.log P` for every `χ ≠ 1` modulo the prime `P`, with
  `bachC p x = (2/3)(1 + 2/√x + 3/x^{3/2})(1 + (5/3)/log p) + (log x + 2)/(√x log p)`
  (`Erdos985/Bach.lean`).
- `Erdos985.Analytic.bach_principal_of_GRH hGRH x hx : |S₀(x) − x/2| ≤ √x/20 + 3`.

**Twist.** `qn` is a primitive root iff `q ∈ a⁻¹G`. In every character expansion,
`χ(qa) = χ(a)χ(q)` and `|χ(a)| = 1`, so `Σ_m Λ(m)w(m)χ(am) = χ(a)·S_χ(x)` has the same bound.
Grosswald's sieve identities (`Grosswald.Sieve.norm_V_sub_le`,
`Grosswald.Sieve.norm_V_insert_sub_le`) go through with `ind ℓ (a·m)` in place of `ind ℓ m`.

**Prime powers.** In erdos-985 and grosswald-grh, "`q^k` is a primitive root" forces "`q` is a
primitive root", so the indicator vanishes on the whole support of `Λ`. Here it does not:
`q^k·n ∈ G` says nothing about `q·n`. On a prime `m = q < x` the sieve combination
`C(m) = Σ_{i∈S} ∏_{E∪{i}} ind(am) − (|S| − 1) ∏_E ind(am)` is `≤ 0` (as in
`Grosswald.Sieve.pointwise`); on a proper prime power it is `≤ 1`. So the left side is at most

`E(x) = Σ_{m<x, m = q^k, k≥2} Λ(m)(1 − m/x) ≤ ψ(x) − θ(x) ≤ log 4 · (√x + (⌊log₂ x⌋ − 2)·x^{1/3})`,

from Mathlib's `Chebyshev.psi_eq_theta_add_sum_theta` and `Chebyshev.theta_le_log4_mul_x`.

**The inequality.** Let `F` be the prime factors of `P − 1`, `E ⊆ F` (kept), `S = F \ E`
(sieved), `s = |S|`, `δ = 1 − Σ_{ℓ∈S} 1/ℓ > 0`, `θ_E = ∏_{ℓ∈E}(1 − 1/ℓ)`, and
`K = 2^{|E|}(2 + (s − 1)/δ) − 1` (grosswald's `KQ`). If no prime `q < n` has `qn` a primitive
root modulo `P`, then

```
δ θ_E · ( S₀(x) − K · bachC(P, x) √x log P )  ≤  E(x)                        (★)
```

With `S = ∅` (no sieve, `δ = 1`, `K = 2^ω − 1`, `θ_E = φ(P−1)/(P−1)`), (★) is erdos-985's
`principal_le_of_no_prime_primitive_root` with the extra right-hand side `E(x)`. So a
counterexample is impossible as soon as

```
x/2 − √x/20 − 3 − K · bachC(P, x) √x log P − E(x)/(δ θ_E)  >  0.              (★★)
```

**Search length.** `x = n = π(P)`. Mathlib's `Chebyshev.pi_ge_of_four_le` gives
`π(P) ≥ P log 2 / log P` with no hypothesis (artin-grh uses it as `div_log_le_primeCounting`).
schoenfeld-rh's `thetaBound_of_RH` would give `x ≥ (P − ¼√P log²P)/log P` instead, but it
needs RH as a second hypothesis and only lowers the thresholds by a factor of about 1.5. The
Mathlib bound suffices, so that is the plan.

**Worst case for a given `ω`.** Take `E` = the `k` smallest prime factors of `P − 1`. The
`i`-th smallest prime factor is at least the `i`-th prime, so `θ_E ≥ ∏_{i≤k}(1 − 1/p_i)` and
`δ ≥ 1 − Σ_{k<i≤ω} 1/p_i`. Also `P ≥ 1 + p_1⋯p_ω`. This is exactly grosswald-grh's domination
argument (`Grosswald.Alg.dominates`, `Grosswald.Alg.lower_le`, `Grosswald.Combi.prod_le_prod_of_dominates`).

## 2. Threshold table (computed)

`P₀(ω)` is the least `P` (on a grid of 200 points per decade, up to `10^16`) from which (★★)
holds for every larger `P`, in the worst-case configuration above. "Check" is the range of
primes with that `ω` that is left to compute (empty when `P₀ ≤ 1 + p_1⋯p_ω`). The script is
reproduced in §7.

| ω | `1+∏p_i` | no sieve, Mathlib π | no sieve, RH π | **sieve, Mathlib π** | sieve, RH π |
|---|---|---|---|---|---|
| 1 | 3 | 1.8·10⁴ | 1.5·10⁴ | 1.8·10⁴ | 1.5·10⁴ |
| 2 | 7 | 1.1·10⁵ | 8.5·10⁴ | 1.1·10⁵ | 8.5·10⁴ |
| 3 | 31 | 5.8·10⁵ | 4.1·10⁵ | 5.8·10⁵ | 4.1·10⁵ |
| 4 | 211 | 3.0·10⁶ | 2.0·10⁶ | 2.2·10⁶ | 1.5·10⁶ |
| 5 | 2311 | 1.5·10⁷ | 9.9·10⁶ | 6.5·10⁶ | 4.3·10⁶ |
| 6 | 30031 | 7.6·10⁷ | 5.0·10⁷ | 1.6·10⁷ | 1.1·10⁷ |
| 7 | 5.1·10⁵ | 3.8·10⁸ | 2.5·10⁸ | 3.4·10⁷ | 2.3·10⁷ |
| 8 | 9.7·10⁶ | 1.9·10⁹ | 1.2·10⁹ | **6.9·10⁷** | 4.6·10⁷ |
| 9 | 2.2·10⁸ | 9.3·10⁹ | 6.2·10⁹ | none (1.3·10⁸ < 2.2·10⁸) | none |
| 10 | 6.5·10⁹ | 4.5·10¹⁰ | 3.0·10¹⁰ | none | none |
| 11 | 2.0·10¹¹ | 2.2·10¹¹ (just above) | none | none | none |
| ≥ 12 | ≥ 7.4·10¹² | none | none | none | none |

The "no sieve, RH π" column reproduces the scout's table (4.7·10⁷ … 3.0·10¹⁰; the small
differences come from the prime-power term, which the scout took as `1.5√x` and which is
divided by `θ` here).

Relative margin of (★★), `(LHS)/(x/2)`, at `P = max(10^8, 1 + p_1⋯p_ω)` with the sieve and
Mathlib's `π` bound. In every case the best `E` is the two smallest prime factors (`|E| = 2`),
or all of them when `ω ≤ 3`:

| ω | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 15 | 20 | 30 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| margin | 98% | 95% | 89% | 80% | 69% | 54% | 36% | **14%** | 20% | 77% | 94% | 98% | 100% | 100% | 100% |

Without the sieve the margin at the primorial is still negative for `ω = 9, 10, 11`
(−404%, −135%, −3.5%) and positive from `ω = 12` (59%, 98% at `ω = 15`). No `(ω, P)` with
`ω ≤ 39` and `P` from `1 + p_1⋯p_ω` up to `10^30` times it had both margins `≤ 0`.

**Conclusion.** One threshold for every `ω`: `P ≥ 10^8`. The tight case is `ω = 8` at
`P = 10^8` (14%), then `ω = 9` at its primorial (20%). That is a better margin than
erdos-985's own `ω = 9` case (about 4%).

## 3. The finite range

- **What is needed:** every prime `P < 10^8` with `n = π(P) ≥ 7`: 5,761,455 − 6 = 5,761,449
  primes (strictly only `P < 6.9·10^7` is needed, but `10^8` keeps erdos-985's chunking).
  By `ω(P − 1)`: 1: 3, 2: 481,361, 3: 1,683,727, 4: 2,136,712, 5: 1,175,855, 6: 264,657,
  7: 18,914, 8: 220. No large-`ω` primes need checking beyond `10^8`.
- **Per prime:** find a prime `q < n` with `(q·n mod P)^{(P−1)/r} ≢ 1 (mod P)` for every prime
  `r | P − 1`. The least such `q` never exceeds 211 for `P < 10^8` (at `P = 21525571`); by
  `ω`: 2, 67, 139, 193, 193, 211, 163, 101. erdos-985's `smallPrimes` (primes below 2000) is
  more than enough.
- **Knowing `n`.** The checker carries a running prime count. A chunk `[lo, lo + L)` takes the
  literal `c₀ = π(lo − 1)` and returns `c₁`. Primality must now be decided *exactly* for every
  number in the chunk (erdos-985 only needs "if prime then OK", so it short-circuits
  composites through a Fermat test): `isPrimeB m := m ≥ 2 ∧ (m = 2 ∨ (m odd ∧ 2^{m−1} ≡ 1 ∧
  m.minFac = m))`, whose correctness is a two-line lemma. The chunk theorem is
  `checkFromC lo L c₀ = some c₁` by `native_decide`; soundness says "if `c₀` counts the primes
  below `lo`, then `c₁` counts those below `lo + L`, and every prime `P` in the chunk with index
  `n > 6` has its `q`". Chaining the 20 chunks from `π(−1) = 0` needs no separate prime count.
- **Cost.** erdos-985's 20 chunks of `5·10^6` take about 60 s each (1,200 CPU-s in all,
  `README.md`, "Axioms and unconditional version"). The per-prime work here is the same (factor
  `P − 1` with `primeFactorsList`, about 3 candidates `q`, `ω` modular powers each). What is
  added is the exact `minFac` on each of the 5.76·10⁶ primes (at most √P/2 ≈ 5000 trial
  divisions each, about 3·10¹⁰ in all, on the order of 100–300 CPU-s compiled). Estimate:
  **20–40 CPU-minutes, 20 `native_decide` axioms**, each chunk well under the one-hour cap. A C
  version of the same check (`ver.c`, §7) does the whole range in 7 s.

## 4. Numerical verification (done, 2026-11-26)

- Every `n ≥ 7` with `p_n < 10^8` (5,761,449 values): no counterexample; least `q ≤ 211`.
  Segmented sieve plus trial-division factorisation, C, 7 s.
- Every `n ≥ 7` with `p_n < 10^10`: see the addendum at the end (run finished after this
  section was written).
- Large `ω` beyond the sieve range (exact `n = π(P)` by the Lucy–Hedgehog method): every prime
  `P ≡ 1 (mod 2·3·…·23)` below `10^11` (110 primes, `ω ≥ 9`, least `q ≤ 139`), every prime
  `P ≡ 1 (mod 2·3·…·29)` below `10^12` (41 primes, `ω ≥ 10`, least `q ≤ 163`), every prime
  `P ≡ 1 (mod 2·3·…·31)` below `10^13` (13 primes, `ω ≥ 11`, least `q ≤ 107`). All pass.
  `π` was cross-checked on small cases (`π(211) = 47`, `π(421) = 82`).

## 5. Plan for Lean

New folder `conjectures/sun-a243164-grh/` (package `SunA243164`), requiring erdos-985 and
grosswald-grh by path (no rebuild of either; only their `.lake` is linked).

| File | Content | Reuse |
|---|---|---|
| `Statement.lean` | `SunA243164Statement : ∀ n, 6 < n → ∃ q, q.Prime ∧ q < n ∧ orderOf ((q * n : ℕ) : ZMod (nth Prime (n − 1))) = nth Prime (n − 1) − 1`; `DirichletLNonvanishingRightOfHalf` from erdos-985 | `Erdos985.DirichletLNonvanishingRightOfHalf` |
| `Assembly.lean` | the theorem from two explicit hypotheses: `AnalyticAbove 10^8` (every prime `P ≥ 10^8` is fine) and `VerifiedBelow 10^8` | — |
| `PrimeIndex.lean` | `π(nth Prime (n−1)) = n`; `n ≥ P log 2 / log P` | `Nat.primeCounting'_nth_eq`, `Chebyshev.pi_ge_of_four_le` |
| `PrimePowers.lean` | `E(x) ≤ log 4 (√x + (⌊log₂x⌋ − 2) x^{1/3})` | `Chebyshev.psi_eq_theta_add_sum_theta`, `Chebyshev.theta_le_log4_mul_x` |
| `TwistedSieve.lean` | (★) with the twist `a`: copies of `Grosswald.Sieve.{V, W, V_expand, norm_V_sub_le, norm_V_insert_sub_le, principal_le_sieve}` with `ind ℓ (a*m)`, and the pointwise bound `≤ 1` on proper prime powers | grosswald's `fac_eq`, `ind`, `coef`, `abs_coef_mul`, `aR`; erdos-985 `Indicator.Lemmas` |
| `Numerics.lean` | (★★) for `P ≥ 10^8`: `ω ≤ 11` with `|E| = min(ω, 2)` through a rational checker in the style of `Grosswald.Crit.crit_sound` (tangent bounds for `log`), worst case through `Grosswald.Alg.LOk_spec`/`dominates`; `ω ≥ 12` with no sieve and `2^ω` bounded through `Erdos985.pow_card_primeFactors_mul_le` | as named |
| `Compute/Checker.lean`, `Compute/ChunkNN.lean` | counting checker, 20 chunks | `Erdos985.Compute.{powMod, powMod_eq, smallPrimes, zmod_pow_eq_one_iff}` |
| `Main.lean` | `sunA243164_of_GRH : DirichletLNonvanishingRightOfHalf → SunA243164Statement` | — |
| `Unconditional/SunA243164Unconditional.lean` | one-line discharge with `LFunction_ne_zero_of_half_lt_re` | erdos-985's pattern |

New mathematics: none beyond the twist and the prime-power term; new Lean is roughly
`TwistedSieve` (about 350 lines, mostly adapted), `Numerics` (about 300), `Compute` (about
200), and small glue. **Effort: M** (a few days for one prover).

**Risks.**
1. The tight case `ω = 8` at `10^8` has a 14% margin. The Lean tangent-line bounds for `log`
   cost a few percent (erdos-985 lost about 1 point at its `ω = 9`), so this should be safe. If
   not, raise the range to `2·10^8` (one more `native_decide` hour at most).
2. The "`i`-th smallest factor `≥ p_i`" domination is proved in grosswald-grh for its
   `InClass` predicate, which hard-codes `10^13 < p`. It has to be restated (copy, about 40
   lines) rather than imported.
3. Grosswald's `pointwise` lemma is stated for its own `hno`. The twisted version with the
   prime-power term is new, but it is elementary.
4. Exact primality in the checker: `Nat.minFac` in compiled code on 5.76·10⁶ primes. Time one
   chunk first.

## 6. Novelty search (2026-11-26)

| Where | Query | Found |
|---|---|---|
| OEIS JSON API | `id:A243164` | revision 12 (2014-06-01); comments are the conjecture and Sun's check to `2·10^5`; no proof claim |
| Exa (3 queries) | proof of A243164 / Sun Conj. 3.25, unconditional or under GRH; QRH/Zenodo corollaries; MathOverflow/MSE | Sun's arXiv:1402.6641 and his talk slides (statement only); dr vengy's Zenodo notes 23405183, 23423889, 23352867, 23623383, 23621867 (Erdős 985, Vinogradov, under QRH: none mentions `q·n` or A243164); MO 135234 and 62851 (Artin-type questions, unrelated) |
| GitHub code search | `A243164`; "primitive root modulo prime(n)" | OEIS mirrors only (africamonkey/OEIS-Spider cross-references, Kuberwastaken/c5-k4 on A239957) |
| formal-conjectures | PR search `243164`, "Sun primitive root"; code search `243164` | no statement, no PR (only unrelated OEIS PRs #7672, #7064, #5568, #1622) |

Nothing proves the statement or its GRH version. The deduction is not in the literature as
far as these searches reach. Label *new* still needs the owner's sign-off (AGENTS.md).

## 7. Reproduction

Scripts (scratch, not kept in the repository): `thr.py` (thresholds, the formulas of §1
verbatim: `bachC`, `E(x)`, `x = P log 2/log P` or the RH variant, worst-case `θ_E`, `δ`, `K`),
`ver.c` (segmented sieve to `LIM`, running index `n`, least `q`), `big.c` (Lucy–Hedgehog
`π(P)` and the check for `P ≡ 1 (mod primorial)`).
