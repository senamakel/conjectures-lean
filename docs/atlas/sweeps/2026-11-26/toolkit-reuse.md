# Lane `toolkit-reuse`: short corollaries of theorems we already prove in Lean

Date 2026-11-26. Research only: nothing built, no repo edited. Python run with `-I` for every
number below. Claims I could not confirm from a primary source are marked *(unverified)*.
Lean statements are quoted from `~/work/personal/conjectures-lean/conjectures/<name>/`.

## Part 1. Premise inventory (what our 28 projects prove, tier U unless noted)

All are unconditional Lean theorems via `riemannHypothesis` / `LFunction_ne_zero_of_half_lt_re`.

| Project | Declaration (Unconditional/ unless noted) | Exact content, constants |
|---|---|---|
| ankeny-grh | `bach_unconditional : BachSubgroupBound (21/5)` | every proper `H ≤ (ZMod q)ˣ`, any `q` (`NeZero`), omits a **unit** `a` with `a.val ≤ c log² q` |
| lls-grh | `LLS.bach2_of_GRH : Ankeny.BachSubgroupBound 2`; `leastNonresidue2_of_GRH : LeastNonresidueBound 2`; `miller2_of_GRH : MillerStatement 2` | Bach's constant 2, all `q` |
| lls-grh | `LeastPrimeOutsideSubgroup` (q ≥ 3000, prime `ℓ ≤ (log q + B q)²`), `…Rough` (`ℓ ≤ log² q` if all `p ∣ q` have `p ≥ log² q`), `LeastNonresidueBelowLogSq` (prime `q ≥ 5`, non-residue `≤ log² q`), `LeastPrimeInCoset` (q ≥ 20000, `p ≤ 10^9` or `≤ ((h−1)log q + 3(h+1) + 5/2 (log log q)²)²`), `L1UpperBound`/`L1LowerBound` (q ≥ 10^10, `|L(1,χ)| ≤ 2e^γ(log log q − log 2 + 1/2 + 1/log log q)`), class-number bounds (main library takes `ClassNumberFormula`; NEXT_TARGETS round 6 says U for every fundamental discriminant) | LLS 2015 |
| miller-grh | `miller_unconditional : MillerStatement (21/5)`, `millerTestGRH_iff_prime_unconditional` | strong witness `a ≤ c log² n` for odd composite `n` |
| bach-sorenson-grh | `bachSorenson_two_unconditional : BachSorensonBound 2` | least prime `p ≡ a (mod q)` `< 2(q log q)²`, `q ≥ 2` |
| psi-grh | `psiChar_/psiCharLogSq_/psiAP_/thetaAP_/piAP_unconditional` | `‖ψ(x,χ) − δ_χ x‖ ≤ C√x log x log(qx)`; `|π(x;q,a) − li x/φ(q)| ≤ C√x log(qx)`; `C` existential |
| schoenfeld-rh | `schoenfeld_statement` | `|ψ−x| < √x log²x/(8π)` (x ≥ 73.2), `|θ−x| <` same (x ≥ 599), `|π(⌊x⌋) − Real.logIntegral x| < √x log x/(8π)` (x ≥ 2657) |
| cramer-rh | `cramer_cmsPrimeInterval : PrimeInClosedInterval 4 (22/25)`, `cramer_cmsPrimeGap`, `PrimeInShortInterval 2 / 3/2 / 107/100` (x ≥ 2), mean squares `∫(ψ−x)² ≪ X²` and its asymptotic | CMS 2019 constant 22/25 |
| mills-rh | `prime_strictly_between_cubes_unconditional (x : ℝ) (hx : 2^(1/3) − 1 < x) : ∃ p prime, x³ < p ∧ p < (x+1)³`; Mills' constant to 87 digits | real `x` |
| erdos-233 | `erdos_233_upper_bound` (`Σ_{n<N} d_n² = O(N log⁴ N)`), `selberg_almost_all`, `selberg_asymptotic`, **`large_gaps`**: `Σ_{n ∈ block x, d_n ≥ h} d_n ≤ C x log² x / h` for `256 log²(5x)/log 2 ≤ h ≤ 2x`, `x ≥ X₀` | Selberg 1943 |
| goldbach-average-rh | `fujii_bound`, `goldbach_average_sharp 4000` | `Σ_{n≤x} G(n) = x²/2 + O(x^{3/2})` |
| robin-rh | `robin_unconditional : RobinStatement` (`σ(n) < e^γ n log log n`, `n > 5040`), `lagarias_unconditional` | no H hypothesis left |
| nicolas-rh | `nicolas_unconditional : NicolasStatement` | `e^γ log log N_k < N_k/φ(N_k)`, every `k ≥ 1` |
| mertens-rh | `mertensSharp`, `liouvilleSharp`, `invZetaSharp` (C = 25 / region `1/2 + 8/log log t`), Riesz, Hardy–Littlewood, Redheffer, Franel–Landau | Titchmarsh 1927 |
| erdos-969 | `montgomeryVaughan_unconditional` (`E_k(x) = O(x^{1/(k+1)+ε})`), `axerKFree_unconditional` | k-free error |
| lindelof-rh | `lindelof_hypothesis`, `dirichletLindelof` | on `Re s = 1/2` only |
| littlewood-rh | `littlewood_of_RH : LittlewoodBound` (C = 4) | `|ζ(1/2+it)| ≤ exp(4 log t/log log t)` |
| density-rh | `density_hypothesis`; `N(T) ≪ T log T`, `N(T+1)−N(T) ≪ log T` (no hypothesis) | |
| speiser-rh | `speiser_of_RH` | `ζ' ≠ 0` on `0 < Re s < 1/2` |
| li-criterion-rh | `li_criterion_rhs` | `λ_n > 0` |
| abelian-erh | `abelianERH`, `cyclotomicERH` | ERH for every abelian `K/ℚ` |
| shoup-grh | `polyOmegaReal_of_GRH (21/5)`, `ankenyType` (C = 1089), `wang` (exp 6) | least primitive root |
| erdos-985, grosswald-grh, weinberger-grh, erdos-770 | prime primitive root `< p`; `g(p) < √p − 2` (p > 409); idoneal list; `h(n) ≤ max(P(n), ⌈200 log² n⌉)` | |
| hironaka-fc, artin-grh, goldbach-grh | not RH premises for this lane | |

Not in Lean anywhere in the 28: Gronwall's theorem / Mertens' third theorem (grep: no `Gronwall`
in any project; nicolas-rh has `Nicolas/Mertens.lean` with `mertens_eq` under a θ hypothesis);
`π(x) < li(x)` below 10^17; any explicit asymptotic for `li`; Phragmén–Lindelöf off the line.

## Part 2. Candidates, easiest first

Status legend: *RH-equivalent* / *RH-consequence*; all are open unconditionally unless said.

### 1. Infinitely many extremely abundant numbers · S · RH-equivalent

- **Statement.** Nazardonyavi–Yakubovich, *Extremely abundant numbers and the Riemann
  hypothesis*, J. Integer Seq. 17 (2014), Art. 14.2.8, Definition 3 and Theorem 7 (read in the
  JIS PDF): `n` is XA if `n = 10080`, or `n > 10080` and `f(n) > f(m)` for every
  `10080 ≤ m < n`, `f(n) = σ(n)/(n log log n)`. **RH ⇔ #XA = ∞.** No formal-conjectures entry.
  facebookresearch/atlas-lean has the definition only
  (`MathlibExt/NumberTheory/ExtremelyAbundantNumber.lean`, `IsExtremelyAbundantNumber`, plus a
  test file); no theorem about it.
- **Deduction (the paper's own, "Necessity" in Thm 7).** If XA were finite with largest element
  `m₀`, strong induction gives `f(n) ≤ max_{10080≤m≤m₀} f(m)` for all `n ≥ 10080`; Robin
  (`robin_unconditional`) makes that max `< e^γ`; Gronwall's `limsup f = e^γ` contradicts it.
- **Missing lemma: Gronwall's lower half, from our own Nicolas theorem.** For fixed `e`,
  `m = N_k^e` has `σ(m)/m = ∏_{p≤p_k}(1−p^{−e−1})/(1−1/p) ≥ (1 − 2^{−e}) N_k/φ(N_k)`
  (since `Σ_{n≥2} n^{−e−1} ≤ 2^{−e}`) and `log log m = log e + log log N_k`. With
  `nicolas_unconditional`, `f(m) ≥ e^γ (1−2^{−e}) L/(L + log e)`, `L = log log N_k → ∞`. So
  `limsup f ≥ e^γ` with no Mertens theorem needed. This lemma is reused by #3. My derivation,
  checked by hand, not in Lean.
- **Finite computation.** None. **Lean exists:** no (atlas-lean: definition only).
- **Effort** S (1–2 days). **Catch:** an RH-equivalent reformulation, so it adds nothing
  mathematically beyond Robin; its value is a named, published, open statement that falls out of
  two finished repos. The statement should be quoted from the paper, not from atlas-lean.

### 2. Solé–Planat: `Ψ(N_n)/(N_n log log N_n) > e^γ/ζ(2)` for every `n ≥ 3` · S · RH-equivalent

- **Statement.** Solé–Planat, *Extreme values of the Dedekind Ψ function*, arXiv:1011.1825
  (J. Comb. Number Theory 3 (2011) *(venue unverified)*), Conjecture 1 / Theorems 1–2:
  `Ψ(n) = n ∏_{p∣n}(1 + 1/p)`, `R(n) = Ψ(n)/(n log log n)`; "`R(N_n) > e^γ/ζ(2)` for `n ≥ 3`
  is equivalent to RH". Read in the arXiv HTML.
- **Deduction (their Theorem 1).** Proposition 5: `φ(N)Ψ(N)/N² = ∏_{p∣N}(1−p^{−2}) > 1/ζ(2)`.
  So `Ψ(N_n)/N_n > (N_n/φ(N_n))/ζ(2) > e^γ log log N_n / ζ(2)` by `nicolas_unconditional`.
  Index check: nicolas-rh's `kthPrimorial k = ∏_{i<k} nth Prime i` is exactly `N_k`, and it holds
  for all `k ≥ 1`, so `n ≥ 3` is covered (and `n = 2` too).
- **Missing lemmas.** `ζ(2) = π²/6` (Mathlib `riemannZeta_two`/`hasSum_zeta_two`); the strict
  inequality `∏_{p≤P}(1−p^{−2})^{−1} < π²/6` from Mathlib's smooth-number Euler product
  (`Mathlib/NumberTheory/EulerProduct`, `…smoothNumbers…`). State `Ψ` locally (Mathlib has no
  Dedekind Ψ; atlas-lean `MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean` is a
  definition only).
- **Finite computation.** None. **Effort** S (≤ 1 day). **Catch:** a two-line corollary of
  Nicolas; RH-equivalent. Not in 1337 (grep of `research/rh-transfer/` for Dedekind/Solé/Planat:
  only unrelated hits).

### 3. Caveney–Nicolas–Sondow: 4 is the only extraordinary number (and no GA2 number > 5040) · S–M · RH-equivalent

- **Statement.** Caveney–Nicolas–Sondow, *Robin's theorem, primes, and a new elementary
  reformulation of the RH*, Integers 11 (2011) A33, arXiv:1110.5078, Definition 1 and Theorem 5
  (read in arXiv v2): `G(n) = σ(n)/(n log log n)`; `N` is extraordinary if `N` is composite,
  `G(N) ≥ G(N/p)` for every prime `p ∣ N`, and `G(N) ≥ G(aN)` for every `a ≥ 1`. **RH ⇔ 4 is the
  only extraordinary number.** Companion: Nicolas–Sondow, Contemp. Math. 627 (2014), report
  "a GA2 number `N > 5040` exists iff RH is false" (CNS, *On SA, CA and GA numbers*, Ramanujan J.
  2012 *(unverified, read via the 2014 survey)*).
- **Deduction (paper §3).** Lemma 1 (Gronwall along multiples) ⇒ an extraordinary `N` has
  `G(N) ≥ e^γ`. Our version: for every `N`, `sup_a G(aN) ≥ e^γ`, using #1's lemma with
  `m = N_k^e`, `e ≥` the largest exponent in `N`, `k` past its largest prime (then `N ∣ m`).
  So `N > 5040` is impossible by `robin_unconditional`; GA2 `> 5040` falls out with no
  computation. For `N ≤ 5040` a finite check remains.
- **Finite computation (sized, Python `-I`).** `R = {3 ≤ n ≤ 5040 : G(n) ≥ e^γ}` has 26 elements
  (3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72, 84, 120, 180, 240, 360, 720,
  840, 2520, 5040). Each of its 22 composites other than 4 has an explicit `p` with
  `G(N/p) > G(N)` (e.g. 48: p = 2; 60: p = 5; 2520: p = 7). Every other composite `n ≤ 5040`
  needs a certified `G(n) < e^γ`; the closest call is `n = 420` (margin 0.0018). About 4,400
  rational interval checks with a proved-sound checker; robin-rh's Lagarias check
  (13 ≤ n ≤ 5040, 1 `native_decide`) is the template. Also `G(4) ≥ G(4a)`: CNS use Robin's
  unconditional `G(n) < e^γ + 0.6483/(log log n)²`, which we do not have in Lean; instead,
  `G(4a) < e^γ < G(4)` for `4a > 5040` by Robin, and `4a ≤ 5040` is in the finite check.
- **Effort** S–M (2–4 days). **Catch:** RH-equivalent; the theorem's interest is that it is
  stated without γ. Nothing in formal-conjectures, 1337 or GitHub (search for "extraordinary"
  Lean code: no hits).

### 4. Exceptions to Legendre, Oppermann, Andrica and Brocard: `O(log³ N)` many · S · RH-consequence

- **Statement and source.** Bazzanella, *Primes between consecutive squares*, Arch. Math. 75
  (2000) 29–34, Theorem 2 (read in the Torino post-print): under RH, all intervals
  `[n², (n+1)²] ⊂ [1, N]` except `O(f(N) log² N)` contain the expected number of primes
  (`f → ∞` arbitrarily slowly). Unconditionally, Corollary 1 gives only `O(N^{1/4+ε})`
  exceptions. The fc statements `LegendreConjecture.legendre_conjecture`,
  `Oppermann.oppermann_conjecture`, `Andrica.andrica_conjecture`,
  `BrocardConjecture.brocard_conjecture` are all research open and are **not** reachable; the
  exceptional-set versions are.
- **Deduction from `large_gaps`** (erdos-233, `Unconditional/Erdos233Unconditional.lean`).
  A Legendre failure at `n` puts the interval `(n², (n+1)²)`, of length `2n+1 ≥ 2√x`, inside one
  prime gap. Distinct `n` give disjoint intervals. So for `x = n² ∈ [X, 2X)`,
  `(#bad n)·2√X ≤ Σ_{d_k ≥ 2√X, p_k ∈ [X/2, 2X)} d_k ≪ X log² X/√X`. That gives `≪ log² X` per
  dyadic block and `O(log³ N)` for `n ≤ N`. This is one log weaker than Bazzanella. It needs
  `h = 2√X ≥ 256 log²(5X)/log 2`, true for `X ≳ 10^{11}`, and the existential `X₀` is absorbed
  by the `O`. The same argument with `h ≈ √X` gives Oppermann (both halves, length `n`) and
  Andrica (`d_n ≥ 2√p_n + 1`, one gap per failure) failing `O(log³ N)` times. For Brocard
  (fewer than 4 primes in `(p_n², p_{n+1}²)`, length `≥ 4p_n`), some prime gap of length
  `≥ p_n` lies there, and each gap serves at most two `n`.
- **Source status of the variants.** Legendre: Bazzanella (published, stronger). The Oppermann,
  Andrica and Brocard exceptional-set versions are my deduction; I found no source *(unverified
  whether published)*.
- **Finite computation.** None (statements are `O(·)`). **Effort** S (1–2 days for all four).
- **Catch:** an exceptional-set bound, not the conjectures; keep the README wording at
  "Legendre fails for at most `O(log³ N)` of the `n ≤ N`". `selberg_almost_all` alone gives
  only `o(√N)`, which is known unconditionally (Bazzanella's `N^{1/4+ε}`), so `large_gaps` is
  the input that matters.

### 5. A prime between `x^α` and `(x+1)^α` for every real `α ≥ 3` and `x ≥ 1` · S (hours) · RH-consequence

- **Statement.** Chamberland–Straub, *Weakening the Legendre conjecture*, arXiv:2602.22502
  (Feb 2026), Theorem 1.2(a): under RH, `[x^{2+δ}, (x+1)^{2+δ}]` contains a prime for all real
  `x ≥ 1` when `δ ≥ 1/4`. Unconditionally only integer `m ≥ 90` is known, for all `n ≥ 1`
  (Cully-Hugill–Johnston, Funct. Approx. 73 (2025), Thm 1.4, read on arXiv:2402.04272). The
  reported record is `m ≥ 86` (Lee, arXiv:2602.14340, as cited by a secondary page;
  *(unverified)*). So `3 ≤ m ≤ 85` is open.
- **Deduction for `α ≥ 3`.** Put `y = x^{α/3}`. Then `(x+1)^{α/3} ≥ x^{α/3} + 1` (superadditivity
  of `t ↦ t^r`, `r ≥ 1`), so `(y, y+1)` cubed sits inside `(x^α, (x+1)^α)`. Apply
  `prime_strictly_between_cubes_unconditional` (mills-rh) with `y ≥ 1 > 2^{1/3} − 1`. About
  30 lines.
- **Do not extend to `2.25 ≤ α < 3`.** Via `cramer_cmsPrimeInterval`, `α = 9/4` needs
  `0.391 log y ≤ y^{1/18}`, true only for `y ≳ 22^{18} ≈ 10^{24}`. Chamberland–Straub close
  the range below that with the Sorenson–Webster prime-gap computation, which is far beyond
  `native_decide`.
- **Effort** S. **Catch:** a trivial corollary of Caldwell–Cheng. Crowded: QRH-based groups
  (teal-sea, rStation) are posting `m = 7, 8, 9` results this month. Present it as the integer
  table `3 ≤ m ≤ 85` that is open unconditionally, not as new.

### 6. Deterministic Solovay–Strassen: every odd composite `n` has an Euler witness `≤ 2 log² n` · S · RH-consequence

- **Statement.** Bach, Math. Comp. 55 (1990) 355–380, abstract and §6 after Theorems 2–3 (read
  via the AMS abstract and K. Conrad's notes, Thm 4.1). Under ERH a composite `m` has a
  compositeness witness "in the sense of Miller or Solovay–Strassen" `≤ 2 log² m`.
  Unconditionally only power bounds are known (Burthe, Acta Arith. 80 (1997) *(bound not
  re-read)*).
- **Deduction.** The Euler liars `{a ∈ (ZMod n)ˣ : J(a/n) = a^{(n−1)/2}}` form a subgroup
  (`jacobiSym` is multiplicative). It is proper for odd composite `n` (Solovay–Strassen: if
  `p² ∣ n`, use an element of order `p`; otherwise use CRT with a non-residue mod one prime).
  Then apply `LLS.bach2_of_GRH`. The unit it returns has `val ≥ 1`. Note the direction: a strong
  liar is an Euler liar (Monier/Rabin), so `miller_unconditional` does **not** imply this; the
  subgroup argument is needed.
- **Effort** S (1–2 days; the proper-subgroup lemma is the work). **Lean exists:** none found
  (GitHub code search "Solovay Strassen language:Lean": only a complexity-class stub in
  wurtylex/ETH). **Catch:** incremental next to miller-grh; low headline value.

### 7. Bach's generator theorem: `(ℤ/m)ˣ` is generated by the units `≤ 2 log² m` · S (hours) · RH-consequence

- **Statement.** Bach 1990, Theorem 3 and §6: under ERH, `(ℤ/m)ˣ` is generated by the numbers
  `< 3 log² m` that are coprime to `m`.
- **Deduction.** The subgroup generated by the units of `val ≤ 2 log² m` is `⊤`; otherwise
  `LLS.bach2_of_GRH` gives a small unit outside it. `BachSubgroupBound` returns a **unit**, so
  we get constant 2, better than Bach's published 3 (checked: `LLS/Bach2/Main2.lean:24`
  `bach2_of_GRH` covers every `q`; `bach2_unconditional` in `Unconditional/`).
- **Effort** S. **Catch:** about ten lines; worth it only as a README corollary.

### 8. Miller's factoring lemma: given a multiple `M` of `λ(n)`, a base `a ≤ 2 log² n` splits `n` · S–M · RH-consequence

- **Statement.** Miller, JCSS 13 (1976); explicit constant from Bach 1990 *(theorem numbers not
  re-read)*. For odd `n` not a prime power, and `λ(n) ∣ M = 2^s t`, some `a ≤ 2 log² n` and
  some `i` give `1 < gcd(a^{2^i t} − 1, n) < n`. This is a deterministic polynomial-time
  reduction from factoring to computing `φ(n)` or `λ(n)`.
- **Deduction.** The bases that reveal no factor lie in a proper subgroup; this is the same
  structure as miller-grh's reduction. Then apply `bach2_of_GRH`.
- **Effort** S–M. **Catch:** whether an unconditional deterministic version exists for general
  `n` (May 2004 and Coron–May 2007 handle `N = pq`) is *(unverified)*; check before calling it
  open.

### 9. Ramanujan's prime-counting inequality `π(x)² < (ex/log x) π(x/e)` · M for the analytic range (U) · U + H for the full statement · RH-consequence

- **Statement.** Dudek–Platt, *On solving a curious inequality of Ramanujan*, Exp. Math. 24
  (2015) 289–294, arXiv:1407.1901 (read). Theorem 1.3: under RH the largest integer
  counterexample is `38,358,837,682`.
- **How the paper closed it.** Lemma 3.2: Schoenfeld plus Platt–Trudgian's `π(x) < li(x)` for
  `x ≤ 1.2·10^{17}` (a one-sided bound) gives the inequality for `x ≥ 1.15·10^{16}`. Lemma 3.4:
  a re-sieve of `[10^{10}, 1.15·10^{16}]` (about 300 CPU-hours) and a stepping argument cover
  `[10^{11}, 1.15·10^{16}]`. Galway covers `x < 10^{11}`.
- **What we can do.** My recomputation (Python `-I`, float `li` series, Schoenfeld's
  `√x log x/(8π)` used on both sides as our `SchoenfeldPi` states it):
  `g(x) = (li x + E(x))² − (ex/log x)(li(x/e) − E(x/e))` stays non-negative up to about
  `10^{17.1}` and is negative beyond. The one-sided version reproduces the paper's
  `≈ 1.1·10^{16}`. So `schoenfeld_statement` gives the inequality for `x ≥ ~2·10^{17}`
  (confirm with interval arithmetic before fixing a threshold), with no computation.
- **Open, and settled by the U part.** Unconditionally the inequality is known for
  `38,358,837,683 ≤ x ≤ e^{103}` (Johnston 2022, Ramanujan J., Thm 5.1) and for
  `x ≥ e^{3158.442}` (Axler, MIA 25 (2022), Thm 1.1). The open window `(e^{103}, e^{3158.442})`
  lies inside our analytic range. The full statement then needs `[38,358,837,683, 2·10^{17}]` as
  a cited tier-H `Prop` (Johnston / Platt–Trudgian / Axler's `≤ 10^{19}` range). That is about
  `5·10^{15}` primes, impossible for `native_decide`.
- **Catch.** Unrefereed unconditional claims exist: Subham De, arXiv:2408.02591, claims
  `x ≥ e^{43.5}`, but its step `π(x) < π(ax/e) + π((e−a)x/e)` looks unjustified to me
  *(unverified)*; J. S. Padhi, Zenodo 23440770 (Oct 2026), claims the full unconditional
  statement. Effort M: explicit `li` asymptotics and the monotonicity of `g`, in real analysis on
  `Real.logIntegral` (vendored in schoenfeld-rh). Recorded as (a)/L in
  `scoping/discovery-unwritten-rh-consequences.md`; this sizes it at M for the U part.

### 10. Weak moment bound `∫₀^T |ζ(1/2+it)|^{2k} dt ≪_{k,ε} T^{1+ε}` for every `k` · S · RH-consequence (Lindelöf-equivalent)

- Pointwise `lindelof_hypothesis` (or `littlewood_of_RH`, giving `T·exp(8k log T/log log T)`)
  integrated over `[0, T]`. formal-conjectures `Paper/RiemannZetaMoments.lean` defines
  `moment k T` but states only the asymptotics (`moment_isEquiv`, open), which this does not
  reach. It is open unconditionally for `k ≥ 3`.
- Effort S. **Catch:** trivial; the real RH results (Soundararajan `(log T)^{k²+ε}`, Harper
  `(log T)^{k²}`) are L–XL.

### 11. Piltz divisor problem `Δ_k(x) ≪ x^{1/2+ε}` for every `k` · M–L · RH-consequence

- Source: Lindelöf ⇔ `α_k ≤ 1/2` for all `k` (Titchmarsh, *Theory of the Riemann zeta-function*,
  Thm 13.4 *(theorem number unverified)*). Open unconditionally for `k ≥ 5` *(unverified; the
  known exponents are in Ivić's book)*.
- Route: mertens-rh's truncated Perron pipeline with `ζ^k` in place of `1/ζ`. It needs
  `|ζ(σ+it)| ≪ t^ε` on `σ ≥ 1/2 + δ`, which lindelof-rh does not state (it is on the line
  only). It also needs the residue of `ζ^k x^s/s` at the order-`k` pole. fc has only `k = 2`
  (`Wikipedia/DirichletDivisorProblem.lean`, exponent 1/4, not reachable).

### 12. Yıldırım: under RH, `ζ''` and `ζ'''` have no zeros in `0 ≤ Re s < 1/2` · L · RH-consequence

- Proc. AMS 124 (1996) 2311–2314, Theorem 1 and Theorem 4 (read in the Bilkent repository copy).
  Same shape as speiser-rh, but the proof uses Spira's list of zeros of `ζ'` with `|γ| < 100`
  (bound `Σ Re 1/ρ₁ < 0.185`) and a numerical sweep of `|t| ≤ 100` (`|t| ≤ 10` for `ζ'''`).
  Certified zero data for `ζ'` is the catch.

### Minor (one line each)

- **Dudek 2015:** under RH a prime in `(x − (4/π)√x log x, x]`, `x ≥ 2`. A two-line corollary of
  `cramer_cmsPrimeInterval`, but superseded by it. S, low value.
- **`log lcm(1..n) = n + O(√n log² n)`:** `ψ(n) = log lcm(1..n)` plus `SchoenfeldPsi`. S;
  RH-equivalent, but only a renaming of the ψ bound (1337's rule would not count it).
- **Effective class-number inversion:** `h(−d) ≤ H ⇒ d ≪ H² (log log H)²` from lls-grh's lower
  bound. S, unnamed, low.

## Part 3. Rejected (also in the edges file)

- **Vinogradov's `n(p) ≪ p^ε` and `g(p) ≪ p^ε`:** trivial from `leastNonresidue2_of_GRH` /
  shoup-grh, but 1337 `research/rh-transfer/vinogradov.md` covers it and its README excludes it
  as an already-published application. Do not repeat.
- **Deterministic Tonelli–Shanks / square roots mod p:** no new mathematical statement beyond
  `LeastNonresidueBound 2` (already Lean).
- **Legendre, Andrica, Oppermann, Brocard in full:** need gaps `< 2√x`; CMS gives
  `0.88√x log x`. Unreachable even under RH (already in NEXT_TARGETS' rejected list).
- **"Legendre for almost all n" (qualitative):** known unconditionally (Bazzanella's
  `N^{1/4+ε}`). Only #4's polylog form is open.
- **Primes between `x^α` and `(x+1)^α` for `2.25 ≤ α < 3`:** leaves a finite range up to
  `~10^{24}` (or Sorenson–Webster's computation). XL for Lean.
- **Ramanujan's inequality in full at tier U:** the `[3.8·10^{10}, 2·10^{17}]` range is XL. Use
  U + H (#9).
- **Least prime `p ≡ 1 (mod n)` below `n²`:** GRH gives only `(φ(n) log n)²`. Not reachable.
- **Explicit Chebotarev for abelian fields / least split prime in an abelian field:** for
  `K ⊂ ℚ(ζ_f)` the Frobenius is the class mod `f`, so `bachSorenson_two_unconditional` already
  does it. A discriminant-form statement would only be weaker.
- **Class-number lists `h(−d) = n` beyond 100 under GRH:** the finite range runs to about
  `10^{10}` discriminants with class-group computations. XL.
- **Goldbach exceptional set `E(x) ≪ x^{1/2+ε}` under GRH:** needs the circle method; Fujii's
  average does not give it. L–XL.
- **Harper / Soundararajan moment bounds under RH:** L–XL.
- **Fermat witnesses `≤ 2 log² n` for non-Carmichael composites:** true by the same subgroup
  argument, but unnamed. Fold into #6 if wanted.
- **Squarefree numbers in short intervals under RH:** the RH exponent (`2/5`) is worse than the
  unconditional `x^{1/5} log x` (Filaseta–Trifonov).

## What I searched

- All 28 `conjectures/*/README.md` headline blocks; `Unconditional/*.lean` of ankeny, robin,
  nicolas, erdos-233, cramer, mills; `Ankeny/Statement.lean`, `Miller/Statement.lean`,
  `Erdos233/{Basic,Statement,AlmostAll}.lean`.
- docs: `NEXT_TARGETS.md`, `FURTHER_PROJECTS.md`, `ATTEMPTS.md`,
  `scoping/discovery-unwritten-rh-consequences.md`.
- formal-conjectures at 9097e2f: grep for RH/GRH hypotheses (12 files, all covered); nonresidue,
  Vinogradov, extraordinary, extremely abundant, Dedekind Ψ, Ramanujan, Solovay, cubes, moments,
  superabundant/colossally, Legendre/Andrica/Brocard/Oppermann, Piltz; read
  `RiemannHypothesisEquivalents.lean`, `RiemannZetaMoments.lean`, `LegendreConjecture.lean`,
  `CramerConjecture.lean`.
- 1337 solved-conjectures `main` (`CONTENTS.md`) and `origin/research:research/rh-transfer/`
  (README inventory of 24 outcomes, and grep over all notes). None of #1–#12 is there;
  Vinogradov is.
- Atlas `data/ranked.jsonl`: regex for RH/GRH/Robin/abundant etc. Nothing relevant beyond rows
  already handled.
- GitHub code search (Lean): Solovay–Strassen, EulerLiar, extremely abundant (atlas-lean
  definition only), Dedekind psi (definitions only: atlas-lean, LeanPool), extraordinary (no
  hits), consecutive powers. The API rate limit stopped "Euler pseudoprime" and
  "Ramanujan primeCounting" before they returned.
- Web (Exa): Solé–Planat (arXiv HTML), CNS (arXiv v2), Nazardonyavi–Yakubovich (JIS PDF),
  Dudek–Platt (arXiv HTML), Axler 2022, Johnston 2022, De 2024, Padhi 2026, Bazzanella 2000 and
  2011, Chamberland–Straub 2026, Cully-Hugill 2023, Cully-Hugill–Johnston 2025, Bach 1990
  abstract, Conrad's Solovay–Strassen notes, Yıldırım 1996.

## What I could not check

- Lee's `m = 86` (seen only on a secondary page); the venue of Solé–Planat; the CNS 2012 GA2
  paper itself; Titchmarsh's theorem number for Piltz and the current unconditional `α_k`; the
  unconditional status of deterministic factoring given `φ(n)` for general `n`; and whether
  Andrica/Oppermann/Brocard exceptional-set bounds under RH are published.
