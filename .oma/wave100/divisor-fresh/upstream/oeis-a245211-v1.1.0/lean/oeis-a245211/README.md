# Divisor-Count Moments of Proper Divisors (OEIS A245211)

Lean 4 formalization of Jaroslav Krizek's proper-divisor first-moment sequence `a(n) = sum_{d | n, d < n} d * tau(d)` ([OEIS A245211](https://oeis.org/A245211)), its companion sequences [OEIS A038040](https://oeis.org/A038040) (`n * tau(n)`), [OEIS A060640](https://oeis.org/A060640) (`S(n) = sum_{d | n} d * tau(d)`), [OEIS A245212](https://oeis.org/A245212) (`n * tau(n) - a(n)`), [OEIS A245213](https://oeis.org/A245213) (`n` with `A245212(n) < n`), and [OEIS A245214](https://oeis.org/A245214) (`n` with `n * tau(n) < a(n)`), and Krizek's fixed-point problem (`a(n) = n`).

## Toolchain and Layout

The project uses Lean `4.35.0` (`lean-toolchain`: `leanprover/lean4:v4.35.0`) with zero external Lean or Mathlib dependencies.

| Path | Contents |
|---|---|
| `lean/oeis-a245211/OeisA245211.lean` | Root library importing all eight Lean modules |
| `lean/oeis-a245211/OeisA245211/Basic.lean` | Balanced binary-tree range sum `sumUpTo`, `tau`, `sigma`, `nTau`, `fullMoment`, `a`, `cantileverDiff`, `IsFixedPoint`, `IsInA245213`, `IsInA245214`, duplicate-free divisor lists `divisors` and `properDivisors`, OEIS identities, refutations (`0, 1, 2, 3, 4, 6, 9, 15, 25, 33, 71, 72`), and certified witness `isFixedPoint_21` (`a(21) = 21`) |
| `lean/oeis-a245211/OeisA245211/Dominance.lean` | Point-sampling lower bounds for `sumUpTo`, divisor-count bounds `tau(m) >= 2` and `tau(m) >= 3` (composite `m`), the Fundamental Dominance Theorem `gt_self_of_dvd_le_tau`, unconditional exclusion of all even positive integers (`ne_self_of_even`, `odd_of_isFixedPoint`), and composite-cofactor exclusion for `3 * m` |
| `lean/oeis-a245211/OeisA245211/Families.lean` | Arithmetic primality `IsPrime p` and decidable characterization `IsPrime p <-> 2 <= p /\ tau p = 2`, Krizek's prime formula `a(p) = 1`, prime-power congruence `a(p^k) % p = 1` and exclusion `ne_self_of_prime_pow`, semiprime formula `a(p * q) = 1 + 2p + 2q`, Krizek's even semiprime formula `a(2p) = 2p + 5`, unconditional uniqueness of `n = 21` among all semiprimes (`semiprime_fixedPoint_iff`) and all multiples of `3` (`three_dvd_fixedPoint_iff_eq_21`), and three-prime-factor (`Omega(n) = 3`) identities and exclusions |
| `lean/oeis-a245211/OeisA245211/Parity.lean` | Multiplicativity of `tau` and `fullMoment` on coprime arguments, exact prime-power recurrence and parity congruence `fullMoment (p^e) % 2 = ((e + 1) * (e + 2) / 2) % 2`, the General Parity Obstruction Theorem (`exact_exponent_mod_four_of_isFixedPoint`), and the sharpened prime-power dominance bound `e * tau m < p` (`sharpened_dominance_bound`) |
| `lean/oeis-a245211/OeisA245211/OmegaFour.lean` | Prime-factor multiplicity function `omegaBig` ($\Omega(n)$), unconditional exclusion of `p^3 q`, `p^2 q r`, `p^2 q^2`, and squarefree `p q r s`, complete classification `fixedPoint_eq_21_of_omegaBig_le_four` (`omegaBig n <= 4 -> IsFixedPoint n -> n = 21`), and non-squarefree $\Omega(n) = 5$ reduction (`omegaFive_must_be_squarefree_ge_17`) |
| `lean/oeis-a245211/OeisA245211/OmegaFive.lean` | Growth bound `five_prime_growth_bound` (`73 <= p`), Cunningham prime-factor forced closure (`prime_dvd_33pqrst_impossible`, `prime_dvd_33pqrst_mem`, `five_prime_moment_ne`, `not_isFixedPoint_five_distinct_primes`), `not_isFixedPoint_of_omegaBig_eq_five`, complete classification `fixedPoint_eq_21_of_omegaBig_le_five`, and structural reduction `omegaBig_ge_six_of_isFixedPoint_ne_21` (`6 <= omegaBig n`) |
| `lean/oeis-a245211/OeisA245211/OmegaSix.lean` | Non-squarefree $\Omega(n) = 6$ exclusions (`p^5 q`, `p^4 q^2`, `p^2 q^2 r^2`, `p^4 q r`, and parity-obstructed shapes), `omegaSix_must_be_squarefree_ge_37` (`37 <= p`), growth bound `six_prime_growth_bound` (`181 <= p`), Cunningham prime-factor forced closure (`prime_dvd_65pqrstu_impossible`, `prime_dvd_65pqrstu_mem`, `six_prime_moment_ne`, `not_isFixedPoint_six_distinct_primes`), `not_isFixedPoint_of_omegaBig_eq_six`, complete classification `fixedPoint_eq_21_of_omegaBig_le_six`, and structural reduction `omegaBig_ge_seven_of_isFixedPoint_ne_21` (`7 <= omegaBig n`) |
| `lean/oeis-a245211/OeisA245211/TableCerts.lean` | Certified evaluation of all 66 OEIS table entries (`map_a_range_66`), companion sequence minimum milestones `not_isInA245213_below_72` (`min(A245213) = 72`) and `not_isInA245214_below_144` (`min(A245214) = 144`), bounded uniqueness `fixedPoint_iff_eq_21_upto_150` (`1 <= n <= 150`), and the closest odd composite near-miss `a_725_eq` (`a(725) = 724`) |
| `lean/oeis-a245211/LICENSE` | Apache License 2.0 covering the Lean 4 formalization and accompanying verification code |
| `lean/oeis-a245211/NOTICE` | Attribution notice file required for redistribution under Apache License 2.0 |
| `lean/oeis-a245211/CITATION.cff` | Citation File Format metadata for the OEIS A245211 formalization |
| `lean/oeis-a245211/.zenodo.json` | Zenodo archive deposit metadata for the OEIS A245211 release |
| `solver/a245211_search.py` | Independent Python sieve verifier (`b245211.txt`, `N = 1,000,000`), near-miss analyzer, parity obstruction check, `Omega(n) <= 5` Diophantine + hyperbolic search, and Cunningham prime-factor forced-closure accelerator (`k = 3..10`) with non-squarefree `Omega(n) = 6` exclusions |
| `docs/oeis-a245211/oeis-a245211.tex` | AMS `amsart` LaTeX source for the mathematics release paper |
| `docs/oeis-a245211/oeis-a245211.pdf` | Compiled PDF mathematics release paper |
| `docs/oeis-a245211/index.html` | Standalone HTML edition of the mathematics release paper with print, warm, and night display modes |
| `docs/oeis-a245211/package_zenodo.sh` | Packaging script building the self-contained `oeis-a245211-v1.1.0.zip` release archive |

## Formalized Definitions and Theorems

In [Basic.lean](OeisA245211/Basic.lean), `a n` sums `d * tau d` over all positive proper divisors `1 <= d < n` of `n`:

- `fullMoment_eq_a_add_nTau` / `a_eq_fullMoment_sub_nTau`: proves Krizek's OEIS identity `A060640(n) = A245211(n) + A038040(n)` for `0 < n`.
- `a_int_eq_nTau_sub_cantileverDiff`: proves `(a n : Int) = (nTau n : Int) - cantileverDiff n` (`A245211(n) = A038040(n) - A245212(n)`).
- `isFixedPoint_iff_fullMoment`: proves `IsFixedPoint n <-> 0 < n /\ fullMoment n = n * (tau n + 1)`.
- `a_eq_sumList_properDivisors`, `fullMoment_eq_sumList_divisors`, `tau_eq_length_divisors`: proves equivalence between `sumUpTo`-based definitions and sums/lengths over the duplicate-free divisor lists `properDivisors n` and `divisors n`.
- `not_isFixedPoint_0`, `not_isFixedPoint_1`, `not_isFixedPoint_2`, `not_isFixedPoint_3`, `not_isFixedPoint_4`, `not_isFixedPoint_6`, `not_isFixedPoint_9`, `not_isFixedPoint_15`, `not_isFixedPoint_25`, `not_isFixedPoint_33`, `not_isInA245213_71`, `isInA245213_72`, `not_isInA245214_72`, and `isFixedPoint_21`: explicit refutation and witness certificates.

In [Dominance.lean](OeisA245211/Dominance.lean), point-sampling lower bounds yield unconditional infinite-family exclusions:

- `gt_self_of_dvd_le_tau` (**Fundamental Dominance Theorem**): if `n = k * m` with `1 < k`, `1 < m`, and `k <= tau m`, then `n + 1 <= a n` (from the two proper divisors `1` and `m` alone).
- `a_gt_self_of_even_gt_two`, `ne_self_of_even`, `not_isFixedPoint_of_even`, `odd_of_isFixedPoint`: every even integer `n > 2` satisfies `n + 1 <= a n`, and combined with `a(2) = 1`, no even integer `n >= 1` is a fixed point. Every fixed point is odd.
- `a_three_mul_ge_of_proper_divisor`, `not_isFixedPoint_three_mul_of_proper_divisor`: if `m` has a proper divisor `1 < d < m`, then `tau m >= 3` and `3 * m + 1 <= a (3 * m)`.

In [Families.lean](OeisA245211/Families.lean), closed-form divisor evaluations and modular congruences classify primes, prime powers, semiprimes, multiples of `3`, and three-prime-factor numbers:

- `tau_of_isPrime`, `isPrime_iff_tau_eq_two`, `a_of_isPrime`, `not_isFixedPoint_of_isPrime`: for every prime `p`, `tau p = 2` and `a p = 1 < p` (Krizek's first 2014 OEIS formula), and `IsPrime p <-> 2 <= p /\ tau p = 2`.
- `a_prime_pow_mod_p`, `ne_self_of_prime_pow`, `not_isFixedPoint_prime_pow`: for every prime `p` and exponent `k >= 1`, `a(p^k) % p = 1` while `p^k % p = 0`, so no prime power is a fixed point.
- `a_semiprime`, `a_two_mul_odd_prime`, `a_three_mul_prime`: for primes `p < q`, `a(p * q) = 1 + 2 * p + 2 * q`; in particular, `a(2 * p) = 2 * p + 5` for every odd prime `p > 2` (Krizek's second 2014 OEIS formula) and `a(3 * p) = 2 * p + 7` for `p > 3`.
- `semiprime_fixedPoint_iff`: among all semiprimes `p * q` (`p <= q` primes), `IsFixedPoint (p * q) <-> p = 3 /\ q = 7`.
- `three_dvd_fixedPoint_iff_eq_21`: among all multiples of `3`, `IsFixedPoint n <-> n = 21`.
- `p2q_near_miss_identity`, `odd_p2q_formula_ne_self`, `three_prime_moment_ne`: proves the polynomial identity `(p^2 - 4p - 2)(q - 3) + (1 + 2p + 3p^2 + 2q + 4pq) = p^2 q + 7(2p + 1)` governing `n = p^2 q`, parity exclusion for odd `p^2 q`, and Diophantine exclusion `(2p + 1)(2q + 1)(2r + 1) != 9 p q r` for all primes `p < q < r`.

In [Parity.lean](OeisA245211/Parity.lean), multiplicativity of `tau` and `fullMoment` yields a general parity obstruction and a sharpened prime-power dominance bound:

- `tau_mul_of_coprime`, `fullMoment_mul_of_coprime`: multiplicativity of `tau` and `fullMoment` on coprime arguments.
- `tau_prime_pow`, `fullMoment_prime_pow_succ`, `fullMoment_prime_pow_mod_two`, `fullMoment_prime_pow_odd_iff`: exact prime-power formulas and odd prime-power parity congruence `fullMoment (p^e) % 2 = ((e + 1) * (e + 2) / 2) % 2`, so `fullMoment (p^e)` is odd iff `e % 4 = 0 \/ e % 4 = 1`.
- `exact_exponent_mod_four_of_isFixedPoint`, `not_isFixedPoint_of_exact_exponent_mod_four_ge_two` (**General Parity Obstruction Theorem**): for every non-square fixed point `n` (`tau n % 2 = 0`), every exact prime-power exponent `e` satisfies `e % 4 = 0 \/ e % 4 = 1`.
- `sharpened_dominance_bound`, `exact_prime_pow_tau_lt_prime`: if `n = p^e * m` with `gcd(p^e, m) = 1`, `1 <= e`, and `1 < m`, then `IsFixedPoint n -> e * tau m < p`.

In [OmegaFour.lean](OeisA245211/OmegaFour.lean), prime-factor multiplicity `omegaBig` ($\Omega(n)$) closes all $\Omega(n) \le 4$ cases and reduces $\Omega(n) = 5$:

- `not_isFixedPoint_prime_cube_mul_prime`, `not_isFixedPoint_prime_sq_mul_two_primes`: unconditional exclusion of `p^3 * q` and `p^2 * q * r` via the General Parity Obstruction Theorem.
- `p2q2_diophantine_ne`, `not_isFixedPoint_prime_sq_mul_prime_sq`: unconditional exclusion of `p^2 * q^2` via `p2q2_growth_bound` (`13 <= p`, `17 <= q`) and modulo-5 obstruction.
- `four_prime_growth_bound`, `four_prime_moment_ne`, `not_isFixedPoint_four_distinct_primes`: unconditional exclusion of squarefree `p * q * r * s` (`5 <= p < q < r < s`).
- `fixedPoint_eq_21_of_omegaBig_le_four`, `omegaBig_ge_five_of_isFixedPoint_ne_21`: every fixed point with `omegaBig n <= 4` equals `21`, so any fixed point `n != 21` satisfies `Nat.gcd n 6 = 1` and `5 <= omegaBig n`.
- `not_isFixedPoint_prime_four_mul_prime`, `omegaFive_must_be_squarefree_ge_17`: unconditional exclusion of all non-squarefree `Omega(n) = 5` families (`p^5`, `p^4 q`, `p^3 q^2`, `p^3 q r`, `p^2 q^2 r`, `p^2 q r s`) and lower bound `17 <= p` on the smallest prime factor of any squarefree 5-prime fixed point.

In [OmegaFive.lean](OeisA245211/OmegaFive.lean), Cunningham prime-factor forced closure closes the remaining squarefree $\Omega(n) = 5$ branch unconditionally:

- `five_prime_growth_bound`: for primes `73 <= p < q < r < s < t`, `(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) < 33 * p * q * r * s * t`.
- `prime_dvd_33pqrst_impossible`, `prime_dvd_33pqrst_mem`, `five_prime_moment_ne`, `not_isFixedPoint_five_distinct_primes`: eliminates all 14 primes `17 <= p < 73` by forcing prime factors of `2 * p + 1` outside `{3, 11}` into `{q, r, s, t}` until a factor below `p` collides with `gcd`.
- `not_isFixedPoint_of_omegaBig_eq_five`, `fixedPoint_eq_21_of_omegaBig_le_five`, `omegaBig_ge_six_of_isFixedPoint_ne_21`: every fixed point with `omegaBig n <= 5` equals `21`, so any fixed point `n != 21` satisfies `Nat.gcd n 6 = 1` and `6 <= omegaBig n`.

In [OmegaSix.lean](OeisA245211/OmegaSix.lean), all non-squarefree and squarefree $\Omega(n) = 6$ branches are closed unconditionally:

- `fullMoment_prime_pow_five`, `p5q_growth_bound`, `not_isFixedPoint_prime_five_mul_prime`: unconditional exclusion of `p^5 * q` via growth bound (`79 <= p`) and 17 modular checks (`11 <= p <= 73`).
- `not_isFixedPoint_prime_four_mul_prime_sq`, `not_isFixedPoint_three_prime_sq`: unconditional exclusion of `p^4 * q^2` modulo `4` and `p^2 * q^2 * r^2` modulo `8`.
- `p4qr_growth_bound`, `not_isFixedPoint_prime_four_mul_two_primes`: unconditional exclusion of `p^4 * q * r` via growth bound (`53 <= p`, `29 <= q`), small-factor forcing, and `decide` checks.
- `omegaSix_must_be_squarefree_ge_37`: excludes all non-squarefree `Omega(n) = 6` shapes (including parity-obstructed `(3, 3)`, `(3, 2, 1)`, `(3, 1, 1, 1)`, `(2, 2, 1, 1)`, and `(2, 1, 1, 1, 1)`) and establishes `37 <= p` on the smallest prime factor of any squarefree 6-prime fixed point.
- `six_prime_growth_bound`, `prime_dvd_65pqrstu_impossible`, `prime_dvd_65pqrstu_mem`, `six_prime_moment_ne`, `not_isFixedPoint_six_distinct_primes`: closes squarefree `p * q * r * s * t * u` via growth bound (`181 <= p`) and Cunningham prime-factor forced closure across all 30 primes `37 <= p < 181`.
- `not_isFixedPoint_of_omegaBig_eq_six`, `fixedPoint_eq_21_of_omegaBig_le_six`, `omegaBig_ge_seven_of_isFixedPoint_ne_21`: every fixed point with `omegaBig n <= 6` equals `21`, so any fixed point `n != 21` satisfies `7 <= omegaBig n`.

In [TableCerts.lean](OeisA245211/TableCerts.lean), balanced binary-tree kernel reduction certifies:

- `map_a_range_66` and `a_1_eq`..`a_25_eq`, `a_66_eq`: all 66 terms in the `%S`, `%T`, `%U` lines of `OEIS A245211` (subsuming all five `decide` theorems `a 1`..`a 5` in `google-deepmind/formal-conjectures:FormalConjectures/OEIS/245211.lean`).
- `not_isInA245213_below_72` and `isInA245213_72`: `n = 72` (`a(72) = 802`, `72 * tau(72) = 864`) is the minimum positive integer in `OEIS A245213`.
- `not_isInA245214_below_144` and `isInA245214_144`: `n = 144` (`a(144) = 2226`, `144 * tau(144) = 2160`) is the minimum positive integer in `OEIS A245214` (`n * tau(n) < a(n)`), certifying Krizek's 2014 OEIS remark.
- `fixedPoint_iff_eq_21_upto_150`: for `1 <= n <= 150`, `IsFixedPoint n <-> n = 21`.
- `a_725_eq`, `not_isFixedPoint_725`: `a(725) = 724` at `n = 725 = 5^2 * 29`, the closest odd composite near-miss below `1,000,000`.

## Remaining Open Problem

Whether `n = 21` is the unique positive integer satisfying `a(n) = n` across all `n >= 1` remains open in full generality. Our unconditional Lean 4 theorems reduce any hypothetical second solution `n != 21` to an odd integer coprime to `6` with `Omega(n) >= 7` prime factors counted with multiplicity (`e * tau(m) < p` for every exact prime power `p^e || n` and `e % 4 in {0, 1}` whenever `n` is non-square). External computation in `solver/a245211_search.py` further verifies `a(n) != n` up to `n = 1,000,000`, accelerates squarefree $\Omega(n) = k$ searches via Cunningham prime-factor forced closure (reducing $\Omega(n) = 5$ from `43,849` hyperbolic triples to `14` candidate primes with `0` surviving roots, and $\Omega(n) = 6$ to `30` candidate primes with `0` surviving roots), and verifies all non-squarefree $\Omega(n) = 6$ exclusions (`(6)`, `(5,1)`, `(4,2)`, `(2,2,2)`, `(4,1,1)`, and parity-obstructed shapes).

## Freshness Checks

Live network checks ran on `2026-11-14`, `2026-11-18`, and `2026-11-19`:

- `https://oeis.org/A245211/internal` (`curl -A "Mozilla/5.0"`): HTTP 200, authored by Jaroslav Krizek (`Jul 23 2014`), listing 66 initial terms (`n = 1..66`), Krizek's formulas `a(p) = 1` and `a(2p) = 2p + 5`, the sign-change threshold `n = 144`, and the fixed-point remark at `n = 21`.
- `https://oeis.org/A245211/b245211.txt`: HTTP 200 (`10001` lines, `sha256:006cd9a3012d809ae12ef9cd29227e5a98c836519922702a0a0957044c5bca74`), Jens Kruse Andersen's table for `n = 1..10000`.
- Companion OEIS sequences `A000005`, `A000203`, `A001222`, `A038040`, `A060640`, `A245212`, `A245213`, and `A245214` (`curl -A "Mozilla/5.0"`): HTTP 200.
- `google-deepmind/formal-conjectures:FormalConjectures/OEIS/245211.lean` (rechecked `2026-11-18`): `0` PRs mentioning `245211`, `0` hits on Palomar and ProofXiv; `theorem conjecture (n : N) (hn : 0 < n) : a n = n <-> n = 21 := by sorry` remains tagged `research open`.

## Verification

- We ran `lake clean && lake build` in `lean/oeis-a245211/` and it completed with exit code 0 (`Build completed successfully (11 jobs)`) and zero warnings.
- We ran `grep --include="*.lean"` across `lean/` for `sorry`, `axiom `, `native_decide`, `ofReduceBool`, `trustCompiler`, `unsafe`, and `set_option` and found zero matches (`grep` exit code 1).
- We inspected `#print axioms` via `lake env lean --stdin` on every exported theorem in `OeisA245211` (`Basic`, `Dominance`, `Families`, `Parity`, `OmegaFour`, `OmegaFive`, `OmegaSix`, `TableCerts`); every theorem depends only on standard Lean axioms (`[propext]`, `[Quot.sound]`, `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]`, or empty `[]`).
- We ran `python3 solver/a245211_search.py --limit 200000` and verified all 66 OEIS header terms, uniqueness of `n = 21` up to `N = 200,000` (previously tested to `1,000,000`), the general parity congruence, the `Omega(n) <= 4` Diophantine census, the non-squarefree `Omega(n) = 5` exclusions, the exhaustive squarefree `Omega(n) = 5` hyperbolic search (`43,849` triples, `0` solutions), the Cunningham forced-closure acceleration for `k = 3..10` (`14` candidate primes for `Omega(n) = 5` and `30` for `Omega(n) = 6`, both `0` surviving roots), and all non-squarefree `Omega(n) = 6` exclusions.

## Attribution and Provenance

Mar Allen P. Sugui ([mariyaholic.github.io](https://mariyaholic.github.io/) · [github.com/mariyaholic](https://github.com/mariyaholic)) developed this formalization with Gemini 4 Argon and Gemini 4 Hydrogen for Lean 4.35.0 proof engineering and Diophantine analysis. The companion paper is available as [docs/oeis-a245211/oeis-a245211.pdf](../../docs/oeis-a245211/oeis-a245211.pdf), with LaTeX source at [oeis-a245211.tex](../../docs/oeis-a245211/oeis-a245211.tex) and an HTML edition at [index.html](../../docs/oeis-a245211/index.html).
