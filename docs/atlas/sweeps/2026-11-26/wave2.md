# Lane `wave2`: second discovery sweep

Date 2026-11-26. Research only: no Lean written, no other file edited. Source of statements:
formal-conjectures at `9097e2f` (local clone, Lean `v4.33.1`), read with a Python extractor
(9,036 attributed declarations; 1,102 `research open` outside `ErdosProblems`, all of whose
statements mentioning primes were read, plus keyword passes for π, ψ, primitive roots, class
numbers, residues, Möbius and Liouville over every directory). Every number below was computed
with Python `-I`. Claims not checked against a primary source are marked *(unverified)*.

The coordinator's priority change (novelty first) is applied: classes 1–3 first, then class 4,
then textbook implications as a short list.

## Summary

- **Class 1 (settle outright):** none found.
- **Class 2 (closes because RH is proved, deduction never written):** one, Sun's conjecture
  `OeisA38098.conjecture1` for every exponent `k ≥ 4`. The case `k = 3` stays open.
- **Class 3 (stronger than published):** none found.
- **Class 4 / brief "solved but `sorry`" items:** nine `research solved` statements that follow in
  a few lines from a neighbouring statement that has a `formal_proof`. Four of them already have
  an open or closed formal-conjectures PR. Then six equivalences between open statements (Lehmer,
  Carmichael, Catalan–Mersenne, perfect numbers, Alaoglu–Erdős) that nobody has written in Lean.
- Several labels in formal-conjectures look wrong. These are recorded below. The main one is
  `Brocard.brocard_conjecture.ferreira_large_n`, which is marked solved on the strength of one
  arXiv preprint.

## 1. Class 2: Sun's conjecture (A038098), exponents `k ≥ 4` · M · RH-consequence (new deduction)

**Statement.** `FormalConjectures/OEIS/38098.lean`, `OeisA38098.conjecture1`:

```lean
theorem conjecture1 (k : ℕ) (hk : 2 < k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)
```

Sun posed it on 14 October 2015 (NMBRTHRY list, "Conjecture 5 (ii)"; talk slides at Shanghai,
29 November 2015) and again on MathOverflow 301662 (2018). On MathOverflow, Sun writes "Even RH
(Riemann Hypothesis) might not be helpful to my question" (that remark was about `k = 2`). The
only progress posted there is a failed attempt with Dusart's bounds. `k` is an argument of the
theorem, so proving `∀ k ≥ 4, conjecture1 k` settles every instance except `k = 3`.

**Premise.** schoenfeld-rh `schoenfeld_statement`, the π part:
`|π(⌊x⌋) − Real.logIntegral x| < √x log x/(8π)` for `x ≥ 2657`. It is tier U, so it is a theorem
in Lean. To be safe against either convention for `Real.logIntegral` (`li` or `∫₂`), I allowed an
extra slack of 1.1 on each side.

**Deduction (mine; I found it written nowhere).** The ratio `li(x)/x` decreases by about
`1/(k n log² n)` between `x = n^k` and `y = (n+1)^k`, while the RH error in `π(x)/x` is about
`k log n /(8π n^{k/2})`. For `k ≥ 4` the gap wins once `x ≥ 2657`, except for small `n`. Results
of a scan (li by series, asymptotic expansion for `log x ≥ 60`, `k = 3..200`, every `n` up to
`10^5` and then sparser):

| k | last `n` where the RH bound does not separate | `x = (n+1)^k` there |
|---|---|---|
| 3 | 7,325,153 | 3.9·10²⁰ |
| 4 | 131 | 3.0·10⁸ |
| 5 – 200 | none (separates from the first `n` with `n^k ≥ 2657`) | – |

**Finite check (exact, done).** A sieve up to `133⁴ = 312,900,721`, with exact rationals,
verifies the inequality for `k = 4`, `2 ≤ n ≤ 132` (smallest margin `1.65/n⁴`), and for every
`k ≥ 5` and `n` with `(n+1)^k ≤ 133⁴`. That covers all `n^k < 2657`. No failure. `k = 3` also
holds for every `n ≤ 676` (same sieve), but the RH bound only separates `k = 3` from
`n ≈ 7.3·10⁶`, which needs `π(n³)` up to about `4·10²⁰`. That is out of reach.

**What a proof needs.** (a) A monotonicity and size lemma for `li(x)/x` in the form
`li(x)/x − li(y)/y ≥ …`, uniform in `k ≥ 5`. For large `k` the ratio `y/x = (1 + 1/n)^k` is huge,
so a crude bound is enough. (b) The Schoenfeld π bound from schoenfeld-rh. (c) A proved-sound
prime-counting checker up to 3.13·10⁸ at 131 points for `k = 4` plus a few dozen points for
`k ≥ 5`. That means a segmented sieve with a soundness proof, as in the erdos-985 checker.
Effort M. **Catch:** `k = 3` is the natural case and stays open, so the README must say
"proved for every `k ≥ 4`", and must not say the conjecture is proved.

**Novelty search.** Not found in: formal-conjectures PRs (`gh pr list --search 38098`: none);
1337isnot1337 code search ("38098": no relevant hit); Exa web search (only Sun's own slides, the
NMBRTHRY post, MathOverflow 301662 and a Cairn Commons listing "no claims yet"); arXiv (no hit
through Exa). The OEIS page itself returned 403 to WebFetch, so I could not read its comments.
Conjecture (ii) of the same entry (`k = 2`, `n > 15646`, and that all `π(n²)/n²` are distinct) is
**rejected**: the RH error `log n/(4πn)` exceeds the step `1/(2n log² n)` for every `n`.

## 2. Class 4: `research solved` statements, still `sorry`, short from a `formal_proof` neighbour

Each becomes `theorem X_of_Y (h : Y) : X`, where `Y` is a Lean theorem elsewhere on another
toolchain, so it enters as a hypothesis (as for openai/math in PR #5). All proofs are a few lines.
The toolchains: formal-conjectures forks are on `v4.33.1`, openai/math is on `v4.34.1` (per the
newsfeed lane), and the others were not checked. Ours is `v4.36.0`, so none of them can be
imported directly.

| Target (fc, solved, `sorry`) | From (`formal_proof`) | Argument | Novelty check (fc PRs) |
|---|---|---|---|
| `Erdos878.erdos_878.parts.iii_all` (`¬∀ x, maxUpTo f x = maxUpTo F x`) | `erdos_878.parts.iii_eventually` (ilpauzner fork of fc) | `∀ x` implies `∀ᶠ x` | none touching `iii_all` (PRs #7424, #7418 link other parts) |
| `erdos_88.variants.erdos_mckay` (`m ≤ δ log² n`) | `erdos_88` (`m ≤ δ n²`, plby/lean-proofs) | `log² n ≤ n²`, same δ | no PR for `erdos_mckay` |
| `erdos_539.variants.isBigO_sq_cube_root` (`h = O(n^{2/3})`) | `erdos_539.variants.limit` (`log h/log n → 1/2`, KitaKen1) | eventually `log h ≤ 0.6 log n` | PR #7448 (closed) attempted the `sq_is…` variants; this one is not claimed |
| `erdos_304.variants.upper_1950`, `upper_1985` (`O(log b/log log b)`, `O(√log b)`) | `upper_bound` (`O(log log b)`, openai/math) | `log log b = O(√log b)` | PRs #2874, #2480 (closed) tried; #5237 linked something else |
| `c7a_upper_bound` (`C7a < 7.1032…`) | `c7a_eq_two` (openai/math `PiExponent`) | `2 < 7.1` | none |
| `isMaxRank_three_three_five_bounds` (`6 ≤ R ≤ 7`) | `isMaxRank_three_three_five` (= 6, KitaKen1) | `IsGreatest` is unique | none |
| `erdos_205.parts.iii` | `erdos_205.variants.many_prime_factors` (plby) | `f(m) = o(log log m)` stays below `c√(log n/log log n)` | catch: `IsRepresentable` allows `m = 0` with `Ω 0 = 0`, so it holds when `f 0 > 0`; we must find a non-power-of-2 `n` in the infinite set, or handle `n = 2^j` (unverified) |
| `HadwigerNelsonAtLeastFive` | `HadwigerNelsonAtLeastSix` (openai/math) | `5 ≤ 6` | **crowded**: PRs #2769, #2738, #3260 (all closed) |
| `erdos_302.variants.upper_nine_tenths` | `upper_0_8461739827964010` (KitaKen1) | `0.846 + ε ≤ 0.9 + ε` | **taken**: PR #8275 (open) adds `formal_proof` links |
| `erdos_670.variants.uniform_in_dim` | `erdos_670.variants.ho` | take `ε = 1/(4π²)` in `ho` against `1/(2π²)` | **taken**: PR #7426 (open) |

Value: these are thin. They clean up formal-conjectures, and they settle nothing that is open.

Larger items in the same class, M or more: `Sidorenko.sidorenko_conjecture_graphon` from the
finite counterexample `sidorenko_conjecture` (openai/math). That needs `graphonHomDensity H W_G =
homDensity H G` for the step graphon (M). `agoh_giuga.variants.equivalence` (Agoh ⇔ Giuga) needs
`Σ_{k<n} k^{n−1} ≡ n·B_{n−1} (mod n)`; Mathlib has Faulhaber but I did not find von
Staudt–Clausen (M–L). `isWeakGiuga_iff_sum_primeFactors` follows from `isWeakGiuga_iff_prime_dvd`
(mo271 fork) plus squarefreeness (S–M).

## 3. Implications and equivalences between open statements (class 2 premise), not in the atlas

None of these appears in `edges.jsonl` or in the earlier lane reports. Each is S unless noted.

1. **Lehmer**: `LehmerTotient.lehmer_totient` ⇔ `¬ Erdos828.erdos_828.variants.lehmer_conjecture`
   ⇔ `OeisA51903.conjecture1`. The docstring of the last one sketches the proof: a composite `n`
   with `φ(n) ∣ n − 1` is squarefree, and `n > 4` holds automatically. No PR found (search
   `51903`: PRs #6759 and #7710 concern `conjecture2`; `lehmer_conjecture`: none).
2. **Carmichael**: `CarmichaelTotient.charmichaelTotient` ⇔ `¬ erdos_694.variants.carmichael`
   (`∃ n > 0, ∃! m, φ m = n`). It uses `φ m = 0 ↔ m = 0`. PRs on 694 (#5505, #3945) concern other
   parts.
3. **Catalan–Mersenne**: `OeisA7013.conjecture` (`∀ n`) ⇔ `Mersenne.catalans_mersenne_conjecture`
   (`∀ n ≥ 5`). The two definitions are literally the same recursion. The first direction needs
   `c₀ … c₄` prime, with `c₄ = 2¹²⁷ − 1` by Mathlib's Lucas–Lehmer machinery *(that the tactic
   reaches 127 is unverified)*. Also `catalans_mersenne_conjecture` ⇒
   `infinitely_many_mersenne_primes`, since `c_{n+1} = mersenne (c_n)` is strictly increasing.
4. **Perfect numbers**: `infinitely_many_mersenne_primes` ⇔ `infinitely_many_even_perfect`
   (Euclid–Euler is in Mathlib: `Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect` and its
   converse), and that implies `infinitely_many_perfect`. Chained with 3, Catalan–Mersenne implies
   infinitely many perfect numbers. No PR (`infinitely_many_even_perfect`: none).
5. **Alaoglu–Erdős** `ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture` ⇒
   `Mathoverflow.mathoverflow_17560` (`2^x, 3^x ∈ ℕ ⇒ x ∈ ℕ`): specialise to `p = 2`, `q = 3`.
   And `four_exponentials_conjecture` ⇒ Alaoglu–Erdős: `log p/log q` is irrational, so `x ∈ ℚ`,
   then `p^a = r^b` forces `b ∣ a`. This is a sibling of PR #3. M for the second.
6. **Linear arboricity**: `linear_arboricity_conjecture` ⇔ `…variants.regular`. Every graph
   embeds in a `Δ`-regular graph, `la` is monotone under subgraphs, and the lower bound
   `⌈(Δ+1)/2⌉` for regular graphs comes from edge counting. Folklore *(attribution unverified:
   Akiyama–Exoo–Harary 1980)*. M.
7. **Reconstruction** `reconstruction_conjecture` ⇒ `edge_reconstruction_conjecture` (Greenwell
   1971, Hemminger 1969 *(unverified)*). L: Greenwell's lemma, plus handling isolated vertices,
   which the fc statement allows.

## 4. Rejected (also in the edges file)

| Candidate | Reason (computed) |
|---|---|
| A038098 conj (ii), `k = 2` | RH error `log n/(4πn)` exceeds the step `1/(2n log²n)` for every `n` |
| A038098 conj (i), `k = 3` | RH separates only from `n ≈ 7.3·10⁶` (`x ≈ 3.9·10²⁰`); the exact range is out of reach |
| A069922 (prime in `[nⁿ, nⁿ + n²]`), A069923 (`[2ⁿ, 2ⁿ + p_n]`) | the interval is far below `(22/25)√x log x` for every `n` |
| A091591 (twin pair between squares) | twin primes, not RH |
| A034693 (`nk+1` prime, `k < n`; and `k < 1 + n^{3/4}`) | Bach–Sorenson gives `p < 2(n log n)²`, more than `n²`; already rejected in sweep 1 |
| Erdős 950 `weaker_pi` | needs intervals of length `x^θ` with `θ < ε`; RH needs `θ > 1/2`, and Brun–Titchmarsh has `log h`, not `log x` |
| Erdős 779 (Deaconescu) | reduces to a prime in `(P, P + p_{n+2}²)`, a Cramér-type gap with constant below 1; even strict Cramér falls short |
| A111291 Colton (`π(n) ≤ 2T(n)`) | the remaining range is `n ≤ 7.42·10¹³`; RH plays no part (the lower bound for `T` is elementary) |
| A113213 (`2ⁿ ± m` both prime) | a Goldbach-type statement |
| Skewes `no_crossover_below_known_region` | not decided by RH bounds; the known verification stops near 10¹⁹ |
| `Brocard.brocard_conjecture.ferreira_large_n` (fc says solved) | the label rests on Ferreira, arXiv:2307.08725 (preprint), and Wikipedia (Nov 2026) still lists Brocard as unproven. RH does not reach it: it needs 4 primes in about `4√x`. Flag the label; do not build on it |
| Meyniel ⇒ soft Meyniel | trivial, and fc PR #8307 (open) marks soft Meyniel solved |
| Union-closed ⇒ its solved weaker variants; Wall–Sun–Sun infinite ⇒ exists | trivial, no value |

## What I searched

formal-conjectures `9097e2f`: all 1,102 open declarations outside Erdős by keyword, and every
statement mentioning primes read in full (326). Every `research solved` + `sorry` declaration
whose docstring or statement names a declaration with a `formal_proof` (119; 46 pairs read).
Wikipedia graph, combinatorics and analysis files; Kourovka, Mathoverflow, Other, Millennium,
Hilbert. `edges.jsonl` (305 edges) and the lane reports, to avoid repeats. `gh pr list -R
google-deepmind/formal-conjectures --state all --search` for 19 names (results in the tables).
Exa web search for Sun's A038098 conjecture and for Ferreira's Brocard claim. 1337isnot1337 code
search for "38098".

## What I could not check

The OEIS A038098 page (HTTP 403). The toolchains of the KitaKen1 and plby `formal_proof` repos.
Whether Mathlib's Lucas–Lehmer tactic proves `2¹²⁷ − 1` prime at our pin. Greenwell's exact
hypotheses. Whether `Real.logIntegral` in schoenfeld-rh is `li` or `∫₂`; the 1.1 slack covers
both. No search for an existing Lean `li(x)/x` monotonicity lemma beyond our own repos. LivingBrain
was not queried in this lane. `/tmp` ran out of inodes during the run, so the scratch scripts
were partly run from stdin.
