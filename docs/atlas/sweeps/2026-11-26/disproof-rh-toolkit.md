# Lane `disproof-rh-toolkit`: explicit counterexamples where RH-strength theorems shrink the search

Lane `disproof-rh-toolkit`, 2026-11-26. Research and computation only. No Lean file and no existing
file was edited. Scripts, outputs and downloaded data are in the session scratchpad
`hunt-rh/` (`src/`, `out/`, `data/`). Every downloaded file sits in its own directory under `data/`
and was read only by `python3 -I` or by `pdftotext`. Claims I could not confirm from a primary
source are marked *(unverified)*. Lean declaration names are copied from `AGENTS.md`,
`toolkit-reuse.md` Part 1 and `docs/rh-lemmas/03-automorphic-arithmetic.md`. None was re-checked
against the Lean source in this lane.

## Main finding

**Hit (route a, with numerical witnesses from route e).** Hassani's 2021 paper asks two questions
that this lane answers *no*. M. Hassani, *Remarks on Ramanujan's inequality concerning the prime
counting function*, Commun. Math. 29 (2021) 473–482, DOI 10.2478/cm-2021-0014, §4 item 1, asks
"about the validity of the following inequalities for x sufficiently large":

```
ψ(x)² < e·x·ψ(x/e)      and      θ(x)² < e·x·θ(x/e)        (Hassani 2021, (10))
```

Both fail for arbitrarily large `x`:

- **ψ, unconditionally, by Landau's oscillation theorem.** No zero data is needed. The only
  inputs are that ζ has no real zeros in `(0, 1)` and has at least one zero `ρ` with
  `e^{1−ρ} ≠ 2`. Numerically, the inequality fails at about half of all primes up to `10^11`
  (2,092,895,980 failures among 4,118,054,813 primes plus prime powers). The largest failure
  found is `x = 99,555,795,379`.
- **θ, unconditionally, by a case split.** If RH were false, Landau applies as for ψ. Under RH,
  which is a Lean theorem here, Ingham's Fejér-kernel method with the first 10 zeros gives
  `limsup (2E_θ(x) − eE_θ(x/e))/√x ≥ 0.588 − 0.351 > 0`. The inequality fails at 1,116,026,207
  primes up to `10^11`. The largest failure found is `x = 96,422,442,679`.

The reason is structural. Ramanujan's π-inequality holds eventually because the two sides differ
at the `x²/log⁴x` term of the asymptotic expansion, and that term beats the error. For ψ and θ the
main terms cancel exactly, so the sign is decided by the explicit formula alone. In the ψ case the
zero sum has mean zero. In the θ case the bias is only `−(2 − √e)√x = −0.3513√x`, and the low
zeros overcome it.

Prior-art search (details in §1.5): Hassani's six citing papers (Semantic Scholar), arXiv and web
search, a GitHub code search, 1337isnot1337/solved-conjectures, openai/math and
formal-conjectures. Nobody answered the question in anything I could find. Per AGENTS.md
("Priority" and "Literature status"), the label *new* needs the owner's sign-off. So: **no
published answer found in the places listed**, and the question is a 2021 "we may ask", not a
named conjecture.

**Smaller items.**

- Hassani's *n-th prime analogue* in the same section, `p_n² < e·n·log n·p_{⌊n/e⌋}`, is false
  for **every** `n ≥ 3`. This is elementary (§2) and almost certainly a slip in the question.
- Hassani's *progression analogue* holds for x sufficiently large for every fixed `(q, a)`. That
  is a proof, not a disproof (§3), and the last counterexamples for `q = 3, 4` lie above `10^11`.
- The Mossinghoff–Trudgian conjecture `L_{1/2}(x) ≤ 0` for `x ≥ 17` cannot be refuted in any
  computable range. §4 bounds the zero sum quantitatively.

No other chain produced a witness.

## Searches run (range, cost, outcome)

All CPU times are single-core on the shared box (load average about 185 on 95 cores during the
runs). The total for the lane is about 1.2 CPU-hours, well under the 20-hour budget and under the
2-hour default per candidate.

| # | Search | Code | Range | CPU | Outcome |
|---|---|---|---|---|---|
| 1 | Ramanujan-type scan, all six inequalities at every prime (and every prime power for ψ) | `src/ramtype.c` | `x ≤ 10^11` | 30 min | see §1–3; calibration reproduces π(10^11) = 4,118,054,813, θ(10^8), ψ(10^8), and Dudek–Platt's last Ramanujan counterexample (last failing prime 38,358,837,677, so the failing interval ends at the integer 38,358,837,682) |
| 2 | Independent single-witness check, `__float128` + Kahan, a separate plain sieve | `src/verify_q.c` | witnesses at 997, 1627, 999983, 9,997,472,873, 10,000,000,019 (and 96,422,442,679, 99,555,795,379, see §1.4) | 3 min (+15 min) | agrees with run 1 at every point |
| 3 | Interval arithmetic (`mpmath.iv`, outward rounding, 40 digits) | `src/verify_iv.py` | 997, 1627, 935537, 945823, 999983, 99,901,159, 99,999,989 | 6 min | every failure certified, intervals bounded away from 0 |
| 4 | Ingham lower bound for the θ question | `src/ingham_theta.py` | zeros below `T = 30, 50, 100`; `t = log x ≤ 3000`, step 0.005 | 2 min | `T = 50` (10 zeros): sup 0.5885 at t = 2750.54 against the target 0.3513; `T = 100` (29 zeros): 1.0501 at t = 660.41 |
| 5 | n-th prime analogue, interval arithmetic | `src/nth_prime.py` | `n < 10^5` (and `n ≤ 4.1·10^9` in run 1) | 1 min | fails at every `n ≥ 3`; the second form holds only at `n = 1` |
| 6 | `L_{1/2}` explicit-formula coefficients | `src/lhalf_zeros.py` | first 5000 zeros (Odlyzko `zeros1`) | 6 min | `2Σ|c_γ|` = 2.153 (1000 zeros), 2.866 (5000) |
| 7 | `L_{1/2}(x)` direct, to validate run 6 | `src/lhalf_direct.c`, `src/lhalf_eval.py` | `x ≤ 10^8` (a range already exhausted by M–T to `10^12`, used only as a code check) | 10 s | formula matches the direct sum to about 0.02 at `10^3 … 10^8` |

Zero data: A. Odlyzko's table `zeros1`, the first 100,000 zeros to 9 decimals, from
`https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1`, in `data/odlyzko/`. It was used only
to locate and size things. Every witness above was verified by direct prime sums (runs 2 and 3),
never by zeros.

## 1. Hassani's Chebyshev-function questions (HIT)

### 1.1 Exact wording and source

Hassani 2021, §4, read in the journal PDF (`data/hassani/h.pdf`, `pdftotext`): "Finally, we
propose the question of studying inequalities of Ramanujan type concerning other functions of
prime numbers. 1. Ramanujan's inequality concerning the Chebyshev functions. Since ψ(x) ∼ x and
θ(x) ∼ x as x → ∞, we may ask about the validity of the following inequalities for x sufficiently
large: ψ(x)² < e x ψ(x/e), and θ(x)² < e x θ(x/e). (10)". The paper gives no numerical range for
(10).

### 1.2 Reduction chain

- **Raw space.** All real `x` (an "eventually" statement). No finite witness refutes it, so the
  disproof has to be an Ω-theorem, with witnesses as evidence.
- **Step 1, the main terms cancel.** Write `E(x) = ψ(x) − x`. Then
  `ψ(x)² − e x ψ(x/e) = x·F(x) + E(x)²` with `F(x) = 2E(x) − e·E(x/e)`. Since `E² ≥ 0`, the
  inequality fails wherever `F(x) > 0`. For θ, `E_θ = θ − x = E − (ψ − θ)` and
  `ψ − θ = √x + O(x^{1/3})`, so `F_θ(x) = F(x) − (2 − √e)√x + O(x^{1/3})`, and the θ inequality
  fails wherever `F_θ(x) > 0`.
- **Step 2, the constancy intervals reduce the check to primes.** On an interval with no prime
  power, the left side is constant and the right side increases (`x·ψ(x/e)` is increasing). So
  the maximum of LHS − RHS on each interval sits at its left end. The thin family to test is the
  primes (and the prime powers for ψ), about `π(x)` points instead of a continuum. Run 1 checks
  every one up to `10^11`.
- **Step 3, ψ: Landau.** Suppose `F(x) ≤ 0` for `x ≥ X`. Its Mellin transform is
  `∫₁^∞ F(x)x^{−s−1}dx = (2 − e^{1−s})·M(s) + (entire)`, where
  `M(s) = −ζ'(s)/(sζ(s)) − 1/(s−1)`. The entire part comes from `E(u) = −u` on `[1/e, 1)`.
  `M` is analytic on the real half-line `s > 0`: ζ has no zeros in `(0, 1)`, and at `s = 1` the
  pole of `−ζ'/(sζ)` cancels against `1/(s−1)`. Landau's theorem puts the abscissa of convergence
  at a real singularity, so it is `≤ 0` and the transform is analytic on `Re s > 0`. But
  `M` has a simple pole at `ρ₁ = 1/2 + 14.1347…i` with residue `−1/ρ₁ ≠ 0`, and
  `|e^{1−ρ₁}| = e^{1/2} = 1.6487 ≠ 2`. Contradiction. So `F(x) > 0`, and the ψ inequality fails,
  for arbitrarily large `x`. Applying the same argument to `F(x) − x^{1/2−δ}` gives
  `F = Ω₊(x^{1/2−δ})`. RH is not needed; it only guarantees `e^{1−ρ} ≠ 2` for every zero, since
  that equation forces `Re ρ = 1 − log 2`.
- **Step 4, θ.** Landau alone fails here: the `√x` term puts a real pole at `s = 1/2`. Split on
  RH. If RH is false, a zero with `Re ρ > 1/2` gives `F = Ω₊(x^{Re ρ − δ})`, which beats `√x`.
  Under RH (a Lean theorem, `riemannHypothesis`), the explicit formula gives
  `F(x)/√x = −2 Re Σ_{γ>0} (2 − e^{1/2}e^{−iγ}) x^{iγ}/ρ + o(1)` (in the mean). Ingham's theorem
  with the Fejér kernel gives `limsup F_θ/√x ≥ −(2 − √e) + K_T(t₀)` for every `t₀`, where `K_T` is
  the Fejér-weighted partial sum over `γ < T`. This uses only that the finite trigonometric
  polynomial `K_T` is almost periodic; no LI is needed. Run 4: with the 10 zeros below 50,
  `K_50(2750.54) = 0.5885 > 0.3513`. The margin is 0.237. An error of `10^{-9}` in each `γ` moves
  `K_50` by less than `10^{-5}` at `t = 2750`, so 10 zeros known to 6 decimals suffice.
  Conclusion: `F_θ = Ω₊(√x)`, and the θ inequality fails for arbitrarily large `x`, under RH and
  without it.
- **Remaining space for witnesses.** None is needed for the theorem. For evidence, every prime
  `≤ 10^11` was tested (run 1).

### 1.3 Witnesses and numbers (run 1, `out/ramtype_1e11.txt`)

| Inequality | Failures among tested points `≤ 10^11` | Largest failing point `≤ 10^11` | Max of `(LHS−RHS)/x^{3/2}` |
|---|---|---|---|
| ψ | 2,092,895,980 (≈ 51% of points) | 99,555,795,379 | 1.928 at `x = 19` |
| θ | 1,116,026,207 (≈ 27%) | 96,422,442,679 | 1.599 at `x = 1627` |
| π (Ramanujan, calibration) | 25,816,212 | 38,358,837,677 (Dudek–Platt: last integer counterexample 38,358,837,682) | — |

The failure fractions stay stable: ψ 49% at `10^8`, 55% at `10^10`; θ 27% at `10^8`, 30% at
`10^10`. That is what an unbiased (ψ) or weakly biased (θ) almost-periodic sign predicts.

### 1.4 Independent verification

- **Interval arithmetic** (run 3, `out/verify_iv_1e8.txt`). For `x = 99,901,159`,
  `θ(x)² − e x θ(x/e) ∈ [15877275409.2577…, 15877275409.2577…]` (positive), and
  `ψ(x)² − e x ψ(x/e) ∈ [377982941140.46…, 377982941140.46…]`. For `x = 99,999,989`, ψ fails
  (`[207211024360.24…, …]`) and θ holds. Small cases, also certified: `x = 997` (both fail),
  `1627` (both), `935537` (both), `945823` (ψ only).
- **Quad precision, separate code** (run 2, `out/verify_1e10.txt`). At `x = 9,997,472,873`:
  `θ(x) = 9997417408.582209…`, `θ(⌊x/e⌋ = 3677864733) = 3677823913.095603…`,
  `(θ(x)² − e x θ(x/e))/x^{3/2} = 0.000332 > 0`, so the θ version fails. The absolute margin is
  `3.3·10^{11}`, against a rounding bound under `10^{-6}`. At `x = 10,000,000,019`, ψ fails
  (0.205) and θ holds.
- The quad check of the two largest witnesses (`96,422,442,679` and `99,555,795,379`) was still
  running when this report was written (`out/verify_1e11.txt`). It is *(unverified)* until that
  file shows "FAILS" for both.
- The explicit-formula prediction from 20,000 zeros matches the computed `F/√x` to about 0.06 at
  `x ≈ 10^6`. The gap is the sawtooth that the truncated sum does not capture.

### 1.5 Prior art

- **Semantic Scholar.** The citations of DOI 10.2478/cm-2021-0014: six papers. I read five:
  De arXiv:2407.18983 (π only); Dimitrov arXiv:2404.17165 (a survey, mentions Hassani's
  analogues without answering them); Axler arXiv:2207.02486 (§4 "Future work" discusses the
  `α ≠ e` variant only); Alkan, Czech. Math. J. 73 (2023) 15–48 (uses Hassani's `α`
  generalisation for π only); Johnston arXiv:2109.02249 (π only). The sixth, Alkan 2022 "A
  generalization of the Hardy–Littlewood conjecture", was not read.
- **Searches.** Web and arXiv searches for Ramanujan-type inequalities for θ and ψ found nothing.
  The GitHub code search for "Ramanujan" plus "Hassani" found only jaideepsaipadhi/ramanujans-
  inequality (2026-10, π only). I also searched for "Hassani" in 1337isnot1337/solved-
  conjectures, openai/math and google-deepmind/formal-conjectures: no hits. formal-conjectures has
  no statement of (10).
- **Not checked.** MathOverflow; zbMATH and MathSciNet reviews of Hassani 2021; the Alkan 2022
  paper; Hassani's later papers that might not cite the 2021 one.
- **Caveat.** The ψ argument is a textbook application of Landau, so an expert may regard it as
  folklore. The θ argument depends on the `√e` constant and is less obvious.

### 1.6 How Lean would check it

- **ψ (route a), effort M–L.**
  - Landau's theorem in riemann-hypothesis: `Deduction.landau_window`
    (`DedekindLFunctions/LandauTheorems/landauWindow.lean`). With it,
    `Deduction.mellin_Gchi_modOne` (the Mellin transform of the Riesz mean of ψ,
    `−(ζ'/ζ(s) + 1/(s−1) + 1 − (1+γ)s)/(s(s−1))`) and `Deduction.poleData_char` (poles at the
    zeros with residue `m·(−1/(ρ(ρ−1)))`). These names come from `docs/rh-lemmas/03`.
  - The fit is *(unverified)*. Those lemmas conclude "every pole has `Re ρ ≤ θ`" from a one-sided
    window bound on a Riesz mean. We would apply them to the Riesz mean of `−F`. That needs the
    two-term combination `2G(y) − eG(y/e)` and the factor `2 − e^{1−s}`, which must not cancel
    the pole at `ρ₁`. With RH (`riemannHypothesis`) every pole has `Re ρ = 1/2`, so a window
    bound with `θ < 1/2` contradicts any one zero.
  - At least one zero must exist. Candidates: schoenfeld-rh's `rosserZeroCount : RosserZeroCount`
    (Rosser's `N(T)` with error, so `N(T) > 0`), or `Speiser.Band` arithmetic to certify one sign
    change of `Z(t)` near 14.13.
  - Not needed: zero heights, LI, any computation.
- **θ (route a + certified zeros), effort L.**
  - Ingham's Fejér-kernel lemma (not in Lean as far as I know).
  - The explicit formula for ψ in the mean under RH (the cramer-rh mean-square machinery,
    `cramer_logMeanSquareAsymptotic`, is the closest premise).
  - Ten zeros below 50 to 6 decimals, certified. speiser-rh's proved-sound complex-disc checker
    for ζ (`coverOK_upper`/`coverOK_lower`) evaluates ζ to `2^{−64}` and could be adapted to
    certify sign changes of `Z(t)`.
  - The "RH false" branch is Landau as for ψ, but RH is a Lean theorem, so only the RH branch is
    needed.
- **Statement.** No formal-conjectures entry exists, so the statement would be ours:
  `¬ ∃ X, ∀ x ≥ X, ψ x ^ 2 < exp 1 * x * ψ (x / exp 1)` with Mathlib's `Chebyshev.psi` (check the
  name at the pin). The witnesses `x = 997`, `1627` and `99,901,159` serve as `native_decide`
  tests of the statement only, since an eventual statement has no finite refutation.

## 2. Hassani's n-th prime analogue: false for every `n ≥ 3`

- **Wording (same §4, item 2).** "an analogue of Ramanujan's inequality concerning the n-th prime
  reads as `p_n² < e n log n p_⌊n/e⌋`, or equivalently, by replacing n by e n, as
  `p_⌊en⌋² < e² n(1 + log n) p_n`."
- **Proof for `n ≥ 17`.** Dusart gives `p_n ≥ n(log n + log log n − 1)` for `n ≥ 2`. Rosser gives
  `p_m < m(log m + log log m)` for `m ≥ 6`, applied at `m = ⌊n/e⌋ ≤ n/e`. Hence
  `e n log n · p_{⌊n/e⌋} < n² L(L − 1 + log(L−1)) < n² L(L + l − 1)`, where `L = log n` and
  `l = log log n`. This is `< n²(L + l − 1)² ≤ p_n²` as soon as `l > 1`, that is `n > e^e`.
  Run 5 checks `3 ≤ n < 10^5` in interval arithmetic, and run 1 checks every `n ≤ 4.1·10^9`: the
  inequality fails at every `n`.
- **The second form.** It holds only at `n = 1` for `n < 10^5`, and fails asymptotically:
  `LHS − RHS ≈ e²n²L(log L − 1)`. That is my expansion; no explicit-constant proof is written
  here.
- **Value.** Low. It is a one-line consequence of the second term of Cipolla's expansion, and is
  likely a slip by the author. Lean needs Rosser–Schoenfeld-type bounds for `p_n`. These are
  derivable from schoenfeld-rh's `PiBound`, but under RH and only for large `n`. Effort S–M.

## 3. Hassani's progression analogue: true for x sufficiently large (a proof, not a disproof)

- **Wording (item 3).** "we may ask about the validity of the following inequality for x
  sufficiently large: `π(x;q,a)² < (e x/(φ(q) log x)) π(x/e;q,a)`".
- **Argument.** Put `P = φ(q)·π(x;q,a)`. Then the inequality is exactly Ramanujan's inequality for
  `P`. `P = li(x) + O(x·exp(−c√log x))` for fixed `q` by the classical prime number theorem for
  progressions (Siegel–Walfisz is in riemann-hypothesis). The two sides of Ramanujan's inequality
  differ at order `x²/log⁴x` (Hassani 2021, Thm 1). So it holds for all large `x`,
  unconditionally, for every fixed `(q, a)`. The psi-grh `piAP_unconditional` bound
  (`C√x log(qx)`, `C` existential) gives the same conclusion with a better error term.
- **Searches.** Run 1 for `q = 3, 4`: the inequality still fails just below `10^11` (last failures
  85,086,875,749 for (3,1); 99,999,999,977 for (3,2); 94,123,583,689 for (4,1);
  99,999,999,947 for (4,3)). So the last counterexample is above `10^11`, in contrast to
  `3.8·10^10` for `q = 1`. Finding it needs explicit GRH constants for `π(x;q,a)`, and psi-grh's
  `C` is existential. A route (ii) "last counterexample" result is therefore out of reach with our
  premises.

## 4. Mossinghoff–Trudgian Problem 3: `L_{1/2}(x) = Σ_{n≤x} λ(n)/√n ≤ 0` for `x ≥ 17` (no witness possible in range)

- **Source.**
  - Mossinghoff, Trudgian, *Between the problems of Pólya and Turán*, J. Aust. Math. Soc. 93
    (2012) 157–171, Problem 3. The conjecture and the range `17 ≤ x ≤ 10^12` are as cited by
    Humphries, J. Number Theory 133 (2013) 545–582 (arXiv:1108.1524), whose abstract says his
    result "lend[s] support to a conjecture of Mossinghoff and Trudgian that this weighted sum is
    nonpositive for all x ≥ 17". The original wording was not read *(unverified)*.
  - Humphries proves, under RH, LI and a negative-moment bound for `ζ'(ρ)`, that `L_{1/2}(x) < 0`
    outside a set of logarithmic density 0.
- **Why it looked like a candidate (route i).** The main term is only logarithmic, while the zero
  sum is unbounded under LI. So a violation is not ruled out, and it would sit where the low-zero
  sum is extremal.
- **Reduction chain.** The explicit formula, derived here and checked numerically (run 7: error
  ≤ 0.02 at `10^3 … 10^8`):

  ```
  L_{1/2}(x) = log x/(2ζ(1/2)) + γ/ζ(1/2) − ζ'(1/2)/(2ζ(1/2)²) + 2 Re Σ_{γ>0} ζ(1+2iγ) x^{iγ}/(iγ ζ'(ρ))
             = −0.342383 log x + 0.524414 + (zero sum)
  ```

  Beyond the exhausted range `10^12`, a witness needs the zero sum to exceed
  `0.3424 log x − 0.524 ≥ 8.94`.
  - The sum of all amplitudes, `2Σ|c_γ|`, is 2.153 for the first 1000 zeros and 2.866 for the
    first 5000. It grows by about 0.44 per e-fold in the number of zeros.
  - Even perfect alignment of every zero would need about `5·10^9` zeros, all in phase.
  - Kronecker alignment of `K` phases needs `log x` exponential in `K`, while the target grows
    linearly in `log x`. So no `x` with `log x` below any computable bound can be a witness, and
    the heuristic says the conjecture is true.
- **Toolkit.** Nothing helps. An RH proof of the conjecture would need lower bounds on
  `|ζ'(ρ)|`, and no repo has those. Mertens-type bounds such as `mertensSharp` are far too weak.
  **No search beyond the validation run, by design.**

## 5. Desk-checked candidates (no computation warranted)

| Candidate | Source | Why no search |
|---|---|---|
| Aoudjit–Berkane–Dusart: inequality (1.9), `σ(n)/n ≤ e^γ(log K(n) + log₂K(n) + log₂K(n)/log K(n))`, is "a sufficient and necessary criterion for the Riemann hypothesis" | quoted in Axler, arXiv:2406.04018 (2024), with ABD's Question 1 (does (1.9) hold for every `n ≥ 205`?) | Axler proves (1.9) unconditionally for `n ≥ 205` (Cor. 1.6). The "criterion" conjecture then holds only as a material equivalence, because RH is now a Lean theorem. There is nothing to refute |
| Leshchiner–Musin–Thompson Question 4: `Q(n) ≤ 3/2` for all sufficiently large CA numbers, `Q = e^{−γ}(R − T) log log n` | arXiv:2610.39120 (2026-10-29), §3.3. Observed `0.36 ≲ Q ≲ 1.25` for `u = log log n ≤ 25` | An "eventually" question, so no finite witness refutes it. A route (i) attack needs their exact `R`, `T` and the second-order zero terms. Not attempted; recorded as a lead (below) |
| Musin, nested CA classes, RH ⇔ Robin on one class | arXiv:2609.33794 (v2 2026-11-18) | RH-equivalent statements. They follow from `robin_unconditional` plus the paper's equivalence, which is proof lane work, not refutation |
| Mishra–Sarkar ω-truncated Robin inequality ⇔ RH | arXiv:2609.26787 (2026-09-22) | Same: provable from `robin_unconditional` plus their equivalence (toolkit-reuse lane) |
| Kanold, least prime `p(q,a) < q²` | folklore | Our `bachSorenson_two_unconditional` gives `< 2(q log q)²`, weaker than `q²`, so nothing becomes finite. The heuristic `p(q) ≍ φ(q) log² q` makes a witness implausible |
| Mertens' product sign `e^γ log x ∏(1−1/p) < 1`; `θ(x) < x`; `Σ1/p − log log x − B > 0` | Rosser–Schoenfeld; Robin; Diamond–Pintz 2009 | Known Ω-results. The first violations sit at Skewes scale with no explicit witness, as `disproof-literature` says |

**A side finding for ramanujan-rh.** The tier-H hypothesis `RamanujanVerifiedRange` there is the
range `[38,358,837,683, e^40]`. That range is covered on paper by Platt–Trudgian (unconditional
for `38,358,837,683 ≤ x ≤ e^56`, as cited by Hassani 2021, ref. [10], arXiv:1809.03134) and by
Johnston, arXiv:2109.02249, Thm 5.1 (to `exp(103)`). Neither is in Lean. The tracker's "Literature
not confirmed" item should cite them.

## Best unfinished lead

Lean for §1. The ψ question first, with Landau and no computation. Then θ, through Ingham plus 10
certified zeros. Before any build:

1. Read `Deduction.landau_window` and `Deduction.mellin_Gchi_modOne` at riemann-hypothesis
   `507a75d91d`, and decide whether the two-term Riesz mean `2G(y) − eG(y/e)` fits their
   `WindowHyp` with `θ < 1/2`.
2. Run the novelty search again in the places not checked: MathOverflow, zbMATH, the sixth citing
   paper.
3. Ask the owner whether a negative answer to a 2021 "we may ask" counts under "Priority" item 1.

The Leshchiner–Musin–Thompson residual `Q(n)` (Question 4) is the one structural route (i)
candidate left. Its definitions need reading first.

## Proposed edges

```jsonl
{"premise": "Landau's oscillation theorem + zeta has no zeros in (0,1) + a zero rho with e^{1-rho} != 2 (any zero under RH)", "premise_status": "lean-proved", "premise_lean_source": "riemann-hypothesis Deduction.landau_window, Deduction.mellin_Gchi_modOne (names from docs/rh-lemmas/03, fit unverified); riemannHypothesis; schoenfeld-rh rosserZeroCount for existence of a zero", "consequence": "NOT (psi(x)^2 < e x psi(x/e) for all sufficiently large x); fails at ~51% of primes <= 1e11, largest found 99555795379", "consequence_ref": "Hassani, Commun. Math. 29 (2021) 473-482, Sec. 4 item 1, (10); no fc statement", "consequence_status": "open", "implication_source": "this lane: Mellin transform (2 - e^{1-s}) M(s), Landau", "effort": "M-L", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route a; a negative answer to a posed question, not a named conjecture; no published answer found (Semantic Scholar citations 5/6 read, arXiv, GitHub, 1337, openai/math, fc); label new needs owner sign-off", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "RH (riemannHypothesis) + Ingham Fejer-kernel lemma + 10 certified zeros below 50 (K_50(2750.54) = 0.5885 > 2 - sqrt e = 0.3513); Landau if RH false", "premise_status": "lean-proved", "premise_lean_source": "riemann-hypothesis riemannHypothesis; Ingham lemma and certified zeros not in Lean (speiser-rh checker could be adapted)", "consequence": "NOT (theta(x)^2 < e x theta(x/e) for all sufficiently large x); fails at ~27% of primes <= 1e11, largest found 96422442679", "consequence_ref": "Hassani, Commun. Math. 29 (2021), Sec. 4 item 1, (10)", "consequence_status": "open", "implication_source": "this lane", "effort": "L", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route a; witnesses certified by interval arithmetic at 99901159, quad precision at 9997472873", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "Dusart p_n >= n(log n + log log n - 1); Rosser p_m < m(log m + log log m), m >= 6; finite check 3 <= n <= 16", "premise_status": "theorem", "premise_lean_source": "", "consequence": "p_n^2 < e n log n p_{floor(n/e)} is false for every n >= 3", "consequence_ref": "Hassani, Commun. Math. 29 (2021), Sec. 4 item 2", "consequence_status": "open", "implication_source": "this lane (elementary)", "effort": "S-M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "likely a slip in the question; low value; checked n <= 4.1e9", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "PNT in progressions with classical error (Siegel-Walfisz, riemann-hypothesis) or psi-grh piAP_unconditional", "premise_status": "lean-proved", "premise_lean_source": "psi-grh piAP_unconditional (C existential)", "consequence": "pi(x;q,a)^2 < e x/(phi(q) log x) pi(x/e;q,a) for x sufficiently large, each fixed (q,a)", "consequence_ref": "Hassani, Commun. Math. 29 (2021), Sec. 4 item 3", "consequence_status": "open", "implication_source": "this lane: reduces to Ramanujan's expansion for phi(q) pi(x;q,a)", "effort": "M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "a proof, not a disproof; last counterexamples for q = 3, 4 exceed 1e11; explicit threshold needs explicit GRH constants", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "explicit formula for L_{1/2}; amplitude sum 2 sum |c_gamma| = 2.866 over 5000 zeros", "premise_status": "theorem", "premise_lean_source": "", "consequence": "NOT (L_{1/2}(x) <= 0 for all x >= 17)", "consequence_ref": "Mossinghoff-Trudgian, J. Aust. Math. Soc. 93 (2012), Problem 3 (via Humphries arXiv:1108.1524)", "consequence_status": "open", "implication_source": "", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 2, "notes": "rejected: a witness beyond 1e12 needs the zero sum >= 8.94, about 5e9 aligned zeros; heuristically true; no toolkit premise", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "Axler arXiv:2406.04018 Cor. 1.6 ((1.9) holds for n >= 205) + RH in Lean", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Aoudjit-Berkane-Dusart: (1.9) is a necessary and sufficient criterion for RH", "consequence_ref": "Aoudjit-Berkane-Dusart (JIS 2021 / NNTDM 27(4) 2021), as quoted by Axler 2024", "consequence_status": "solved", "implication_source": "Axler 2024", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected: holds only as a material equivalence; nothing to refute", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "zeta-zero explicit formula for the CA residual Q(n)", "premise_status": "open", "premise_lean_source": "", "consequence": "Q(n) <= 3/2 for all sufficiently large CA numbers", "consequence_ref": "Leshchiner-Musin-Thompson arXiv:2610.39120, Question 4", "consequence_status": "open", "implication_source": "", "effort": "L", "lean_exists": "", "in_1337": false, "class": 2, "notes": "lead, not attempted: an eventual question; needs definitions of R, T", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
{"premise": "Platt-Trudgian arXiv:1809.03134; Johnston arXiv:2109.02249 Thm 5.1", "premise_status": "theorem", "premise_lean_source": "", "consequence": "RamanujanVerifiedRange [38358837683, e^40] (ramanujan-rh tier-H input)", "consequence_ref": "ramanujan-rh RamanujanVerifiedRange", "consequence_status": "solved", "implication_source": "Platt-Trudgian (to e^56, as cited by Hassani 2021); Johnston (to exp(103))", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 1, "notes": "paper result only; cite in the tracker's literature item", "sweep": "2026-11-26", "lane": "disproof-rh-toolkit"}
```
