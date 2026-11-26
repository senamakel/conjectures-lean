# Conjectures in Lean

Machine-checked Lean 4 proofs of mathematical conjectures and theorems, each project in its own
folder under [`conjectures/`](conjectures/). The table lists every project, finished or not,
together with the attempts that never became a project. RH and GRH for Dirichlet L-functions come from
Levent Alpöge's Lean proof ([riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)),
which the Lean FRO and the Mathlib Initiative
[certified](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) on 21 November 2026.

The first 28 projects are consequences of RH and GRH. From 26 November 2026 the scope is any
open conjecture that can be settled by connecting results that already exist: lemmas inside big
Lean proofs, the theorems below, recently solved conjectures, and published implications between
conjectures. Those links are collected in the [implication atlas](docs/atlas/).

[Docs](docs/) · [Atlas](docs/atlas/) · [Further projects](docs/FURTHER_PROJECTS.md) · [Attempts](docs/ATTEMPTS.md) · [Method](docs/METHOD.md) · [Status tracker and rules](AGENTS.md) · [Literature status](docs/LITERATURE_STATUS.md) · [Next targets](docs/NEXT_TARGETS.md) · [Paper](paper/)

## Results

42 projects: 24 proved in full, 15 proved in part, 1 conditional at its ceiling, 1 wound down, and 1 collection of implications between open conjectures (listed in the next section).

| Conjecture | Folder | Lean | Literature |
| :--- | :--- | :---: | :--- |
| **1.** Erdős Problem 985: every odd prime has a prime primitive root `q < p` | [`erdos-985`](conjectures/erdos-985/) | ✅ | RH-consequence |
| **2.** Lindelöf hypothesis, for ζ and for Dirichlet L-functions | [`lindelof-rh`](conjectures/lindelof-rh/) | ✅ | RH-consequence |
| **3.** Density hypothesis for ζ (and `N(T) ≪ T log T` with no hypothesis) | [`density-rh`](conjectures/density-rh/) | ✅ | RH-consequence |
| **4.** Grosswald's conjecture: `g(p) < √p − 2` for every prime `p > 409` | [`grosswald-grh`](conjectures/grosswald-grh/) | ✅ | RH-consequence |
| **5.** Euler's 65 idoneal numbers are the only ones | [`weinberger-grh`](conjectures/weinberger-grh/) | ✅ | RH-consequence |
| **6.** Extended Riemann hypothesis for every finite abelian extension of ℚ | [`abelian-erh`](conjectures/abelian-erh/) | ✅ | RH-consequence |
| **7.** Robin's inequality `σ(n) < e^γ n log log n` for `n > 5040` | [`robin-rh`](conjectures/robin-rh/) | ✅ | RH-equivalent |
| **8.** Nicolas' inequality at every primorial | [`nicolas-rh`](conjectures/nicolas-rh/) | ✅ | RH-equivalent |
| **9.** Li's criterion, positivity direction: `λ_n > 0` | [`li-criterion-rh`](conjectures/li-criterion-rh/) | ✅ | RH-equivalent |
| **10.** Speiser's theorem: `ζ'(s) ≠ 0` for `0 < Re s < 1/2` | [`speiser-rh`](conjectures/speiser-rh/) | ✅ | RH-equivalent |
| **11.** Mertens bound `M(x) = O(x^{1/2+ε})`, with Riesz, Hardy–Littlewood, Redheffer and Franel–Landau | [`mertens-rh`](conjectures/mertens-rh/) | ✅ | RH-equivalent |
| **12.** Lamzouri–Li–Soundararajan: every theorem of the paper, and Bach's constant `2` | [`lls-grh`](conjectures/lls-grh/) | ✅ | RH-consequence |
| **13.** Bach–Sorenson: least prime `p ≡ a (mod q)` is `< 2(q log q)²` | [`bach-sorenson-grh`](conjectures/bach-sorenson-grh/) | ✅ | RH-consequence |
| **14.** Schoenfeld's bounds for `ψ`, `θ` and `π − li` with constant `1/(8π)` | [`schoenfeld-rh`](conjectures/schoenfeld-rh/) | ✅ | RH-consequence |
| **15.** Cramér's prime-gap theorem with constant `22/25` | [`cramer-rh`](conjectures/cramer-rh/) | ✅ | RH-consequence |
| **16.** Littlewood's bound `\|ζ(1/2+it)\| ≤ exp(C log t / log log t)` | [`littlewood-rh`](conjectures/littlewood-rh/) | ✅ | RH-consequence |
| **17.** `ψ(x,χ)` and primes in arithmetic progressions, uniform in `q` | [`psi-grh`](conjectures/psi-grh/) | ✅ | RH-consequence |
| **18.** Fujii's average Goldbach bound `Σ G(n) = x²/2 + O(x^{3/2})` | [`goldbach-average-rh`](conjectures/goldbach-average-rh/) | ✅ | RH-equivalent |
| **19.** Hironaka's resolution of singularities in characteristic 0 | [`hironaka-fc`](conjectures/hironaka-fc/) | ✅ | known |
| **20.** Erdős Problem 770, part (iii); parts (i) and (ii) open | [`erdos-770`](conjectures/erdos-770/) | 🟡 | RH-consequence |
| **21.** Erdős Problem 233: the RH bound `O(N log⁴ N)`; `N log² N` open | [`erdos-233`](conjectures/erdos-233/) | 🟡 | RH-consequence |
| **22.** Erdős Problem 969: Montgomery–Vaughan's `E_k(x) = O(x^{1/(k+1)+ε})` | [`erdos-969`](conjectures/erdos-969/) | 🟡 | RH-consequence |
| **23.** Bach's explicit Ankeny bound, constant `21/5` here (`2` in lls-grh) | [`ankeny-grh`](conjectures/ankeny-grh/) | 🟡 | RH-consequence |
| **24.** Deterministic Miller–Rabin, constant `21/5` here (`2` in lls-grh) | [`miller-grh`](conjectures/miller-grh/) | 🟡 | RH-consequence |
| **25.** Shoup's least primitive root bound: `ω^{21/5} log² p` proved, Shoup's `ω⁴(log ω+1)⁴` not | [`shoup-grh`](conjectures/shoup-grh/) | 🟡 | RH-consequence |
| **26.** Mills' constant: 87 decimals proved, Caldwell–Cheng's 600 not | [`mills-rh`](conjectures/mills-rh/) | 🟡 | RH-consequence |
| **27.** Artin's primitive root conjecture (Hooley): proved given Hooley's hypothesis; needs GRH for non-abelian fields | [`artin-grh`](conjectures/artin-grh/) | 🟠 | RH-consequence |
| **28.** Ternary Goldbach under GRH (proved without GRH by Helfgott 2013) | [`goldbach-grh`](conjectures/goldbach-grh/) | ⬜ | known |
| **29.** A prime between `x^α` and `(x+1)^α` for every real `α ≥ 3`: proved from RH, with RH supplied by the riemann-hypothesis repository | [`prime-powers-rh`](conjectures/prime-powers-rh/) | ✅ | RH-consequence |
| **30.** Bach's bound, three corollaries: `(ℤ/m)ˣ` is generated by the integers `≤ 2 log² m`, deterministic Solovay–Strassen, Miller's factoring. Proved from Bach's bound with constant `2`, supplied under GRH by lls-grh and the riemann-hypothesis repository | [`bach-corollaries-grh`](conjectures/bach-corollaries-grh/) | ✅ | RH-consequence |
| **31.** Implications between open conjectures (table below) | [`implications`](conjectures/implications/) | 🔗 | see below |
| **32.** Ramanujan's inequality `π(x)² < (e·x/log x)·π(x/e)` for every `x ≥ e⁴⁰`: proved from RH, with RH supplied by the riemann-hypothesis repository. The range `38,358,837,683 ≤ x < e⁴⁰` is a cited hypothesis (`RamanujanVerifiedRange`) | [`ramanujan-rh`](conjectures/ramanujan-rh/) | 🟡 | RH-consequence |
| **33.** Legendre, Oppermann, Andrica and Brocard each fail for at most `O(log³ N)` of the first `N` indices: proved from RH, with RH supplied by the riemann-hypothesis repository. These bound the exceptions and prove none of the four | [`legendre-exceptions-rh`](conjectures/legendre-exceptions-rh/) | ✅ | RH-consequence |
| **34.** Solé–Planat's inequality at every primorial, infinitely many extremely abundant numbers, and `4` as the only extraordinary number: proved from RH and Robin's inequality, both supplied by the riemann-hypothesis and robin-rh repositories | [`abundant-rh`](conjectures/abundant-rh/) | ✅ | RH-equivalent |
| **35.** Hajós's conjecture is false: a Lean proof of Catlin's (1979) disproof, at `k = 8` | [`hajos-catlin`](conjectures/hajos-catlin/) | ✅ | known |
| **36.** Pólya's conjecture `L(n) ≤ 0` is false (`L(906150257) = 1`), and so is von Sterneck's `\|M(x)\| < ½√x` (`M(7725038629) = 43947`) | [`polya-liouville`](conjectures/polya-liouville/) | ✅ | known |
| **37.** The Cookson Hills series `Σ sec²(n)/n³` converges (and the Flint Hills series `Σ csc²(n)/n³`, rebuilt here). From `μ(π) = 2`, proved in Lean by [openai/math](https://github.com/openai/math) and vendored | [`cookson-hills`](conjectures/cookson-hills/) | ✅ | consequence of `μ(π) = 2` (OpenAI 2026) |
| **38.** Sun's conjecture (OEIS A038098): `π(n^k)/n^k` is strictly decreasing in `n`, proved for every `k ≥ 4` from RH; the run that supplies RH is pending. `k = 3` is proved outside `141 ≤ n < 10⁷` | [`sun-prime-density-rh`](conjectures/sun-prime-density-rh/) | 🟡 | RH-consequence; no proof found in the literature |
| **39.** Every odd prime `p` has a prime primitive root `q < p` modulo `p²`, hence modulo every `p^k` (Erdős Problem 985 for prime powers): proved from GRH; the run that supplies GRH is pending | [`primitive-root-sq-grh`](conjectures/primitive-root-sq-grh/) | 🟡 | RH-consequence; the all-`p` statement was not found in the literature |
| **40.** Two monotonicity conjectures of Sun on `π(x)` (arXiv:1402.6641): `π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}` for `n > 4`, `1 ≤ k ≤ n` (Conj. 2.7(i), OEIS A238165), and `π(n²)^{1/n}` strictly decreasing for `n ≥ 3` (Conj. 2.14(ii), OEIS A038107). No RH | [`sun-pi-inequalities`](conjectures/sun-pi-inequalities/) | ✅ | no proof found in the literature |
| **41.** Conjecture 5.6 of Gawron–Miska–Ulas (2018) on `m`-coloured binary partitions is false: `b₁(16) − b₁(4) = 32` is not divisible by `2^6`; it also fails at `m = 3, 4, 5, 6`. A minor correction; `m = 1` follows from Churchhouse's congruence (Rødseth 1970) | [`gmu-binary-partitions`](conjectures/gmu-binary-partitions/) | ✅ | *new*, pending the owner's sign-off |
| **42.** Bach's sharp generator constant: under GRH, `(ℤ/m)ˣ` is generated by the integers `≤ (2/log² 3) log² m`. Proved that no smaller constant works (equality at `m = 3`), the bound for every `m < 2^17` (no GRH) and, from GRH, for every `m ≥ 5·2^49`; the range `2^17 ≤ m < 5·2^49` is open. The run that supplies GRH is pending | [`bach-sharp-grh`](conjectures/bach-sharp-grh/) | 🟡 | RH-consequence; the sharp constant was not found in the literature |

**Lean status.** ✅ the target statement is proved, end to end from Lean's three standard axioms plus
the finite computations its README names. 🟡 part of the target, or a weaker constant, is proved
and the README says what is left. 🟠 proved with a hypothesis that can't be discharged yet.
⬜ attempted and stopped. 🔗 an implication: the theorem is proved, and its premise is an explicit
hypothesis that is itself open.

**Literature.** *RH-consequence*: a published theorem "RH (or GRH) implies X". *RH-equivalent*: X is
equivalent to RH. *known*: proved in the literature without RH. *new*: not found in the literature (searches listed in the project README); the label on the Gawron–Miska–Ulas row is pending the owner's sign-off. Attributions are in
[`docs/LITERATURE_STATUS.md`](docs/LITERATURE_STATUS.md). Each folder's README gives the exact
Lean statements, `#print axioms` output and build instructions.

## Implications between conjectures

Each row is a Lean theorem `premise → consequence`, in [`conjectures/implications`](conjectures/implications/).
Where formal-conjectures has the statements, both sides are copied from it word for word. Every
theorem depends on Lean's three standard axioms only. A row does not settle its consequence: it
becomes an unconditional theorem the day its premise is proved in Lean. A row may also be a
refutation, `premise → ¬ consequence` (the [refutation lane](AGENTS.md#disproofs-the-refutation-lane)): then the two
conjectures cannot both hold, and neither is settled. The links were found
with the [implication atlas](docs/atlas/).

| Premise | Consequence | Notes |
| :--- | :--- | :--- |
| abc conjecture | Erdős Problem 936: `2^n ± 1` and `n! ± 1` are powerful for only finitely many `n` (all four statements) | after Cushing–Pascoe and CrowdMath |
| abc conjecture | Erdős Problem 977, factorial variant: `P(n! + 1)/n → ∞` | after Murty–Wong |
| abc conjecture | infinitely many non-Wieferich primes | after Silverman 1988 |
| abc conjecture | finitely many triples of consecutive powerful numbers; `n! + 1 = m²` has finitely many solutions; finiteness forms related to Erdős Problem 366 | these finiteness statements are ours: formal-conjectures states the stronger "none exist" forms, which abc does not give |
| abc conjecture | its constant form and its quality form in formal-conjectures (equivalences) | |
| Cramér's conjecture, its strict form, or Firoozbakht's conjecture | Erdős Problem 382, part (i) | also from any gap bound `p_{n+1} − p_n ≤ p_n^ε`; includes Firoozbakht ⇒ Cramér |
| Dickson's conjecture | Erdős Problem 647, the "infinitely many" variant | Erdős noted it follows from hypothesis H; we found no written proof |
| Dickson's conjecture | Erdős Problem 891, Weisenberg's variant | stated in formal-conjectures with this hypothesis, unproved there |
| Dickson's conjecture | infinitely many twin, cousin, sexy and safe primes | each against its formal-conjectures statement |
| Dickson's conjecture | every admissible pattern occurs at consecutive primes; hence Erdős Problem 141 (`k` consecutive primes in arithmetic progression, every `k`, infinitely often), the equal-gaps variant of Erdős Problem 218, and infinitely many balanced primes of every order | seven formal-conjectures statements |
| Schinzel's hypothesis H | Dickson's conjecture; Bunyakovsky's conjecture | |
| Firoozbakht's conjecture | Oppermann, Andrica, Legendre and Brocard | attributed to Ferreira–Mariano; proof written independently |
| Oppermann's conjecture | Andrica's conjecture | |
| Andrica's conjecture | Legendre's conjecture | |
| Butson-type Hadamard matrices `H(4, 2m)` exist for every `m` | Hadamard conjecture | Turyn's doubling |
| Four exponentials conjecture | `2^t` or `3^t` is transcendental for every irrational `t` | |
| `r_k(N) ≤ C·N·exp(−c (log log N)^{1+η})` for every `k ≥ 3` | Erdős Problem 142, lower variant `r_k(N) = o(N/log N)`; Erdős Problem 140 for every `k` | the premise is a Lean theorem of [openai/math](https://github.com/openai/math) (Erdős #3); it is a hypothesis here because that library is on another Lean version, and the link has not been typechecked |
| first Hardy–Littlewood conjecture (prime `k`-tuples asymptotic, every tuple) | the second Hardy–Littlewood conjecture `π(x + y) ≤ π(x) + π(y)` is **false** (Hensley–Richards 1973, Richards 1974) | a refutation link: both conjectures stay open, and no explicit counterexample is known. One admissible 447-tuple of width 3158 (Polymath8 database; `π(3159) = 446`) and positivity of its singular series suffice. `sorry` in formal-conjectures until now; no `native_decide` |
| infinitely many squarefree `2^n − 1` | infinitely many non-Wieferich primes (Rotkiewicz 1965) | a theorem, not a conjecture-to-conjecture link; `sorry` in formal-conjectures until now |

## Disproved and refuted

Conjectures shown false, or shown incompatible with another conjecture. A refutation link
`X → ¬Y` proves that `X` and `Y` cannot both hold; it disproves neither on its own. Each theorem
is in [`conjectures/implications`](conjectures/implications/), with statements copied word for
word from formal-conjectures. The incompatibility links in the first table depend on Lean's three standard axioms only; the two outright disproofs below it use one `native_decide` each.

| Refuted | Given | Lean theorem | Notes |
| :--- | :--- | :--- | :--- |
| Second Hardy–Littlewood conjecture, `π(x + y) ≤ π(x) + π(y)` | first Hardy–Littlewood conjecture (prime `k`-tuples) | `not_first_and_secondHardyLittlewoodConjecture` | Hensley–Richards 1973, Richards 1974. Uses one admissible 447-tuple of width 3158 against `π(3159) = 446`. No explicit counterexample is known |
| Cramér's `limsup g_n / log² p_n = 1` | Granville's conjecture (`limsup ≥ 2e^{−γ}`) | `not_limsupEqOne_of_granville` | Granville 1995; the only arithmetic is `1 < 2e^{−γ}` |
| Strict Cramér bound `g_n < log² p_n` for `n ≥ 4` | Granville's conjecture | `not_strictBound_of_granville` | |
| Shanks' conjecture on maximal prime gaps | Granville's conjecture | `not_shanks_of_granville` | |
| Granville's conjecture | Firoozbakht's conjecture, with its cited consequence `g_n < log² p_n − log p_n` as a second hypothesis | `not_granville_of_firoozbakht` | the cited consequence (Kourbatov) is not proved here |

Outright disproofs, in [`conjectures/polya-liouville`](conjectures/polya-liouville/) (tier D, no hypotheses). Each uses the standard three axioms plus one `native_decide` with a proved-sound checker.

| Disproved | Lean theorem | Notes |
| :--- | :--- | :--- |
| Pólya's conjecture `L(n) ≤ 0` for `n ≥ 2` | `polya_conjecture_false` | `L(906150257) = 1`; Haselgrove 1958, Tanaka 1980 |
| von Sterneck's conjecture `\|M(x)\| < ½√x` for `x > 200` | `vonSterneck_conjecture_false` | `M(7725038629) = 43947`; Neubauer 1963, Cohen–Dress 1979 |

A new counterexample, in [`conjectures/gmu-binary-partitions`](conjectures/gmu-binary-partitions/) (tier D, no hypotheses, Lean's three standard axioms; the extra `m = 6` witness uses two `native_decide` with a proved-sound checker).

| Disproved | Lean theorem | Notes |
| :--- | :--- | :--- |
| Gawron–Miska–Ulas Conjecture 5.6 (arXiv:1703.01955), `b_{2^m−1}(2^{k+1}n) ≡ b_{2^m−1}(2^{k−1}n) (mod 2^{4⌊(k+1)/2⌋−2})` for `k ≥ m + 2` | `gmu_conjecture_5_6_false` | `m = 1, k = 3, n = 1`: `36 − 4 = 32`. The `m = 1` failures follow from Churchhouse's congruence (Rødseth 1970, Gupta 1971); the failures at `m = 3, 4, 5, 6` are not covered by any result we found. Holds for `m = 2` in our computations |

All of the incompatibility links above are between open conjectures. The reports behind this lane, with
the candidates for outright disproofs, are in [`docs/atlas/sweeps/2026-11-26/`](docs/atlas/sweeps/2026-11-26/)
(`disproof-erdos.md`, `disproof-fc-other.md`, `disproof-literature.md`).

## How it was built

The Lean proofs were built with [OpenHuman](https://github.com/tinyhumansai/openhuman) agents
running in an [RSI Ralph](https://github.com/tinyhumansai/rsi-ralph) loop. RSI Ralph keeps
asking a team of agents to improve a working copy and only keeps a change when a score says it
is better. Here the score is the Lean kernel: a change is kept when the repo builds and
`#print axioms` shows nothing beyond the allowed list.

The stack behind the agents:

| Role | Provider |
|---|---|
| Agents | [OpenHuman](https://github.com/tinyhumansai/openhuman) |
| Loop | [RSI Ralph](https://github.com/tinyhumansai/rsi-ralph) |
| Memory | [LivingBrain](https://livingbrain.com) |
| Search | [Exa](https://exa.ai) ([@ExaAILabs](https://x.com/ExaAILabs)) |

Agent roles are defined in [`.claude/agents/`](.claude/agents/): a scout that finds implications
and records them in the atlas, a lemma miner that inventories big proofs, a prover, a mechanic
for scaffolding and checkers, and an auditor that rebuilds every result and reads its axioms
before it is merged.

## Licence

This repository, every project folder included, is licensed under the
[GNU General Public License v3](LICENSE). Files vendored from other projects keep their own
licences (Apache-2.0 or MIT); each repo's Credits section and NOTICE files list them.
