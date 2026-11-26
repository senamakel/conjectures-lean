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

28 projects: 19 proved in full, 7 proved in part, 1 conditional at its ceiling, 1 wound down.

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

**Lean status.** ✅ the target statement is proved, end to end from Lean's three standard axioms plus
the finite computations its README names. 🟡 part of the target, or a weaker constant, is proved
and the README says what is left. 🟠 proved with a hypothesis that can't be discharged yet.
⬜ attempted and stopped.

**Literature.** *RH-consequence*: a published theorem "RH (or GRH) implies X". *RH-equivalent*: X is
equivalent to RH. *known*: proved in the literature without RH. Attributions are in
[`docs/LITERATURE_STATUS.md`](docs/LITERATURE_STATUS.md). Each folder's README gives the exact
Lean statements, `#print axioms` output and build instructions.

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
