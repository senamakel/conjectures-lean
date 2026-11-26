# Conjectures in Lean

Machine-checked Lean 4 proofs of conjectures and theorems in number theory, each project in its own
folder under [`conjectures/`](conjectures/). The table lists every project, finished or not,
together with the attempts that never became a project. RH and GRH for Dirichlet L-functions come from
Levent Alpöge's Lean proof ([riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)),
which the Lean FRO and the Mathlib Initiative
[certified](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) on 21 November 2026.

[Docs](docs/) · [Status tracker and rules](AGENTS.md) · [Literature status](docs/LITERATURE_STATUS.md) · [Next targets](docs/NEXT_TARGETS.md) · [Paper](paper/)

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

## Attempted, no project

| Problem | Where | Lean | Notes |
| :--- | :--- | :---: | :--- |
| Erdős Problem 404(ii) | [`docs/scoping/erdos-404/`](docs/scoping/erdos-404/) | ⬜ | Spike: a plausible invariant, no proof; stopped |
| Powerful numbers: error term below `x^{1/6}` under RH | [`docs/scoping/powerful-numbers-error-term.md`](docs/scoping/powerful-numbers-error-term.md) | ⬜ | Scoped, not started |
| Open Erdős problems #3–#1221 | [`docs/scoping/`](docs/scoping/erdos-discovery-part1.md) | ⬜ | Discovery sweep in three parts; nothing kept beyond 985, 770, 233, 969 |

## Layout

| Path | Content |
|---|---|
| `conjectures/<name>/` | one Lean package per project (`lakefile`, `lean-toolchain`, `README.md`) |
| `docs/` | literature status, next targets, scoping and research reports, RH-repo lemma specs |
| `paper/` | the write-up |
| `AGENTS.md` | per-project checklist, proof-tier rules and README rules |

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

## How the conjectures were attempted

Every repo was built the same way, and most of what went wrong went wrong in the same few places.

**The statement comes first.** Before any proof, the target goes into `<Pkg>/Statement.lean` and
is not edited again. Where formal-conjectures has the statement, we copy it word for word. Where
it doesn't, we transcribe it from the paper and say so. This rule exists because the easiest way
to finish a hard proof is to weaken what it claims, and with a fixed file that shows up in a diff.

**RH is an argument of the theorem.** The main library of each repo never imports the RH proof.
A theorem reads `RiemannHypothesis → X` or `DirichletLNonvanishingRightOfHalf → X`, and a
separate `Unconditional/` file supplies the hypothesis from riemann-hypothesis in one line. So
each repo holds two results: the implication, which stands on Mathlib alone, and the
unconditional theorem.

**Agents did the proving, one per repo.** [OpenHuman](https://github.com/tinyhumansai/openhuman)
subagents each took one target on its own branch and opened a pull request. A lead session
then rebuilt the branch, read the `#print axioms` output itself, ran the unconditional check and
merged. An agent's report was never accepted without that rebuild. On 2026-11-22 a stale checkout
printed `sorryAx` under a headline theorem, and the rule dates from then.

**Large `x` by analysis, small `x` by computation.** Most of these theorems hold "for all `x`
above some point", and an explicit proof only works above a threshold. Below it we check every
case with a program whose correctness is proved in Lean and which runs through `native_decide`.
The work is in making the two ranges meet: sharpen the analytic constants until the threshold
drops to something a machine can reach. Three examples:

- erdos-985 checks every prime below `10^8`.
- grosswald-grh checks every prime below `10^13` in 2,502 chunks, about 3.3 million CPU-seconds.
- robin-rh sieves every integer below `1.07·10^13` in 624 chunks, about 54 core-hours.
- speiser-rh covers the band `5/2 ≤ |Im s| < 7` with 142,446 small discs in three minutes.

Agents write and size these checkers but do not run the large ones. The big runs go last, one at
a time, after an early attempt to run several at once overloaded the build machine.

**The published constant is the target.** A first proof often lands with a weaker constant than
the paper's, and the README then states the constant actually proved and why. Each of those
gaps was later closed. Bach's bound for the least non-residue went from `21/5` to `11/4` to
Bach's own `2` (lls-grh). Bach and Sorenson's bound went from `7/2` to their `2`. Schoenfeld's
bounds went from `1/8` to his `1/(8π)`, and Cramér's prime-gap constant from `2` to
Carneiro, Milinovich and Soundararajan's `22/25`. In every case the first estimate of what the
paper's constant would cost was too high: the barrier came from one loose step, and keeping
that step exact removed it.

**Missing background theory becomes a named hypothesis.** Some proofs need a classical theorem
that Mathlib doesn't have at our pin, such as the Kronecker-Weber theorem or Dirichlet's class
number formula. Those enter as explicit `Prop` arguments, never as `sorry`, and the
`Unconditional/` file discharges them from lemmas inside riemann-hypothesis where it has them.

**What did not work.**

- Erdős 233 asks for more than RH is known to give. We proved the classical RH bounds
  (Selberg's); the problem as posed stays open.
- A search for open Erdős problems that RH would settle by a new argument found nothing we kept.
- Several first guesses about attribution were wrong and were corrected against the papers.

The reasoning behind each dead end, and the constants that were sized up and rejected, are in
LivingBrain. The status of every box is in [`AGENTS.md`](AGENTS.md).

**Public Lean code.** When a repo stalls we search for existing formalisations before writing
more. The search has turned up kernel-checked zeta enclosures
([smmercuri/zeta](https://github.com/smmercuri/zeta),
[teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab)), explicit zero counting
([anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean)) and a Weil explicit
formula inside calr3/ternary-goldbach. These are permissively licensed, so files can be vendored
with credit. riemann-hypothesis has no licence, so we import it and copy nothing from it.

## Licence

This repository, every project folder included, is licensed under the
[GNU General Public License v3](LICENSE). Files vendored from other projects keep their own
licences (Apache-2.0 or MIT); each repo's Credits section and NOTICE files list them.
