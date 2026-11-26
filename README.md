# Conjectures

Machine-checked Lean 4 proofs in number theory: 17 projects, each a consequence of the
Riemann Hypothesis or of GRH for Dirichlet L-functions, and 11 further projects they build on or
that sit beside them. Each project is a folder of this repository, a Lean package of its own,
imported with its full commit history from its former standalone repository.

On 20 November 2026 Levent Alpöge released a Lean proof of RH and of GRH for Dirichlet
L-functions. The Lean FRO and the Mathlib Initiative
[certified it](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) the next
day, and independent kernels accept the exported proof
([Sutherland's verification files](https://math.mit.edu/~drew/grh/)). With that proof, every row
below is a theorem that Lean checks end to end from its three standard axioms, plus the
finite computations each row names. These statements were open before that proof. Rows 1 to 6 are named conjectures: Erdős 985,
the Lindelöf hypothesis, the density hypothesis, Grosswald's conjecture, the completeness of
Euler's list of idoneal numbers, and the extended Riemann hypothesis for abelian number fields.
Rows 7 to 11 are statements known to be equivalent to RH. Rows 12 to 17 are further
theorems under RH or GRH; rows 12 to 15 carry the papers' own constants. Three rows concern
Erdős problems: 985 in full, part (iii) of 770, and the RH bounds toward 233.

What this workspace contributes is the Lean proofs themselves. Each implication "RH implies X"
was proved here in full, with explicit constants where the papers leave them implicit, in
places with lemmas the papers state without proof, and with proved-sound checkers for every
finite range.
The conditional theorems are due to the authors in the last column, and the proof of RH is
Alpöge's. [`AGENTS.md`](AGENTS.md) holds the status checklist, the proof-tier rules and the README
rules; attributions are in [`docs/LITERATURE_STATUS.md`](docs/LITERATURE_STATUS.md).

## Abstract

Living Brain and OpenHuman collaborated on a formal mathematics programme
following Levent Alpöge’s Lean proof of RH and Dirichlet GRH. OpenHuman’s agents
and the RSI Ralph recursive self-improvement loop developed 17 machine-checked
results. Living Brain provided persistent, source-linked research memory that
helped identify consequences within scope, retrieve literature and dependencies,
and record why other approaches were set aside. Lean checked the proofs. The
collaboration demonstrated memory-assisted target selection. The effect of
individual memory scores and Brain Health on proof outcomes remains unmeasured
in this account.

## TL;DR

Living Brain carried research context across sessions. OpenHuman’s agents and
RSI Ralph developed the downstream proofs, and Lean checked them using Alpöge’s
formalisation to discharge RH or GRH.

| Total projects | Named conjectures and RH-equivalent statements | Further consequences of RH or GRH |
| :---: | :---: | :---: |
| **17** | **11** | **6** |

The six further consequences include four projects that formalise published
bounds with their original constants, a proof of part (iii) of Erdős 770, and
an upper bound toward Erdős 233. The remaining parts of Erdős 770 and the full
Erdős 233 problem remain open.

Several of the questions go back generations. The Lindelöf hypothesis dates to
1908, and the question of whether Euler’s 65 idoneal numbers exhaust the list
goes back to his eighteenth-century work. RH itself dates to 1859.

[Results](#results) · [How it worked](#how-it-worked) · [Build and verification](#build-and-verification) · [Licence](#licence)

## Results

The projects cover six named conjectures, five statements known to be equivalent
to RH, and six further consequences. For the RH-equivalent statements, the table
describes the direction formalised in this collection. Erdős 770 parts (i) and
(ii) remain open, as does the full Erdős 233 problem.

### Six named conjectures

| # | Submodule | Result | Tier | In the literature |
|---|---|---|---|---|
| 1 | [erdos-985](erdos-985/) | every odd prime has a prime primitive root `q < p` | U | RH-consequence (McGown–Treviño–Trudgian 2016) |
| 2 | [lindelof-rh](lindelof-rh/) | Lindelöf hypothesis for ζ and for Dirichlet L-functions | U | RH-consequence |
| 3 | [density-rh](density-rh/) | density hypothesis for ζ; zero counting `N(T) ≪ T log T` (the latter with no hypothesis) | U (library D) | RH-consequence; the zero count is known |
| 4 | [grosswald-grh](grosswald-grh/) | Grosswald's conjecture: every prime `p > 409` has least primitive root `g(p) < √p − 2` | U | RH-consequence |
| 5 | [weinberger-grh](weinberger-grh/) | Euler's 65 idoneal numbers are the only ones | U | RH-consequence |
| 6 | [abelian-erh](abelian-erh/) | ERH for every finite abelian extension of ℚ (Kronecker–Weber taken from riemann-hypothesis) | U | RH-consequence |

### Five statements equivalent to RH

| # | Submodule | Result | Tier | In the literature |
|---|---|---|---|---|
| 7 | [robin-rh](robin-rh/) | Robin's inequality for every `n > 5040`, and Lagarias's form | U (624 `native_decide` for the finite range) | RH-equivalent |
| 8 | [nicolas-rh](nicolas-rh/) | Nicolas' inequality `N_k/φ(N_k) > e^γ log log N_k` for every primorial | U | RH-equivalent |
| 9 | [li-criterion-rh](li-criterion-rh/) | Li's criterion, positivity direction: `λ_n > 0` for `n ≥ 1` | U | RH-equivalent |
| 10 | [speiser-rh](speiser-rh/) | `ζ'(s) ≠ 0` for `0 < Re s < 1/2` (the band between heights `5/2` and `7` by a verified computation, 2 `native_decide`) | U | RH-equivalent |
| 11 | [mertens-rh](mertens-rh/) | `M(x) = O(x^{1/2+ε})`; Titchmarsh's `\|M(x)\| ≤ √x·exp(25 log x/log log x)`, the same for Liouville's `L(x)`, and `1/\|ζ\|` on `σ ≥ 1/2 + 1/log log t`; Riesz, Hardy–Littlewood; convergence of `Σ μ(n)n^{-s}`; Liouville `L(x)`; Franel–Landau; `det R_n = M(n)` | U (Redheffer's identity D) | RH-equivalent (the identity is known) |

### Six further consequences of RH or GRH

| # | Submodule | Result | Tier | In the literature |
|---|---|---|---|---|
| 12 | [lls-grh](lls-grh/) | Every theorem of Lamzouri–Li–Soundararajan with the paper's constants: the least prime in a coset of a subgroup of index `h` is `≤ 10^9` or `≤ ((h−1) log q + 3(h+1) + (5/2)(log log q)²)²` (Thm 1.4); the least prime outside a proper subgroup of `(ℤ/q)ˣ` is `≤ (log q + B(q))²` for `q ≥ 3000` (Thm 1.1); least quadratic non-residue `≤ (log q)²` for prime `q ≥ 5` (Cor 1.2); `\|L(1,χ)\| ≤ 2e^γ(log log q − log 2 + 1/2 + 1/log log q)` and the matching lower bound (Thm 1.5) and class-number bounds (Cor 1.3) for `q ≥ 10^10`; Bach's bound with Bach's own constant `2`, and deterministic Miller with `2` | U | RH-consequence |
| 13 | [bach-sorenson-grh](bach-sorenson-grh/) | least prime `p ≡ a (mod q)` is `< 2(q log q)²` (Bach–Sorenson's own constant) | U | RH-consequence |
| 14 | [schoenfeld-rh](schoenfeld-rh/) | Schoenfeld's bounds with his constant: `\|ψ(x) − x\| < √x log² x / (8π)` (`x ≥ 73.2`), the same for θ (`x ≥ 599`), and `\|π(x) − li(x)\| < √x log x / (8π)` (`x ≥ 2657`) | U | RH-consequence |
| 15 | [cramer-rh](cramer-rh/) | a prime in `[x, x + (22/25)√x log x]` for every `x ≥ 4` (Cramér's gap bound with the literature's constant `22/25`, Carneiro–Milinovich–Soundararajan); Cramér's mean square `∫_X^{2X} (ψ(x) − x)² dx ≪ X²` and its asymptotic `∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X` | U | RH-consequence |
| 16 | [erdos-770](erdos-770/) | Erdős 770(iii): `h(n) ≤ max(P(n), ⌈200 log² n⌉)` for every `n ≥ 2` (parts (i) and (ii) stay open) | U | RH-consequence |
| 17 | [erdos-233](erdos-233/) | `Σ_{n<N} (p_{n+1} − p_n)² = O(N log⁴ N)` (the RH upper bound; Erdős 233 itself stays open); Selberg's theorem that almost all intervals `(x, x + h(x)]` with `h(x)/log² x → ∞` contain a prime, and `π(x+h) − π(x) ~ h/log x` for almost all `x` | U | RH-consequence |

**Proof tiers.** **D** is a direct proof without RH or GRH. **C** leaves RH or
GRH as an explicit hypothesis. **U** discharges RH or GRH with the upstream
proof. **U₀** uses a lemma from the upstream repository that is independent of
RH or GRH. **H** marks a cited result supplied as an explicit hypothesis.
See the full tier rules and per-theorem axiom counts in [AGENTS.md](AGENTS.md).


## Further projects

These folders are not among the 17 results above. Some are dependencies of those results, and the
others were started beside them. Each folder's README gives its tier, its axioms and its status
in the literature.

| Folder | Content |
|---|---|
| [ankeny-grh](ankeny-grh/) | Bach's explicit Ankeny theorem under GRH; bach-sorenson-grh, erdos-770, lls-grh and miller-grh require it |
| [miller-grh](miller-grh/) | Deterministic Miller–Rabin under GRH; lls-grh requires it |
| [littlewood-rh](littlewood-rh/) | Littlewood's bound for ζ(1/2 + it) under RH; mertens-rh requires it |
| [artin-grh](artin-grh/) | Artin's primitive root conjecture under Hooley's hypothesis; abelian-erh requires it |
| [shoup-grh](shoup-grh/) | The least primitive root `g(p) ≪ ω(p−1)^{21/5} log² p` under GRH |
| [psi-grh](psi-grh/) | Primes in arithmetic progressions under GRH |
| [erdos-969](erdos-969/) | Montgomery–Vaughan's bound for squarefree and k-free numbers under RH |
| [goldbach-average-rh](goldbach-average-rh/) | Fujii's average Goldbach bound under RH |
| [mills-rh](mills-rh/) | Mills' constant to 87 decimals under RH |
| [goldbach-grh](goldbach-grh/) | Ternary Goldbach under GRH (proved without GRH by Helfgott 2013; wound down) |
| [hironaka-fc](hironaka-fc/) | Hironaka's resolution of singularities in characteristic 0 |

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

## Results

| # | Submodule | Result | Tier | In the literature |
|---|---|---|---|---|
| 1 | [erdos-985](erdos-985/) | every odd prime has a prime primitive root `q < p` | U | RH-consequence (McGown–Treviño–Trudgian 2016) |
| 2 | [lindelof-rh](lindelof-rh/) | Lindelöf hypothesis for ζ and for Dirichlet L-functions | U | RH-consequence |
| 3 | [density-rh](density-rh/) | density hypothesis for ζ; zero counting `N(T) ≪ T log T` (the latter with no hypothesis) | U (library D) | RH-consequence; the zero count is known |
| 4 | [grosswald-grh](grosswald-grh/) | Grosswald's conjecture: every prime `p > 409` has least primitive root `g(p) < √p − 2` | U | RH-consequence |
| 5 | [weinberger-grh](weinberger-grh/) | Euler's 65 idoneal numbers are the only ones | U | RH-consequence |
| 6 | [abelian-erh](abelian-erh/) | ERH for every finite abelian extension of ℚ (Kronecker–Weber taken from riemann-hypothesis) | U | RH-consequence |
| 7 | [robin-rh](robin-rh/) | Robin's inequality for every `n > 5040`, and Lagarias's form | U (624 `native_decide` for the finite range) | RH-equivalent |
| 8 | [nicolas-rh](nicolas-rh/) | Nicolas' inequality `N_k/φ(N_k) > e^γ log log N_k` for every primorial | U | RH-equivalent |
| 9 | [li-criterion-rh](li-criterion-rh/) | Li's criterion, positivity direction: `λ_n > 0` for `n ≥ 1` | U | RH-equivalent |
| 10 | [speiser-rh](speiser-rh/) | `ζ'(s) ≠ 0` for `0 < Re s < 1/2` (the band between heights `5/2` and `7` by a verified computation, 2 `native_decide`) | U | RH-equivalent |
| 11 | [mertens-rh](mertens-rh/) | `M(x) = O(x^{1/2+ε})`; Titchmarsh's `\|M(x)\| ≤ √x·exp(25 log x/log log x)`, the same for Liouville's `L(x)`, and `1/\|ζ\|` on `σ ≥ 1/2 + 1/log log t`; Riesz, Hardy–Littlewood; convergence of `Σ μ(n)n^{-s}`; Liouville `L(x)`; Franel–Landau; `det R_n = M(n)` | U (Redheffer's identity D) | RH-equivalent (the identity is known) |
| 12 | [lls-grh](lls-grh/) | Every theorem of Lamzouri–Li–Soundararajan with the paper's constants: the least prime in a coset of a subgroup of index `h` is `≤ 10^9` or `≤ ((h−1) log q + 3(h+1) + (5/2)(log log q)²)²` (Thm 1.4); the least prime outside a proper subgroup of `(ℤ/q)ˣ` is `≤ (log q + B(q))²` for `q ≥ 3000` (Thm 1.1); least quadratic non-residue `≤ (log q)²` for prime `q ≥ 5` (Cor 1.2); `\|L(1,χ)\| ≤ 2e^γ(log log q − log 2 + 1/2 + 1/log log q)` and the matching lower bound (Thm 1.5) and class-number bounds (Cor 1.3) for `q ≥ 10^10`; Bach's bound with Bach's own constant `2`, and deterministic Miller with `2` | U | RH-consequence |
| 13 | [bach-sorenson-grh](bach-sorenson-grh/) | least prime `p ≡ a (mod q)` is `< 2(q log q)²` (Bach–Sorenson's own constant) | U | RH-consequence |
| 14 | [schoenfeld-rh](schoenfeld-rh/) | Schoenfeld's bounds with his constant: `\|ψ(x) − x\| < √x log² x / (8π)` (`x ≥ 73.2`), the same for θ (`x ≥ 599`), and `\|π(x) − li(x)\| < √x log x / (8π)` (`x ≥ 2657`) | U | RH-consequence |
| 15 | [cramer-rh](cramer-rh/) | a prime in `[x, x + (22/25)√x log x]` for every `x ≥ 4` (Cramér's gap bound with the literature's constant `22/25`, Carneiro–Milinovich–Soundararajan); Cramér's mean square `∫_X^{2X} (ψ(x) − x)² dx ≪ X²` and its asymptotic `∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X` | U | RH-consequence |
| 16 | [erdos-770](erdos-770/) | Erdős 770(iii): `h(n) ≤ max(P(n), ⌈200 log² n⌉)` for every `n ≥ 2` (parts (i) and (ii) stay open) | U | RH-consequence |
| 17 | [erdos-233](erdos-233/) | `Σ_{n<N} (p_{n+1} − p_n)² = O(N log⁴ N)` (the RH upper bound; Erdős 233 itself stays open); Selberg's theorem that almost all intervals `(x, x + h(x)]` with `h(x)/log² x → ∞` contain a prime, and `π(x+h) − π(x) ~ h/log x` for almost all `x` | U | RH-consequence |

Every row was rebuilt and checked on 2026-11-24 or 2026-11-25 against riemann-hypothesis
`507a75d91d`, the community repository's `main` (the certified release is its commit `40e56bab`,
since moved to Lean v4.36.0). Our check links against the community build cache; it does
not repeat the kernel checks cited above.

Tiers: **D** proved directly, with no use of RH. **U** proved unconditionally, with RH or GRH
supplied by [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
**C** conditional on RH or GRH. **H** a cited result taken as a hypothesis. See `AGENTS.md`.

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
