# Next targets

Working notes, 2026-11-24, on which RH/GRH consequences to formalise next. Tiers (D, U, C, H)
and the rules they refer to are defined in [`AGENTS.md`](../AGENTS.md). Status of the existing
seven repos lives in `AGENTS.md`, not here.

Every target follows a published theorem, proved outright or assuming RH/GRH; the Lean proof is
what gets built here. [`LITERATURE_STATUS.md`](LITERATURE_STATUS.md) labels each one (known; known, via GRH
here; RH-consequence; RH-equivalent) and says how to describe it.

## Scope widened, 2026-11-26

Targets are no longer limited to RH and GRH consequences: any open conjecture qualifies when it
can be settled by connecting existing results (see `AGENTS.md`, "Scope" and "Mine the lemmas of
big proofs"). The rounds below were all run under the older RH/GRH filter.

## Avoid what 1337isnot1337/solved-conjectures already covers

**Decided 2026-11-26.** Before a target is started, check
[1337isnot1337/solved-conjectures](https://github.com/1337isnot1337/solved-conjectures)
(`CONTENTS.md` on `main`, and `research/rh-transfer/` on its `research` branch). A conjecture that repository lists as settled
is not a new target here.

Checked against its `main` at `60e47a0` and its `research` branch on 2026-11-26. Its RH-transfer
inventory gives written deductions, with no Lean, for four of our projects: Robin's conjecture
(robin-rh), Nicolas's conjecture (nicolas-rh), Grosswald's conjecture (grosswald-grh) and the
Lindelöf hypothesis (lindelof-rh). It excludes the idoneal-number classification (weinberger-grh)
as an already published application, and it lists Artin's conjecture and Goldbach as unresolved. Its
"Li" entries concern Ethan Li's chromatic symmetric functions and the Keiper and
Chaudhary–Khmiri–Mazhouda Li-coefficient conjectures, not Li's criterion (li-criterion-rh). None of
our other 23 projects, nor Erdős 985, 770, 233 or 969, appear there.

## Open problems only

**Decided 2026-11-24: a target must be open in the literature.** Its unconditional statement has
no published proof, so its label in [`LITERATURE_STATUS.md`](LITERATURE_STATUS.md) is
*RH-consequence* or *RH-equivalent*. Theorems already proved without RH (labels *known* and
*known, via GRH here*) are not targets, however famous, and were removed from this file that
day; the list is under "Removed: already theorems" near the end. hironaka-fc was finished before
the decision and stays as a repo.

## The test a candidate has to pass

[riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) proves exactly
two things: `riemannHypothesis : RiemannHypothesis` (ζ) and
`LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` (Dirichlet L-functions).
It says nothing about Dedekind zeta functions of non-abelian fields, Hecke L-functions or
elliptic-curve L-functions.

So a result can reach tier U only if its analytic input is RH for ζ or GRH for Dirichlet L, and
any finite range left below the analytic threshold fits in `native_decide` with a proved-sound
checker. Anything else stays C or H at best. That is the filter applied below.

## Ranked candidates

| # | Target | Analytic input | Expected tier | Reuses |
|---|---|---|---|---|
| 1 | Euler's idoneal numbers under GRH (Weinberger 1973) | GRH, real characters | U | erdos-985 zero sums |
| 2 | von Koch / Schoenfeld bound for `π(x) − li(x)` under RH | RH | U, if the small range fits | erdos-985 explicit formula, robin-rh `Robin/RH/` |
| 3 | Least prime in an arithmetic progression under GRH (Bach–Sorenson 1996) | GRH | U | ankeny-grh, miller-grh |
| 4 | Lindelöf for Dirichlet L-functions under GRH | GRH | U | lindelof-rh blueprint (statement already stubbed) |
| 5 | Cramér's prime-gap theorem under RH (1920) | RH | U | #2 |

### 1. Idoneal numbers (Weinberger)

Euler's 65 idoneal numbers are known to be the complete list under GRH. Unconditionally,
Weinberger's 1973 results leave room for at most two more. Some sources say "at most one",
which is wrong. The unconditional question is still open, so a tier-U proof would
be a formal result about an open problem, not just a re-proof. Class number one for imaginary
quadratic fields (`h(−d) = 1` exactly for the nine Heegner discriminants) runs on the same
machinery and comes almost for free:

1. A GRH lower bound for `L(1, χ_d)`, from erdos-985's zero-sum toolkit.
2. The class number formula `h(−d) = w √d · L(1, χ_d) / (2π)`.
3. Genus theory. An idoneal discriminant has a class group of exponent at most 2, so
   `h = 2^(t−1)`, where `t` is the number of prime factors of the discriminant.
4. Steps 1–3 make `h` too large for every discriminant beyond an explicit bound. A finite
   `native_decide` check covers the rest.

**Main cost:** Mathlib's support for class groups of binary quadratic forms and for genus
theory is thin. Scope that before writing any proof: check that steps 2 and 3 can be *stated*
against the Mathlib pin. If they can't, this becomes a Mathlib project first.

Statement source: check formal-conjectures for an idoneal statement to copy verbatim (rule 3).
The Conjecture Atlas carries the rows `wiki-idoneal-number` and `wiki-class-number-problem`.

### 2. von Koch / Schoenfeld under RH

Schoenfeld (1976): under RH, `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`, and a
companion bound holds for `ψ(x)`. Very well known, and needs RH for ζ only. erdos-985's
weighted explicit formula and robin-rh's `Robin/RH/Bach.lean` and `Robin/RH/Psi1.lean` already
do most of the analytic work. The risk is bookkeeping the explicit constants. The range just
above 2657 may need a direct computation, which decides whether it is U or U + H.

### 3. Least prime in an arithmetic progression (Bach–Sorenson)

Under GRH, the least prime `p ≡ a (mod q)` satisfies `p ≤ 2 (q log q)²` (Bach–Sorenson 1996;
Lamzouri–Li–Soundararajan sharpen it). This is the GRH form of Linnik's problem. The machinery
is almost identical to ankeny-grh's subgroup bound, so expect a weaker constant first, as with
ankeny's `21/5`. Record any deviation in the README (rule 3).

### 4. Dirichlet-L Lindelöf

`dirichletLindelof_of_GRH` already exists in `lindelof-rh/Lindelof/Dirichlet.lean`, with its
proof left as `sorry`. The `AGENTS.md` checklist gives the plan: steps 1–8 of
`lindelof-rh/docs/BLUEPRINT.md`, with `ξ` replaced by the completed L-function of the inducing
primitive character. This is the quickest win here.

### 5. Cramér's prime-gap theorem

Cramér (1920): under RH, `p_{n+1} − p_n = O(√p_n log p_n)`. This is his *theorem*, not his
conjecture (gaps `≪ log² p`), which is rejected below. It follows naturally from #2. An explicit
version (Carneiro–Milinovich–Soundararajan 2019, `p_{n+1} − p_n < (22/25) √p_n log p_n` for
`p_n > 3`) would make a better headline than a bare `O(·)`.

## Round 2 (2026-11-24): revisions to the list above

A second research pass, filtered the same way, changed four things:

- **#2 von Koch / Schoenfeld moves to the front.** Mills (#7) and Nicolas (#11) are built on it.
- **#5 Cramér folds into #2.** Dudek ([arXiv:1402.6417](https://arxiv.org/abs/1402.6417), Thm 2):
  under RH there is a prime in `(x − (4/π)√x log x, x]` for `x ≥ 2`, which follows almost directly
  from the explicit `π(x) − li(x)` bound.
- **#3: target Lamzouri–Li–Soundararajan, not Bach–Sorenson.** LLS (Math. Comp. 84 (2015),
  [arXiv:1309.3595](https://arxiv.org/abs/1309.3595)) Cor 1.2 gives `P(a,q) ≤ (φ(q) log q)²` for
  `q > 3`, which is stronger.
- **#1 Weinberger: a cheaper finite check.** If `h(−q) = 1`, every prime below `q/4` is inert, and
  LLS Thm 1.4 bounds the least split prime, which caps `q`. LLS also gives `h(−q) ≥ 9053` for
  `q ≥ 10^11` under GRH.

## Round 2: new candidates

| # | Target | Input | formal-conjectures statement | Expected tier | Effort |
|---|---|---|---|---|---|
| 7 | Mills' constant: `A ∈ (1.3063778838, 1.3063778839)` | RH | `Wikipedia/Mills.lean`, `Mills.lower_bound_of_RH` | U | S, after #2 |
| 8 | Density hypothesis | RH | `Wikipedia/DensityHypothesis.lean`, **research open** | U | S–M |
| 9 | Li's criterion, RH ⇒ `λ_n > 0` | RH | `Paper/RiemannHypothesisEquivalents.lean`, `li_criterion_rhs`, **research open** | U | M |
| 10 | Mertens `M(x) = O(x^{1/2+ε})`, with Redheffer and Franel–Landau as corollaries | RH | none | U | M–L |
| 11 | Nicolas' criterion (the φ version of Robin) | RH | none | U, if the small range fits | M–L |
| 12 | LLS upgrade of ankeny-grh / miller-grh (constant near 1 instead of `21/5`) | GRH | none | U | M |
| 13 | Explicit Littlewood bounds for `L(1,χ)` and class numbers | GRH | none | U | M–L |
| 14 | Erdős 233, upper bound: `Σ_{n<N} gap_n² = O(N log⁴ N)` | RH | `ErdosProblems/233.lean`, `erdos_233.variants.upper_bound` | U | L |
| 15 | Littlewood's bound `log ζ(1/2+it) ≪ log t / log log t` | RH | none | U | M |
| 16 | Riesz and Hardy–Littlewood criteria | RH | none | U | S–M, after #10 |

Statements the research could not confirm against the primary source are marked *(unverified)*.
Check them before fixing a `Statement.lean`.

### 7. Mills' constant

Caldwell–Cheng, J. Integer Seq. 8 (2005), Art. 05.4.1, Thm 1, through Lemma 5: under RH there is
a prime between `x³` and `(x+1)³`, via Schoenfeld's bound for `x ≥ 2657`, i.e. #2. The lower bound
needs no RH: `q_n ≥ P_n` for the greedy sequence 2, 11, 1361, 2521008887. The upper bound needs
the greedy limit to be a Mills number, which is where primes between cubes come in.
`P₄^{1/81} = 1.30637788386308…` and `(P₄+1)^{1/81} = 1.30637788386947…` both lie inside the
target interval. The finite work is one primality certificate, six compositeness checks and two
rational 81st-power comparisons, all within `norm_num` / `decide` range. Wikipedia-level, with a
ready statement.

### 8. Density hypothesis

Under RH, `N(σ,T) = 0` for `σ > 1/2`. At `σ = 1/2` only `N(T) ≪ T log T` is needed (Riemann–von
Mangoldt; Titchmarsh ch. 9 *(section unverified)*). It reuses erdos-985's `XiGrowth` with
Mathlib's Jensen formula (`Analysis/Complex/JensenFormula.lean`). formal-conjectures'
`zeroCountOn` counts multiplicity, which Jensen handles. The zero-counting lemma is shared with
#9 and #14, so build it once as a library.

### 9. Li's criterion (RH ⇒ positivity)

Li, J. Number Theory 65 (1997) 325–333; Bombieri–Lagarias, JNT 77 (1999) 274–287. Under RH,
`|1 − 1/ρ| = 1`, so each term is `2(1 − cos nθ_ρ) ≥ 0`. Missing: summability from
`Σ 1/|ρ|² < ∞`, and, for strict positivity, infinitely many zeros. Mathlib has no theorem that
ζ has any zero; erdos-985's Hadamard factorisation plus the Γ growth of `ξ` supplies one.
formal-conjectures' `lambda` sums over a set, ignoring multiplicity, which is harmless here.

### 10. Mertens function

Littlewood, C. R. Acad. Sci. 154 (1912) 263–266 *(attribution from surveys)*. Redheffer's
`det R_n = M(n)` *(1977; venue unverified)* and Franel–Landau (Gött. Nachr. 1924) come almost
free afterwards. Needs `1/ζ ≪ |t|^ε` on `σ ≥ 1/2 + δ`, which lindelof-rh's log-ζ /
Borel–Carathéodory work should reach, and a **sharp-cutoff Perron formula**, which Mathlib
lacks. erdos-985's smoothed Perron stops at `x^{3/4+ε}`, the same barrier robin-rh hit with `ψ`.
This is the most famous RH equivalence on the list.

### 11. Nicolas' criterion

`N_k/φ(N_k) > e^γ log log N_k` for every primorial `N_k` (Nicolas, JNT 17 (1983) 375–388
*(theorem number unverified)*; restated in Acta Arith. 155 (2012)). Uses Schoenfeld's
`|θ(x) − x| ≤ √x log²x/(8π)` for `x ≥ 599`, `θ(x) < x` below `8·10^11`, and
`Σ 1/(ρ(1−ρ)) = 2 + γ − log 4π`. Reuses robin-rh's Mertens estimates and #2. The size of the
finite check is not yet established; probably `≤ 10^8`.

### 12. LLS upgrade of ankeny-grh and miller-grh

LLS Thm 1.1: for `q ≥ 3000`, the least prime `ℓ ∤ q` outside a proper subgroup is
`≤ (log q + B(q))²`. Thm 1.4 (`q ≥ 20000`) handles cosets, including the least prime quadratic
residue. This replaces ankeny-grh's `21/5`, which is weaker than Bach's own `2`, with a constant
near 1. The `q < 3000` check is trivial. Deterministic Tonelli–Shanks (polynomial-time square
roots mod `p` under GRH) is a free corollary.

### 13. Explicit `L(1,χ)` and class-number bounds

LLS Thm 1.5 and Cor 1.3, for `q ≥ 10^10`: `|L(1,χ)| ≤ 2e^γ(log log q − log 2 + 1/2 + 1/log log q)`,
a matching lower bound, and `h(−q) ≥ (π/(12e^γ)) √q / (log log q + …)`. Also an input to #1.

### 14. Erdős 233 (upper bound)

Selberg, Arch. Math. Naturvid. 47 (1943): the mean-square lemma
`∫|θ(y+δy) − θ(y) − δy|² ≪ δx² log² x` is confirmed. The exact `Σ d_n²` form, and
formal-conjectures' attribution to Cramér, are *unverified*. Explicit version: Cully-Hugill–Dudek,
[arXiv:2206.00433](https://arxiv.org/abs/2206.00433). Needs a Gallagher/Plancherel mean-value
lemma and #8's zero counting.

### 15. Littlewood's strong Lindelöf bound

`log|ζ(1/2+it)| ≤ C log t / log log t`. Littlewood 1924 gives an unspecified `C`
*(Titchmarsh §14.14, unverified)*, which is the realistic target and extends lindelof-rh. The
sharp `(log 2)/2 + o(1)` is Chandee–Soundararajan, Bull. LMS 43 (2011), Thm 1.1 (effort L).

### 16. Riesz and Hardy–Littlewood criteria

Under RH, the Riesz function is `O(x^{1/4+ε})` (Riesz, Acta Math. 40 (1916)), and
`Σ μ(n)/n · e^{−x/n²} = O(x^{−1/4+ε})` (Hardy–Littlewood, Acta Math. 41 (1916)). Both are
Mellin–Barnes contour shifts once #10's `1/ζ` bound exists. They are smoothed by nature, so no
sharp-cutoff Perron is needed.

## Round 3 (2026-11-24): what riemann-hypothesis proves along the way

Rounds 1 and 2 treated riemann-hypothesis as two theorems. Round 3 read the whole repo and
inventoried its intermediate lemmas in [`rh-lemmas/`](rh-lemmas/README.md). Three follow-up
reports matched those lemmas against the Conjecture Atlas and formal-conjectures:
[analytic](rh-lemmas/targets-analytic.md), [algebraic](rh-lemmas/targets-algebraic.md) and
[geometry and algebra](rh-lemmas/targets-geometry-algebra.md). They hold the declaration names,
paths and the full reasoning for every row below.

All of it was read from statements. Nothing was built, and no `#print axioms` was run. The
first step on any target here is to import the one module it needs and check the statement and
its axioms. artin-grh PR #11 shows that works: importing a single `GroundTheory` module took
17 s and 6.6 GB of RAM, not the 93 GB / 19 GB of the full import.

### The filter changes

The round 1 test was "the analytic input is RH for ζ or GRH for Dirichlet L". The repo also
proves, with no hypothesis, Siegel–Walfisz, Linnik, Brun–Titchmarsh, the large sieve, a
truncated explicit formula, global class field theory, Chebotarev density, the continuation of
`dedekindZeta`, and Hironaka in characteristic 0. So a target can now also qualify because its
missing input is one of those.

**Tier U₀.** A theorem that imports riemann-hypothesis for one of those lemmas and never uses
RH is tier **U₀** (defined in `AGENTS.md`). After the open-problems-only decision above, no
remaining target is U₀: a statement provable from those lemmas alone is already a theorem. The
lemmas still matter as inputs to RH-conditional targets.

### Build once: the GRH `ψ(x,χ)` bound

Under GRH, `|ψ(u,χ) − δ_χ u| ≤ C √u log²(qu)`, uniformly in the modulus `q`. The cheaper forms of #2, #5 and #8 reduce to it. Its constant is existential, so it
helps `O(·)` statements and does nothing for targets that end in a finite check. Brief H0 below.

### New candidates

| # | Target | Input from riemann-hypothesis | formal-conjectures statement | Tier | Effort |
|---|---|---|---|---|---|
| H0 | The GRH `ψ(x,χ)` bound (shared library) | GRH, truncated explicit formula, zero counts | none | U | S–M |
| 24 | ERH for every abelian number field | RH, GRH, Kronecker–Weber, `dedekindZeta` continuation | none (formal-conjectures has `DedekindZetaRH` vocabulary only) | U | M–L |

The briefs below carry everything the three reports found. Paths are relative to
`riemann-hypothesis/src/` at `507a75d91d`. "Opened" means an agent read that Lean statement;
"inventory" means it is known only from the inventory tables. Every declaration name must be
confirmed with `#check` before anything is built on it.

### How to run a target

This is the same for every brief, so it is written once.

1. **Read first.** `AGENTS.md` (tiers, rules 1–7, README rules), this brief, the inventory file
   the brief cites, and LivingBrain for the target's name (dead ends and constants are there).
2. **Create the repo.** `senamakel/<slug>`, Lean `v4.36.0`, Mathlib `fc4f59e5`, requiring
   erdos-985 at `9538edb` over HTTPS (rule 7). riemann-hypothesis is on the same toolchain and
   Mathlib pin, so its modules import directly. Add the repo as a submodule here, give it a row
   in `README.md` and a section in the `AGENTS.md` checklist.
3. **Fix the statement.** Put the target in `<Pkg>/Statement.lean`. If formal-conjectures has
   it, copy it word for word and link it (rule 3). Don't edit it later to make a proof go
   through; if you prove something weaker, state the weaker theorem and say why in the README.
4. **Smoke-test every imported lemma before building on it.** Write a scratch file that imports
   the one module, `#check`s the declaration and runs `#print axioms` on it. Compile it the way
   `erdos-985/scripts/check-unconditional.sh` does: `LEAN_PATH` from `lake env printenv
   LEAN_PATH` in the riemann-hypothesis checkout, then `lean <file>`. A single `GroundTheory`
   module cost 17 s and 6.6 GB of RAM in artin-grh PR #11; the full `Main` import costs 93 GB
   of cache and 19 GB of RAM. If the axiom list has anything beyond `propext`,
   `Classical.choice` and `Quot.sound`, stop and record it.
5. **Check the definitions, not only the statement.** For each imported lemma that mentions a
   repo-internal definition (`IsKroneckerChar`, `psi0`, `IsBlowup`, `piMod`, …), open the
   definition and write a bridging lemma to the Mathlib object. Record anything degenerate.
6. **Keep the layering.** The main library never imports riemann-hypothesis (rule 1). An
   imported lemma enters the main library as an explicit `Prop` hypothesis whose definition is
   stated in Mathlib terms. `Unconditional/<X>Unconditional.lean` imports the repo and
   discharges each hypothesis in one line. For a U₀ target the hypotheses are the imported
   classical lemmas (Siegel–Walfisz, Linnik, …) instead of RH.
7. **No copying.** riemann-hypothesis has no licence: import it, never paste from it. The
   Apache-2.0 sources may be vendored with a NOTICE and a Credits section (README rule 11).
8. **Assemble first, then fan out.** Prove the top-level assembly from the stated steps with the
   steps as hypotheses, then give one step to each agent in its own worktree
   (`worktree <slug>` at the superproject level).
9. **Finish.** Paste real `#print axioms` output into the README, add
   `scripts/check-unconditional.sh`, tick the checklist in `AGENTS.md`, bump the gitlink, and
   write to LivingBrain whatever git won't hold: an approach that failed, a constant you sized.

### H0. The GRH `ψ(x,χ)` bound (shared library for #2, #5, #8)

- **Statement to prove.** Under `hGRH : DirichletLNonvanishingRightOfHalf`: there is `C > 0`
  such that for every `N` with `[NeZero N]`, every Dirichlet character `χ` mod `N` and every
  `u ≥ 2`, `|ψ(u,χ) − δ_χ·u| ≤ C·√u·log²(N·u)`, where `ψ(u,χ) = Σ_{n≤u} Λ(n)χ(n)` and
  `δ_χ = 1` for the principal character, `0` otherwise. `N = 1` gives ζ.
- **Where it lives.** A new module in erdos-985 (the analytic toolkit root), or a small new
  repo `grh-psi` required by the targets that use it. Decide before starting; erdos-985 is
  preferred because every sibling already requires it.
- **Inputs (both opened).**
  - `GlobalTheory.ExplicitFormula.truncated_explicit_formula`,
    `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean:16`.
    Shape: `∃ C > 0, ∀ N [NeZero N] χ, χ.IsPrimitive → …`, uniform in `N`, `χ`, `T` and `u`.
    Its `psi0` is `Σ_{n ≤ ⌊u⌋} Λχ − [N=1]·u`. It carries an extra term
    `Σ_{|Im ρ|<1} m_ρ/‖ρ‖`.
  - `GlobalTheory.ZeroWindow.count_zeros_window`,
    `…/GlobalInterpolation/FinsumMemLeOfSubset.lean:31`. Zeros in a unit window number at most
    `C·log(N(|t|+2))`, counted with multiplicity through `analyticOrderNatAt`, uniformly in the
    conductor.
  - `Claim.prim_zero` and `UpperTheory.Top.imprimitive`
    (`Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`, `Imprimitive.lean`)
    for the reduction to primitive characters.
- **Steps.**
  1. Under GRH every nontrivial zero has `Re ρ = 1/2`, so `|u^ρ/ρ| = √u/|ρ|` and `|ρ| ≥ 1/2`.
     The extra term is then at most `C·log 2N` by the window count.
  2. Sum `√u/|ρ|` over `|Im ρ| ≤ T` using the window count: `≪ √u·log T·log(NT)`.
  3. Take `T = u` (or `√u`); the truncation error in the formula becomes `≪ log²(Nu)`.
  4. Imprimitive `χ` mod `N` induced by primitive `χ*`: the two `ψ` differ only at prime powers
     of primes dividing `N`, a difference of at most `log N·log u`.
- **Missing.** Only the bookkeeping above. No new analysis.
- **Risks.** The constant is existential, so this library serves `O(·)` targets only. The
  explicit formula's exact error term and its range of `T` were read, not typechecked: confirm
  them in step 4 of "How to run a target" before writing step 2.
- **Module cost.** `TruncatedExplicitFormula` has about 203 repo files in its import closure
  *(count from one agent, not rebuilt)*.
- **Tier.** The bound is tier C in the main library; its `Unconditional/` discharge is tier U.
- **Effort.** S–M.

### 1 (revised). Idoneal numbers by the split-prime route

- **Statement.** formal-conjectures `Wikipedia/IdonealCompleteness.lean`,
  `idoneal_numbers_completeness` (**research open**). formal-conjectures defines `IsIdoneal n`
  as "`n` is not `ab + bc + ca` with `0 < a < b < c`" (Rains' form, OEIS A000926). The converse,
  `knownIdonealNumbers_are_idoneal`, is already proved there. Atlas row `wiki-idoneal-number`.
- **Source.** Weinberger, Acta Arith. 22 (1973) 117–124; Kani, Ann. Sci. Math. Québec 35
  (2011), Cor. 23 and Remark 24. Unconditionally at most two more idoneal numbers exist, none
  below `7.75·10^19` (OEIS A000926), so a tier-U proof is a formal result on an open problem.
- **Repo.** `idoneal-grh`, requiring erdos-985 and ankeny-grh. **Tier** U. **Effort** M.
- **Step 1, the witness lemma (elementary, about ten lines).** Let `p` be an odd prime with
  `p ∤ n`, `−n` a square mod `p`, and `p² < n`. Then `n` is not idoneal.
  Proof: pick `x` with `x² ≡ −n (mod p)` and `0 < x < p/2`. Write `n + x² = p·m`. Put
  `a = x`, `b = p − x`, `c = m − x`. Then `(a+b)(a+c) = p·m = n + a²`, so `ab + bc + ca = n`.
  `a < b` because `x < p/2`. `b < c` because `m > n/p > p`. This derivation came from one
  agent and was re-checked by hand; it has not been checked in Lean.
- **Step 2, the analytic bound (the real work).** Under GRH, for `n` above an explicit
  threshold there is an odd prime `p ∤ n` with `χ_{−4n}(p) = 1` and `p ≤ c·log²(4n)`, with an
  explicit `c`. This is the coset form of ankeny-grh's `BachSubgroupBound`: weight `(1 + χ)`
  instead of the characters trivial on a subgroup. Reuse ankeny-grh's explicit formula and
  erdos-985's zero sums; expect a constant near ankeny's `21/5` at first. The repo's H0 inputs
  don't help, because their constants are existential.
- **Step 3, the finite range.** `p² < n` holds once `c²·log⁴(4n) < n`. For `c ≈ 4` that is
  `n` above roughly `10^6` *(order of magnitude from one agent; size it against the `c`
  actually proved before choosing the checker design)*. Below it, supply a witness `(a, b, c)`
  for every `n` not on the list of 65, checked with `native_decide` and a proved-sound checker
  (rule 5).
- **Do not use.** LLS Thm 1.4 (arXiv:1309.3595): its "either `p ≤ 10⁹` or …" escape clause
  pushes the finite range to about `10^18`. The class number formula and genus theory are not
  needed on this route; the repo's formula covers maximal orders only, and `−4n` is usually not
  fundamental.
- **Done when.** `idoneal_numbers_completeness_of_GRH` (C) and its one-line discharge (U), with
  the `native_decide` count and timing in the README.

### 24. ERH for every abelian number field

- **Statement.** New. Use formal-conjectures' `IsDedekindZeta` / `DedekindZetaRH` vocabulary
  (`Millennium/RiemannHypothesis.lean` leaves ERH unstated until a continuation of
  `dedekindZeta` exists): for `K/ℚ` abelian, every zero of `ζ_K` with `0 < Re s < 1` has
  `Re s = 1/2`.
- **Repo.** `abelian-erh`. **Tier** U. **Effort** M–L.
- **Inputs.**
  - `UpperTheory.V.CF.kwHom`,
    `Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/ClassFieldRamification/KwHom.lean:13`
    (opened): an abelian `K` embeds in `CyclotomicField N ℚ`. Also `kw`, `kwRam`.
  - `continuedDedekindZeta`, `continuedDedekindZeta_eq`, `completedDedekindZeta_one_sub`,
    `GroundTheory/GlobalFields/TateThesis/Dedekind{Zeta,}Continuation.lean` (opened).
  - `dedekindZeta_eq_exp`,
    `Development/WeilBound/…/ZetaEulerProducts/SummablePrimesRpow.lean:13` (inventory 05): the
    Euler product of `dedekindZeta`.
  - `LFunction_ne_zero_of_half_lt_re` and `riemannHypothesis`.
- **Steps.**
  1. Embed `K` in `ℚ(ζ_N)`. Let `X(K)` be the Dirichlet characters mod `N` trivial on
     `Gal(ℚ(ζ_N)/K)`, imprimitive ones allowed.
  2. For `Re s > 1`: `ζ_K(s) = E(s)·∏_{χ∈X(K)} L(s,χ)` with
     `E(s) = ∏_{p∣N} ∏_{𝔭∣p} (1 − N𝔭^{−s})^{−1}`. Only unramified `p` need an Euler-factor
     identity: Frobenius of `p` is `p`, and
     `∏_{𝔭∣p}(1 − N𝔭^{−s}) = ∏_χ (1 − χ(p)p^{−s})` by orthogonality. Working mod `N` with
     imprimitive characters avoids all conductor and inertia bookkeeping, because `E` is
     holomorphic and zero-free on `Re s > 0`.
  3. On `Re s > 1/2`, `s ≠ 1`: any `Z` with `IsDedekindZeta K Z` equals `E·∏L` by the identity
     theorem, hence is nonzero by GRH.
  4. On `0 < Re s < 1/2`: the functional equation, with the gamma factors nonzero.
- **Missing.** The Euler-factor identity, and "Frobenius at `p` is `p`" in `ℚ(ζ_N)`
  (`GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean` may have it; not opened).
- **What it does not unlock.** Checked case by case: Weinberger's Euclidean rings (Kummer
  fields of units, non-abelian), Bach's class-group generator bound (Hilbert class field,
  generalised dihedral over ℚ), Miller's real-cyclotomic class numbers (Odlyzko bounds on the
  Hilbert class field; confirmed from arXiv:1407.2373), Hooley (`k ≥ 3`). Its value is the
  headline and the factorisation lemma.

### Existing targets, re-costed

- **#2 von Koch and #5 Cramér.** The `O`-forms are now effort S from H0 at `N = 1`:
  `ψ(x) = x + O(√x·log² x)` and gaps `O(√p·log² p)`. The gap bound is one logarithm weaker than
  Cramér's `√p·log p`, which needs a smoothed formula; state it as a deviation (rule 3).
  Schoenfeld's explicit `√x·log x/(8π)` is unchanged at M–L and still needs erdos-985's
  explicit machinery, so **#7 Mills** is unchanged too.
- **#8 density hypothesis.** Effort S. `N(σ,T) = 0` for `σ > 1/2` under RH; at `σ = 1/2`,
  summing `count_zeros_window` over unit windows gives `N(T) ≪ T·log T` with multiplicity.
  formal-conjectures' `Wikipedia/DensityHypothesis.lean` uses `Complex.zeroCountOn`, which also
  counts multiplicity, so one bridging lemma from `analyticOrderNatAt` remains.
- **#9 Li's criterion.** `Σ 1/|ρ|² < ∞` now follows from the window count. Strict positivity
  still needs infinitely many zeros: Hadamard in erdos-985, or a lower bound for `N(T)`. M.
- **#10 Mertens function.** M, down from M–L. The recorded blocker was a sharp-cutoff Perron
  formula. `GlobalTheory.PerronKernel.truncated_perron_kernel`
  (`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean:351`,
  opened) is that kernel lemma, for `y > 0`, `y ≠ 1`, `c > 0`, `T ≥ 1`, with explicit constant
  3. Still to prove: `1/ζ ≪ |t|^ε` on `σ ≥ 1/2 + δ` under RH (Littlewood; lindelof-rh's
  Borel–Carathéodory work), and the contour shift for `Σ μ(n)n^{−s} = 1/ζ(s)`, for which
  `GlobalTheory.ResRect.residue_rectangle` exists. `logDeriv_LFunction_strip` and
  `ZetaWide.main` are related inputs. **#16** follows #10.
- **#13 explicit `L(1,χ)` and class numbers.** The class-number step is free: `L(1,χ) = πh/√d` is
  `GlobalTheory.QuadraticZeta.LFunction_one_and_mean_log_eta` in the repo, for maximal orders. The Littlewood bound for `L(1,χ)` with explicit constants is unchanged.
- **#3, #11, #12.** Unchanged: they end in explicit constants, and the repo's are existential.
  The few explicit ones are Brun–Titchmarsh `48`, the Perron kernel `3`, Mertens' first theorem
  `log 4 + 4`, and `π(y) < 1.26·y/log y`.
- **artin-grh.** Done in artin-grh PR #11 (merged): the repo's `continuedDedekindZeta`,
  `completedDedekindZeta_one_sub`, `gammaFactor_one` and `discrNormConductor_one` supply every
  field of `DedekindContinuation` except the strip bound, which the PR proves in the main
  library. `HooleyHypothesis` stays, so the result is tier C with no H hypothesis.

### Rejected in round 3

- **Catalan / Mihăilescu.** Already proved in Lean 4 (cadamcat/catalan-lean4).
- **Anything Weil-bound shaped.** `WeilBound` contains no Weil bound, and `EtaleCohomology`
  states Poincaré duality and the Frobenius weights without proving them.
- **Unconditional Bombieri–Vinogradov at level 1/2, Vinogradov's three primes, Chowla.** The
  repo has the large sieve and Siegel–Walfisz, but no Vaughan identity, bilinear estimates or
  circle method.
- **Erdős 695, Erdős 980 for general `k`, Erdős–Halberstam proper.** Reasons in the analytic
  report.
- **Briançon–Skoda, Serre's dimension inequality, Fujita-type bounds.** Each is XL.
  Briançon–Skoda has the right Skoda division theorem in the repo
  (`ReciprocityTheory.L2DbarEstimates.skoda`) but no formal statement, no ring of convergent
  germs in Mathlib, and separate arguments for `m = 1` and `m > n`. Serre's inequality needs
  Cohen's structure theorem for the reduction to the diagonal. Fujita-type bounds need the
  multiplier-ideal concentration argument, on internal definitions.
- **Elliott–Halberstam proper (`θ ≥ 1/2`) and Chowla's least-prime conjecture.** Open even
  under GRH. The repo's Linnik exponent is existential, so Xylouris's `L = 5` is out of reach.
- **"No Siegel zeros".** A one-line corollary of GRH with no formal-conjectures statement
  found. Note it in a README; it isn't a target.
- **Bach's class-group generator bound, Miller's real-cyclotomic class numbers, Weinberger's
  Euclidean rings, Harper–Murty.** All need ERH for non-abelian fields or a number-field
  Bombieri–Vinogradov. See #24.
- **Full Kummer criterion, `not_isRegularPrime_37`, infinitely many irregular primes.** Need
  the analytic `h⁻` formula. XL.
- **Brauer–Hasse–Noether in full, Grunwald–Wang.** The repo has injectivity and the zero sum of
  invariants only, on a cohomological Brauer group not linked to central simple algebras.
- **Kummer–Vandiver, Leopoldt, Greenberg, Iwasawa main conjecture, Brumer–Stark, Stark,
  Hilbert's twelfth problem.** Open, and nothing in the repo touches them.
- **Brouwer, invariance of domain, Hörmander, Markov, Lie–Trotter, Minkowski II,
  Harder–Narasimhan.** Proved in the repo, but no Atlas or formal-conjectures row turns on them.

## Round 4 (2026-11-24): started

Labels recorded before work, as the open-problems-only rule requires. Each unconditional
statement is open in the literature; the conditional theorem is published.

| # | Target | Repo | Label | Source |
|---|---|---|---|---|
| 24 | ERH for every abelian number field | abelian-erh | RH-consequence | textbook (Washington, Ch. 4); scoping in `scoping/abelian-erh.md` |
| H0 | `ψ(x,χ) = δ_χ x + O(√x log²(qx))` and `π(x;q,a) = li(x)/φ(q) + O(√x log(qx))` under GRH | psi-grh | RH-consequence | Davenport, Ch. 20; Montgomery–Vaughan Thm 13.7 |
| 33 | Squarefree numbers: `E(x) ≪ x^{2/5+ε}` under RH | erdos-969 | RH-consequence | Axer 1911; Montgomery–Vaughan Ex. 13.2.1.14; scoping in `scoping/erdos-969-squarefree-error.md` |
| 34 | Average of Goldbach representations: `Σ_{n≤x} G(n) = x²/2 + O(x^{3/2+ε})` | goldbach-average-rh | RH-equivalent | Hardy–Littlewood 1923; Fujii 1991; Granville 2007 |
| 35 | Speiser: `ζ'` has no zeros in `0 < Re s < 1/2` | speiser-rh | RH-equivalent | Speiser 1934; Levinson–Montgomery 1974 |
| 36 | Least primitive root under GRH | shoup-grh | RH-consequence | Wang 1959; Shoup 1992 |
| 10b, 16b | Liouville `L(x) = O(x^{1/2+ε})`, `Σ μ(n)n^{-s}` on `Re s > 1/2`, Franel–Landau | mertens-rh | RH-equivalent | Littlewood 1912; Franel 1924, Landau 1924 |

The attributions in this table are from memory and have not been checked against the sources;
each agent verifies its own before the README cites it.

## Round 5 (2026-11-24): done

Every earlier target has an agent's result or a recorded reason. These five extend finished
repos. All five are merged and verified tier U; the last column says what each reached.

| # | Target | Repo | Label | Source | Result |
|---|---|---|---|---|---|
| 37 | `k`-free numbers: error term `O(x^{1/(k+1)+ε})` under RH (at least the Axer-type `x^{2/(2k+1)+ε}`) | erdos-969 | RH-consequence | Axer 1911; Montgomery–Vaughan 1981 | U for Axer's `2/(2k+1)`, every `k ≥ 2`; `1/(k+1)` not proved |
| 38 | Primes in almost all short intervals `(x, x + h]`, `h/log² x → ∞`, under RH | erdos-233 | RH-consequence | Selberg 1943 | U for the existence form; the asymptotic form not proved |
| 39 | `M(x) ≪ √x·exp(C log x / log log x)` under RH | mertens-rh | RH-consequence | Titchmarsh 1927 (improving Landau 1924) | U, `C = 25` |
| 40 | Class numbers under GRH: `h(−d) ≪ √d·log log d` with explicit constants, both directions | lls-grh | RH-consequence | Littlewood 1928; LLS 2015 Cor 1.3 | U for odd discriminants, `q ≥ 10^10`, additive constant `5` |
| 41 | Mean square `∫₁^X (ψ(x) − x)² dx ≪ X²` under RH | cramer-rh | RH-consequence | Cramér 1922 | U, all three forms |

## Round 6 (2026-11-24): done

Each row closes a gap that round 5 measured. All five are merged and verified tier U, each as the full target.

| # | Target | Repo | Label | Source |
|---|---|---|---|---|
| 42 | Selberg's asymptotic form: `π(x+h) − π(x) ~ h/log x` for almost all `x`, `h/log² x → ∞` (`SelbergAsymptoticStatement`) | erdos-233 | RH-consequence | Selberg 1943; Saffari–Vaughan 1977 |
| 43 | Class-number bounds for every fundamental discriminant `−q` (even ones too), without the explicit `q % 4 = 3` and squarefree hypotheses | lls-grh | RH-consequence | Littlewood 1928; LLS 2015 Cor 1.3 |
| 44 | Liouville: `L(x) ≪ √x·exp(C log x/log log x)`; `1/ζ` bound on a region closer to Titchmarsh's `σ ≥ 1/2 + 1/log log t` | mertens-rh | RH-consequence | Titchmarsh 1927 |
| 45 | Asymptotic `∫_1^X ((ψ(x) − x)/x)² dx ∼ (Σ_ρ m_ρ/\|ρ\|²) log X` | cramer-rh | RH-consequence | Cramér 1922; Montgomery–Vaughan Thm 13.6 |
| 46 | Fujii's `O(x^{3/2})` error term for the average Goldbach count (the repo has `x^{3/2} log² x`) | goldbach-average-rh | RH-equivalent | Fujii 1991 |

## Most famous open targets

"Open" means the unconditional statement has no published proof. Every row is a published
consequence of RH or GRH, so the unconditional theorem is exactly as reliable as the RH proof in
riemann-hypothesis (see `LITERATURE_STATUS.md`).

| Rank | Target | Why it is known | Label | Effort | Atlas opportunity (rank of 1,402 open) |
|---|---|---|---|---|---|
| 1 | #10 Mertens function `M(x) = O(x^{1/2+ε})` | The best-known equivalent form of RH | RH-equivalent | M | no row for the bound |
| 2 | #24 ERH for abelian number fields | The extended Riemann hypothesis for a class of fields | RH-consequence | M–L | no row |
| 3 | #1 Euler's idoneal numbers | Euler's list of 65, 1778; open formal-conjectures statement | RH-consequence | M | +25 (255th) |
| 4 | #2 / #5 von Koch, Schoenfeld and Cramér's prime-gap theorem | The classical consequences of RH for primes | RH-consequence | S for the `O`-forms | no row |
| 5 | #7 Mills' constant | A prime-generating constant; Wikipedia-level | RH-consequence | S after #2 | +19 (row marked resolved) |
| 6 | #14 Erdős 233, sum of squared prime gaps | An Erdős problem with a formal statement | RH-consequence | L | +1 (951st) |
| 7 | #12 / #13 least primes and `L(1,χ)` bounds (LLS) | Sharp GRH bounds; upgrades two finished repos | RH-consequence | M–L | no row |
| 8 | #15 Littlewood's bound for `log ζ(1/2+it)` | The strong form of Lindelöf | RH-consequence | M | no row |
| 9 | #16 Riesz and Hardy–Littlewood criteria | Classical equivalents of RH | RH-equivalent | S–M after #10 | no row |

The Atlas scores the parent problem, not our target, and most rows are estimated. Its one clear
signal agrees with this table: idoneal numbers is the best-shaped open target we have. About
half the targets have no Atlas row; add them there first if the ranking matters.

## Recommended order

Revised 2026-11-24 for open problems only. Targets #1–#16 have agents from the `finality` work;
check `AGENTS.md` for which are finished before starting anything.

1. **H0, the GRH `ψ(x,χ)` bound**, then the `O`-forms of **#2 / #5** and **#8**.
2. **#1 idoneal numbers by the split-prime route.** The only open formal-conjectures statement
   here that looks reachable at tier U at moderate cost.
3. **#2 with Schoenfeld's constant**, then **#7 Mills**; **#3 / #12** least primes via LLS.
4. **#10 Mertens** (the repo's truncated Perron kernel removes the old blocker), then **#16**.
5. **#24 ERH for abelian fields**; **#13**; **#15**; **#14**.

Use the workflow that worked for lindelof-rh: fix every step's Lean statement in
`<Pkg>/Statement.lean` and prove the assembly first, then run parallel agents on one step each,
in separate worktrees.

## Removed: already theorems

Removed from the targets on 2026-11-24 because each is proved in the literature without RH. They
are listed so the next search does not propose them again. Their briefs are in git history
(`git show 19e7bce:docs/NEXT_TARGETS.md`) and the reasoning is in `rh-lemmas/targets-*.md`.

- **#6 ternary Goldbach.** Helfgott 2013; the GRH version (Deshouillers–Effinger–te
  Riele–Zinoviev 1997) is weaker than what is published.
- **#17 Bombieri–Vinogradov** (1965), **#21 Pollack's theorem and Erdős 1141** (2017),
  **#22 Erdős 980 for `k = 2`** (Erdős 1961), **#23 class number one** (Heegner, Baker, Stark),
  **#30 Littlewood's sign changes** (1914), **#31 Titchmarsh divisor problem** (Linnik 1961).
  Each was to be proved through GRH, which is weaker than the literature.
- **#18 Erdős 696, #19 Erdős 694, #20 Linnik's theorem, #28 Cox's `x² + ny²`, #29 Kummer's
  criterion, #32 `h(−d) → ∞`.** Known theorems; no RH involved.
- **#25 Hironaka** (done, in hironaka-fc), **#26 Zariski's local uniformisation**,
  **#27 Auslander–Reiten over regular local rings.** Known theorems; no RH involved.
- **Weak unconditional Bombieri–Vinogradov, the Erdős 971 solved variant, cited re-exports of
  class field theory, small Cohen–Macaulay modules in dimension ≤ 2.** Known theorems.

These remain reasonable *formalisation* projects for Mathlib or formal-conjectures. They are not
what this workspace is for.

## Considered and rejected

Kept so the next search doesn't rediscover these and argue about them again.

- **Gilbreath, binary Goldbach, twin primes, Legendre, Cramér's conjecture.** Not consequences of
  RH. Unreachable even with it.
- **Unconditional Artin.** Hooley's hypothesis is RH for the zeta functions of the Kummer fields
  `ℚ(ζ_k, a^(1/k))`, which are non-abelian over ℚ for `k > 2`. Their zeta functions are not
  products of Dirichlet L-functions. Even with Hecke's continuation formalised, riemann-hypothesis
  cannot discharge it. artin-grh's target stays "C + Hecke formalised".
- **Closing robin-rh's or grosswald-grh's computed range by brute force.** Morrill–Platt
  (`5040 < n ≤ exp(e^30)`) and Cohen–Oliveira e Silva–Trudgian (`409 < p ≤ 2.5·10^15`, about
  7·10^13 primes) are far beyond `native_decide`. The only route to tier U is a new argument that
  lowers the analytic threshold. See their checklist items in `AGENTS.md`.
- **Weil positivity and Beurling–Nyman** (formal-conjectures `_rhs` forms). The RH ⇒ criterion
  direction needs the full Weil explicit formula for `C_c^∞` test functions, or the hard
  direction of Nyman–Beurling. XL.
- **Knapowski–Turán refutation** (Kaczorowski, Analysis 15 (1995)). Needs oscillation theorems and
  certified zero data for `L(s, χ₄)`.
- **Montgomery pair correlation and zeta-moment asymptotics.** Not consequences of RH.
  **Rubinstein–Sarnak** needs the linear independence hypothesis (LI).
- **Euclidean rings of integers (Weinberger 1973) and Breuillard–Varjú.** Need GRH for Dedekind
  zeta of non-abelian fields.
- **Lagarias's criterion.** Already proved as `lagarias_of_RH` in robin-rh. Upstream it to
  formal-conjectures (`lagarias_criterion_rhs` / `robin_criterion_rhs`) rather than redoing it.
- **Báez-Duarte criterion.** No formal-conjectures statement, and less famous; fold it into #16 if
  wanted.

## See also

- The lemma inventory behind round 3: [`rh-lemmas/README.md`](rh-lemmas/README.md).
- Reasoning behind these choices is recorded in LivingBrain (see `AGENTS.md`, "Memory").
- The Conjecture Atlas note with the same ranking:
  [senamakel/tiny-cortexdb-mathagent#1](https://github.com/senamakel/tiny-cortexdb-mathagent/pull/1).
