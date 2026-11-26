# Conjectures workspace

This repository (`github.com/senamakel/conjectures-lean`) holds Lean 4 projects that formalise
conjectures and theorems: the 17 headline results, each a consequence of RH or GRH, and further
projects (see the table in `README.md`). Since 2026-11-26 the scope is any open conjecture in
mathematics, theoretical computer science or mathematical physics (see "Scope"). Each project is a folder under
`conjectures/` and a Lean package of its own, imported with its full history from the former standalone
repository `github.com/senamakel/<name>`. This file is the tracker: when a box changes, update it
here in the same commit as the change.

Status as of 2026-11-26 for the three newest sections, 2026-11-25 for the rest. Every box marked **verified** below was rebuilt from source on the
build box on 2026-11-24 or 2026-11-25, its `#print axioms` output read, and (for tier U) its
`scripts/check-unconditional.sh` run against riemann-hypothesis `507a75d91d`.

## Memory: LivingBrain

Memory for this work lives in [LivingBrain](https://livingbrain.com), the same memory layer the
OpenHuman agents used to build erdos-985. Claude Code reaches it through the `livingbrain` MCP
server (`https://livingbrain.fernmcp.dev/livingbrain`, configured in `~/.claude.json`).

- At the start of a session, recall what LivingBrain holds about the conjecture you're working
  on before you re-derive it: approaches tried, dead ends, constants, why a hypothesis exists.
- Write to LivingBrain whatever the repos can't hold: an approach that failed and why, a
  threshold or constant you sized up, a decision and its reason. Don't store anything git
  already records.
- This file stays the source of truth for **status**. LivingBrain holds the reasoning behind
  it. When a checklist box changes here, record the why in LivingBrain.
- If the `livingbrain` tools aren't loaded in a session, say so and don't fall back silently to
  local memory files.
- Brain: `projec1006` (`63af7dac-de64-581f-9949-9e1bed98d7fd`). Earlier captures used the source
  label "RH formalization repos"; keep using it.

### Ingestion

`scripts/lb_ingest.py` keeps the brain in step with the repos. For each submodule's remote
default branch, and for this superproject's `AGENTS.md`, `README.md` and everything under
`docs/` (read from the working tree; a file over 45,000 characters is sent in parts, because
LivingBrain rejects content over 50,000), it captures:
- documentation (`README.md`, `AGENTS.md`, `docs/*.md`, `paper/README.md`) whenever its content changes;
- new commit messages: the history of attempts, one note per repo per run;
- every PR, in any state, re-captured when it's updated. A PR closed without merging is
  labelled an abandoned attempt;
- branches with unmerged commits: attempts in flight or abandoned.

Captures are idempotent: `originRef` carries the commit, content hash or update time, and
`~/.local/state/conjectures-lb-ingest.json` records what was already sent. `--dry-run` shows the
captures without sending anything. Credentials come from `~/.claude.json` and are never printed.
Cron runs it hourly from the primary checkout and logs to `~/.cache/conjectures-lb-ingest.log`:

```
17 * * * * cd $HOME/work/personal/conjectures && flock -n $HOME/.cache/conjectures-lb-ingest.lock python3 -I scripts/lb_ingest.py >> $HOME/.cache/conjectures-lb-ingest.log 2>&1
```

The script records only what git and GitHub know. Reasoning that never reaches a commit (an
approach dropped mid-session, a constant sized up in a scratch script) has to be written to
LivingBrain by hand, as above.

## Shared facts

- Toolchain: Lean `v4.36.0`, Mathlib `fc4f59e5`. `erdos-985` is the root: it holds the analytic
  toolkit (weighted explicit formula, Hadamard factorisation, zero sums under GRH) and the GRH
  statement. Every other repo requires it as a lake dependency.
- RH/GRH come from [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
  checked against commit `507a75d91d`. It proves `riemannHypothesis : RiemannHypothesis` and
  `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`. The import needs about
  93 GB of cache, about 19 GB of RAM and roughly 900k open files. The proof was certified by
  the Lean FRO and the Mathlib Initiative on 2026-11-21
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>) and independent
  kernels accept its export (<https://math.mit.edu/~drew/grh/>); the certified release is commit
  `40e56bab`. Our checks link against the community build cache of `main` and do not repeat
  those kernel checks (`RH_FULL_BUILD=1` rebuilds from source).
- Dependency graph:

  ```
  riemann-hypothesis ── only in each Unconditional/*.lean
  erdos-985 ──┬── lindelof-rh ── mertens-rh
              ├── robin-rh ──┬── nicolas-rh
              │              └── lls-grh ──┬── bach-sorenson-grh
              │                            └── erdos-770
              ├── schoenfeld-rh ──┐
              ├── erdos-233 ──────┴── cramer-rh
              ├── abelian-erh
              └── density-rh, grosswald-grh, li-criterion-rh, speiser-rh, weinberger-grh
  ```

### A second, smaller proof of RH and GRH: lsernau/grh-lean (noted 2026-11-26)

[lsernau/grh-lean](https://github.com/lsernau/grh-lean) is a shorter Lean 4 proof of RH and of GRH for
Dirichlet L-functions, based on Alpöge's. Facts read from the repository on 2026-11-26:

- **Licence:** Apache-2.0 (Copyright 2026 Anthropic, PBC), with `NOTICE` and `ATTRIBUTION.md`. Unlike
  riemann-hypothesis it may be vendored, with credit.
- **Size:** two editions of the same five theorems, each its own Lake project: `grh/` (about 300,000
  lines, readable) and `grh-compact/` (about 76,000 lines). Mathlib is the only dependency.
- **Cost:** one to two hours on 12 cores with 24 GB of memory, from source. Compare 93 GB of
  untrusted cache and 19 GB per import for riemann-hypothesis, which has never been rebuilt here.
- **Pin:** Lean `v4.35.0`, Mathlib `56a00585`. That is not our pin (`v4.36.0`, `fc4f59e5`), so it cannot
  be imported as it is. A port of the compact edition to our pin is in progress on branch
  `grh-compact-port` (`conjectures/grh/`).
- **Axioms:** its README states `propext`, `Classical.choice`, `Quot.sound` only. Not yet checked here.
- **Review:** its README says it has passed machine checks only and that no mathematician has read it
  through.

Once the port builds, `Unconditional/` files should take RH and GRH from it: the check then runs
from source in an hour or two, needs no raised open-file limit, and the caveat about the untrusted
cache no longer applies. Until then riemann-hypothesis `507a75d91d` remains the source, and the
README rule 10 caveat stays word for word.

## Proof tiers: when a result counts as a direct proof

Each headline theorem has exactly one tier, and the README must say which.

| Tier | Name | Meaning | Allowed axioms |
|---|---|---|---|
| **D** | Direct | A closed statement with no hypotheses, proved inside the repo without importing riemann-hypothesis | standard three + documented `native_decide` |
| **U** | Unconditional via RH | `Unconditional/<X>Unconditional.lean` imports riemann-hypothesis and closes the RH/GRH hypothesis in one line | same as D; the README carries the trust caveat |
| **C** | Conditional | RH/GRH (or another open conjecture) is an explicit argument of the main-library theorem | same as D |
| **U₀** | Unconditional via an RH-repo lemma | `Unconditional/` imports riemann-hypothesis for a lemma that does not depend on RH (Siegel–Walfisz, Linnik, class field theory, resolution of singularities, …) and discharges it in one line. No RH or GRH hypothesis is involved | same as D; the README carries the trust caveat |
| **H** | Cited hypothesis | A known result we don't re-prove (a large computation, a theorem missing from Mathlib) appears as an explicit `Prop` argument | same as D |

Rules:

1. **The main library never imports riemann-hypothesis.** RH/GRH enters as an explicit
   hypothesis (`(hRH : RiemannHypothesis)` / `(hGRH : DirichletLNonvanishingRightOfHalf)`).
   Only `Unconditional/` imports the RH repo, and its theorems discharge the hypothesis in one
   line. If riemann-hypothesis ever turns out wrong, the main library is still correct as a
   conditional result.
2. **Hypothesis definitions are copied word for word** from their source
   (riemann-hypothesis `src/Statements.lean`, Mathlib's `RiemannHypothesis`, or
   formal-conjectures). Both projects use the same Lean and Mathlib pin, so the definitions are the
   same term and the one-line discharge typechecks. Never restate a hypothesis in your own words.
3. **Target statements are fixed.** `<Pkg>/Statement.lean` holds the target definitions. When a
   formal-conjectures statement exists, copy it verbatim and link to it. Don't edit these files to
   make a proof go through. If the proved constant differs from the literature (e.g. `21/5`
   instead of Bach's `2`), state the weaker theorem and say why in the README.
4. **No `sorry` on the path to a headline theorem.** Prefer a tier-H hypothesis to a cited
   `sorry`: put the input in a `Prop` (`RobinVerifiedRange`, `VerifiedUpTo`,
   `DedekindContinuation`) and prove `X_of_..._of_verified`. A theorem whose
   `#print axioms` shows `sorryAx` is not a result. It may exist only as a clearly labelled
   convenience wrapper, never as the headline.
5. **`#print axioms` is the source of truth.** Every headline theorem's axiom list goes in the
   README, pasted from real output. Allowed: `propext`, `Classical.choice`, `Quot.sound`,
   `*._native.native_decide.ax_*` and `*._native.bv_decide.ax_*` (see "Certificate results").
   Each `native_decide` needs a soundness proof for its checker
   and its count in the README. No `axiom` or `opaque` declarations for mathematical content.
6. **"Done" means tier D, U or U₀ for the full target statement**, with every remaining H
   hypothesis named. A repo whose best result is C or H is not done. It is done as far as it can
   go only when its README explains why no unconditional version is possible.
7. **Requires resolve in the checkout.** A sibling project is required by local path
   (`path = "../<name>"`), never by git URL, and its `lake-manifest.json` entry is `"type": "path"`.
   External packages (Mathlib and its dependencies) stay git requires at the shared pin.

## Literature status: label every result

What this workspace contributes is the Lean proof: each implication "RH/GRH implies X" proved in
full, and with the certified Lean proof of RH, each X as a theorem checked end to end. The
conditional theorems on paper belong to their authors and the proof of RH to Alpöge, so each
result carries a second label next to its tier, saying where the mathematics comes from. The
label goes in the README table, in the checklist heading below, and in the opening paragraph of
the repo's README (README rule 13). Attributions are in
[`docs/LITERATURE_STATUS.md`](docs/LITERATURE_STATUS.md).

| Label | Meaning | How to describe it |
|---|---|---|
| **known** | Proved in the literature with no hypothesis. Our proof uses no RH | "a complete Lean proof of X (author, year)" |
| **known, via GRH here** | Proved in the literature with no hypothesis; our proof goes through RH or GRH | "a Lean proof of X through GRH; X is also a theorem of (author, year) by other means" |
| **RH-consequence** | A published theorem "RH/GRH implies X", with X open until the 2026 proof of RH | main library: "a complete Lean proof that GRH implies X, following (author, year)"; `Unconditional/`: "X, proved unconditionally in Lean with the certified proof of RH/GRH" |
| **RH-equivalent** | X is known to be equivalent to RH | as RH-consequence, and say X is RH in another form |
| **new** | A statement or argument not found in the literature | say what is new and what was searched; needs the user's sign-off before a README uses it |

Rules:

- **State results at full strength.** Say what is proved, in the active voice, with its axioms.
  A tier-U theorem is proved unconditionally in Lean; say so. Don't open a README with what the
  result is not, and don't apologise for a formalisation: a complete machine-checked proof with
  explicit constants is a result.
- **Stay exact.** Credit the conditional theorem to its authors and RH to Alpöge. Where our
  constant or range differs from the paper's, give both numbers (README rule 8). Never call an
  open problem resolved when only part of it is proved (Erdős 233, 969, 770).
- "First in Lean" is a claim too. Before writing it, search Mathlib, formal-conjectures'
  `formal_proof` attributes and GitHub for an existing formalisation, and say what was searched.
- **Targets are open problems only** (decided 2026-11-24). A new target must have been open
  before the 2026 proof of RH: label *RH-consequence* or *RH-equivalent*. Results labelled
  *known* or *known, via GRH here* are not started, however famous. Record the label in
  this file before any work.

## README rules

Each README follows the shape already used across these repos:

1. **Title**: `# <Result> under <RH|GRH> in Lean` (or `from RH`). No marketing.
2. **Opening paragraph**: the classical statement with its source (author, year, journal or arXiv),
   and what is known unconditionally.
3. **Headline Lean block**: the exact Lean signatures of the main theorems, hypotheses included,
   copied from the source.
4. **Tier and provenance**: say which tier each headline theorem is in. Name every hypothesis and
   where its definition was copied from. If formal-conjectures has the statement, link to it.
5. **Axioms**: real `#print axioms` output in a code block, and one sentence on each non-standard
   axiom (what the `native_decide` computes and how long it takes).
6. **Proof outline**: numbered steps that point at files, with the key inequality or constant at
   each step. Put the full blueprint in `docs/PLAN.md` or `docs/BLUEPRINT.md` and link to it.
7. **Layout table** (`| File | Content |`) when there are more than about 6 modules.
8. **Deviations from the literature**: a section on any weaker constant, larger threshold or
   extra hypothesis, with the reason (see the "Deviations from the literature" section of mertens-rh).
9. **Building**: the exact `lake build` target, toolchain and Mathlib pin, and the CPU or wall
   time of the expensive modules.
10. **Unconditional version**: a table `| Theorem | Statement | Axioms |`, the riemann-hypothesis
    commit, the `scripts/check-unconditional.sh` command, the resource needs (93 GB, 19 GB RAM,
    open-file limit), and this note word for word: *"The riemann-hypothesis proof adds no axioms of its
    own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and
    independent kernels accept it (math.mit.edu/~drew/grh). This check links against the
    community build cache and does not repeat those kernel checks."* If there is
    no unconditional version, a "This result stays conditional" section saying why.
11. **Credits** for every vendored file: source repo, commit, licence, NOTICE.
12. **Claims stay calibrated.** Never write "proves the conjecture" for a tier-C or tier-H
    result. Write "proves X under GRH" or "proves X, given the computation Y". A section
    heading must not claim more than its table shows (e.g. "standard axioms only" above
    theorems that use `native_decide`).
13. **Say what is proved, then where it comes from.** The opening paragraph states the theorem
    and that Lean checks it, then credits the paper it follows, using the labels above and
    [`docs/LITERATURE_STATUS.md`](docs/LITERATURE_STATUS.md). No disclaimers about what the
    result is not; gaps to the literature go in the Deviations section with both numbers.

## Scope: any open conjecture, by connecting existing lemmas

**Decided 2026-11-26.** The workspace is no longer limited to consequences of RH and GRH. A
target may be an open conjecture in any area of mathematics. The strategy is fixed, though: we
settle a conjecture by connecting results that already exist (lemmas of big Lean proofs, our own
theorems, recently solved conjectures, published implications between conjectures), not by
looking for a new argument from nothing. The 28 projects below and their RH/GRH labels are
unchanged; the rules on tiers, axioms, fixed statements and calibrated claims apply to every
target. A target outside RH/GRH takes the label that fits (*known*, *new*, or "consequence of
X" naming the premise) and its row in `docs/NEXT_TARGETS.md` says which.

### Computer science and physics

**Decided 2026-11-26 (owner).** The scope also covers theoretical computer science and
mathematical physics, not only pure mathematics, and nothing in it has to involve RH or GRH. A
target qualifies when it is a precise mathematical statement that can be written against Mathlib:
a complexity or algorithmic bound with a finite open case (tensor rank of small matrix
multiplication, optimal sorting networks, Busy Beaver values), an extremal problem of the kind SAT
solvers settle (Ramsey, Schur, van der Waerden, Erdős–Szekeres numbers), or a finite or algebraic
problem from physics (Kochen–Specker sets, mutually unbiased bases, SIC-POVMs, kissing numbers,
quantum codes). Open problems in physics that are not mathematical statements (quantum gravity,
interpretation questions), and Millennium-hard ones (the Yang–Mills mass gap, Navier–Stokes, P vs
NP), are out of scope. Candidates and their status are in the sweep reports
`docs/atlas/sweeps/2026-11-26/cs-physics-*.md`.

Rules on top of the ones above:

- **Physical assumptions are hypotheses, never axioms.** A modelling assumption (a Hamiltonian, a
  noise model, a locality condition) is an explicit `Prop` argument (tier H) or a definition
  stated in Mathlib's terms. The statement says which.
- **Certificate results.** Many targets here are settled by a search that outputs a certificate:
  an explicit construction (a colouring, a scheme, a vector set), or an UNSAT proof. A
  construction is checked in Lean by `decide`, `native_decide` with a proved-sound checker, or a
  polynomial identity. An UNSAT proof is checked as LRAT, either through Lean core's verified
  LRAT checker (the one `bv_decide` uses) or a checker proved sound in the project. At Lean
  `v4.36.0`, `#print axioms` shows a `bv_decide` proof as `*._native.bv_decide.ax_*` (checked
  2026-11-26), the same compiler trust as `native_decide`'s `*._native.native_decide.ax_*`.
  They are allowed exactly like `native_decide`'s: counted in the README, each with one sentence on
  what it checks, how big the certificate is and how long it takes. Core's LRAT checker is
  proved sound in Lean, so it needs no soundness proof of our own.
- **The encoding is part of the statement.** When a SAT or ILP encoding is used, the theorem
  stated in Lean is the mathematical one, and the proof that the encoding is faithful (and that
  symmetry breaking loses no solutions) is in Lean too. A certificate for an encoding that only a
  script relates to the problem is not a result.
- **Record how it was found.** The README's proof outline gives the search method, solver and
  version, the parameters, the wall and CPU time, and the certificate's size and hash, so the
  search can be rerun. The refutation lane's rules on bounded searches apply to every search.
- **Bound improvements count.** A better bound on an open extremal quantity (a new lower bound by
  construction, a smaller scheme) is a priority-3 result ("strictly stronger than the published
  one") even when the exact value stays open; say both the old and the new bound.

LivingBrain is part of the method. Ingest the proofs and lemma inventories we read (statement,
source, repo and path, what it needs, what it gives), so a later search for "what proves a bound
of this shape?" finds them. Check any identifier it returns against the source.

## Priority: results not yet in the public literature

**Decided 2026-11-26 (owner).** We work on conjectures whose solution is not yet known in the
public literature: not proved in a paper, a preprint, a problem-site comment, a Zenodo note or a
public Lean repository. **Do not start a prover on a deduction that is already published**, and
stop one that is running on it. A Lean version of a known proof is a formalisation; it is not what
this workspace is for. On 2026-11-26 four provers were stopped for this reason (further Cramér,
Schinzel, abc and Berge–Fulkerson consequences); their partial branches (`impl-cramer-2`,
`impl-schinzel-2`, `impl-abc-3`, `impl-combinatorics`) are unmerged and stay that way unless the
owner asks. The implications already merged stay; the table in `README.md` marks nothing as new.

Every edge in the atlas carries a `novelty` verdict (`docs/atlas/README.md`), and a prover is
started only on an edge whose verdict is `not-found` or `asserted-unproved`.

What counts, strongest first:

1. An open statement settled outright (proved or disproved) by connecting existing results.
2. An open statement that becomes a theorem because RH and GRH for Dirichlet L-functions are
   now proved in Lean, where even the conditional deduction "RH ⇒ X" was never written down, or
   where the published conditional result leaves a finite range or a constant that we close.
3. A result strictly stronger than the published one (a better constant, a wider range, a
   hypothesis removed).
4. A new implication between open conjectures that was asserted without proof, or not stated.

Every candidate of this kind needs a novelty search before work starts and again before it is
announced: arXiv, the problem's own page and comment thread, erdosproblems.com and its mirrors,
Zenodo, formal-conjectures (statements, `formal_proof` links and open PRs),
1337isnot1337/solved-conjectures, openai/math and a GitHub code search. Record what was
searched and when. Easy visible corollaries of the RH proof are being posted within days, so a
search older than a week is stale. The label *new* still needs the owner's sign-off before a
README uses it (see "Literature status"); until then say exactly what was not found and where
we looked.

## Agent roles

Defined in `.claude/agents/`. Research roles write only to `docs/`; proving roles work in a
worktree on one project folder.

| Agent | Model | Does | Use it |
|---|---|---|---|
| `conjecture-scout` | opus | finds open statements that follow from existing results; records edges in `docs/atlas` | discovery sweeps; before any new target |
| `lemma-miner` | opus | inventories the intermediate lemmas of a big Lean proof and matches them to open problems | when a large formalisation lands; when a target lacks one input |
| `implication-prover` | opus | proves one target in `conjectures/<name>/`, statement fixed first, real `#print axioms` at the end | once a candidate is chosen |
| `lean-mechanic` | sonnet | scaffolds packages, writes `Unconditional/` modules and checkers, repairs builds | work that needs no new mathematical idea |
| `proof-auditor` | opus | rebuilds, reads axioms, diffs the statement against its source, checks README claims and prior proofs | every finished target, before merge |
| `counterexample-hunter` | opus | looks for a new witness against an open, unclaimed conjecture: transplants an existing construction to its neighbours, or searches a space first cut down by structure; prior art before compute | the refutation lane |

The order for a target is scout, prover (with the mechanic for scaffolding and checkers), then
auditor. A prover's own report is never accepted without the audit. The atlas schema is in
[`docs/atlas/README.md`](docs/atlas/README.md).

## Mine the lemmas of big proofs

A large Lean proof is worth more for its intermediate lemmas than for its last line. The headline
of riemann-hypothesis is two theorems; on the way it proves Siegel–Walfisz, Linnik, Brun–Titchmarsh,
the large sieve, a truncated explicit formula, a truncated Perron kernel, global class field
theory, Chebotarev, the continuation of `dedekindZeta`, Kronecker–Weber and Hironaka in
characteristic 0. Four of our projects exist only because of such lemmas: artin-grh (Hecke's
continuation from the Tate-thesis module), abelian-erh (`kwHom` and `continuedDedekindZeta`),
mertens-rh (the Perron kernel removed the blocker recorded for it) and hironaka-fc (90 lines of
glue around the repo's resolution algorithm). Treat every big formalisation the same way.

- **Inventory first, then match.** When a big proof lands (in riemann-hypothesis,
  1337isnot1337/solved-conjectures, formal-conjectures `formal_proof` targets, Mathlib, or any
  public Lean repo), list its intermediate statements before thinking about targets, as
  [`docs/rh-lemmas/`](docs/rh-lemmas/README.md) does. Then match the list against open statements
  in formal-conjectures and the Conjecture Atlas. Ask of each lemma "which open problem is
  missing exactly this?", and of each open problem "what is the one input it lacks?".
- **Our own theorems are premises too.** Bach's constant `2`, the least prime in a progression
  below `2(q log q)²`, Schoenfeld's `1/(8π)`, Cramér's `22/25`, `ψ(x,χ)` uniform in `q`, the
  class-number bounds and ERH for abelian fields each have published consequences that are short
  deductions. A second-order consequence costs days; a new analytic argument costs weeks.
- **One module is cheap.** Importing a single riemann-hypothesis module took 17 s and 6.6 GB of
  RAM (artin-grh), against 93 GB of cache and 19 GB of RAM for the whole proof. Smoke-test the
  one declaration (`#check`, `#print axioms`) before building on it.
- **Read the definitions, not the names.** A lemma stated over a repo-internal definition
  (`psi0`, `IsKroneckerChar`, `piMod`, `IsBlowup`) needs a bridging lemma to the Mathlib object,
  and may be degenerate. Constants in riemann-hypothesis are mostly existential, so its lemmas
  serve `O(·)` targets and do nothing for a target that ends in a finite check. The explicit ones
  found so far: Brun–Titchmarsh `48`, the Perron kernel `3`, Mertens' first theorem `log 4 + 4`,
  `π(y) < 1.26·y/log y`.
- **Import, don't paste.** A repo with no licence (riemann-hypothesis) may be imported from
  `Unconditional/` only and never copied. Record the licence of any other source before using it.
- **Implications between open conjectures count.** `theorem Y_of_X (h : X) : Y` for a published
  deduction (from abc, Schinzel's hypothesis H, Dickson, Elliott–Halberstam, another Erdős
  problem) is a tier-C result today and becomes unconditional the day `X` is proved in Lean.
  Prefer edges where both statements exist word for word in formal-conjectures.
- **The easy ones go within a week.** After the RH announcement, four people posted RH proofs of
  one Erdős problem (#462, composite reading) inside eight days. Before starting a target, check
  1337isnot1337/solved-conjectures, formal-conjectures' `formal_proof` attributes and a GitHub
  code search, and write down what was searched.
- **Keep the edges.** Every implication found, kept or rejected, goes into the atlas with its
  premise, its source and the reason, so the next sweep starts from the graph and not from zero.

## Disproofs: the refutation lane

**Decided 2026-11-26.** Alongside proving, the workspace looks for conjectures it can refute. The
strategy is the same: connect what exists. A disproof comes from one of five routes, and the
README says which:

| Route | Meaning | How to describe it |
|---|---|---|
| **a** | The negation follows from RH/GRH, a lemma of a big Lean proof, or one of our theorems | "X is false", with the tier of the premise |
| **b** | Another open conjecture refutes it (`Y ⇒ ¬X`) | "Y implies X is false"; both stay open. Never "X is disproved" |
| **c** | A disproof published on paper, not yet in Lean | "a Lean proof of (author, year)'s disproof of X" |
| **d** | The formal statement is false as written (edge case, junk value, quantifier order) | "the formal-conjectures statement of X is false as written"; a misformalisation, not a disproof of X. Report it upstream |
| **e** | A finite counterexample found by computation | "X is false: witness W", checked in Lean by `decide` or a `native_decide` with a proved-sound checker |

Rules:

- **Searches are educated and bounded.** Python, C and solvers (SAT, SMT, ILP, nauty) are
  welcome and the box has the cores and RAM, but no search starts without three things written
  down: why a witness is plausible in the range (a density or size heuristic, a structural
  reason, a hint from a related conjecture or lemma, or a prior search limit being extended),
  the bounded search space, and a stop condition. The default cap is about 2 CPU-hours per
  candidate; go past it only when the estimate says a witness is close. Never redo a range
  someone already exhausted.
- **Negative results are recorded.** A search that finds nothing goes in the sweep report with
  its range and its cost, so it is not repeated.
- **Re-derive every witness from the literal Lean statement** before it is reported, and have
  Lean check it. A witness that only a script has seen is not a result.
- The tier, axiom, fixed-statement and audit rules apply unchanged. Sweep reports are
  `docs/atlas/sweeps/<date>/disproof-*.md`; edges use `"lane": "disproof-…"`.

### What counts, and how to hunt (learned 2026-11-26)

The first day of the lane ran sixteen sweeps. Every substantive hit had already been claimed,
one of them hours earlier; the unclaimed ones were shallow. The rules below come from that.

- **The goal is a new counterexample to an open, unclaimed conjecture by a named author.** A
  Lean proof of a disproof already in the literature (Pólya, Hajós, von Sterneck) is tooling,
  not a result of this lane, and is not started without the owner asking.
- **A hit is real only if the authors tested and believed the conjecture** and the witness lies
  beyond what they checked and took structure to find. A statement false at its first small
  case, contradicting a classical theorem, or dropped from the published version (Gawron–Miska–Ulas
  5.6 at `36 − 4 = 32`; the `{1,8,k}` formula of arXiv:1401.7183v1) is recorded in one line.
- **Prior art comes before compute, and again before reporting.** Search the exact wording on
  arXiv, Zenodo, evidencepress.org, GitHub and the 1337 repo. Taken on the day: Cazenave's
  spectral Conjecture 2, Wu–Yu–Guo, Sun's A308656 Conjecture 2, Kozma–Nitzan (proved).
- **Transplant before you search.** The model is the Caiolo–Ferroni–Hoster disproof in
  1337isnot1337/solved-conjectures: a matroid family built to refute one real-rootedness
  conjecture (Bérczi–Coron–Eur–Li) was evaluated, by a closed recursion in `q`, on the
  neighbouring invariant it had never been tried on. The witness has about `17^8` points and
  was never enumerated; the 53-digit numbers in the announcement are discriminants. A
  counterexample is an asset: record it in `docs/atlas/constructions.jsonl` with the neighbours
  it has not been tested against, and test them.
- **When there is no construction, cut the space first.** Scan only the residue classes where
  local conditions block most representations (how Sun's conjectures fall near `10^8`–`10^10`);
  search inside the "minimal counterexample must…" lemmas of the source paper; pass to a
  parametrised family; let an asymptotic expansion or a zero sum locate the violation; warm-start
  case `n` from the certificate for `n − 1`. Estimate the expected number of witnesses in reach
  and drop a target far below 0.1.
- **A negative result can be evidence for the conjecture.** Brannen's conjecture in dimensions
  4 to 8: the simplex is exactly optimal among polytopes with `n + 2` facets, and the first-order
  test changes sign between 8 and 9. Say so; it points a prover at the target instead.
- **Exact arithmetic for every hit, and read definitions, not headlines.** Floating-point
  volumes and grid sampling produced false hits. A Lean file that compiles proves only its own
  definitions: stutxo/gaupenov-guyon-venier "refutes" a conjecture about the identity map, and
  its 77-digit witness is the SHA-256 of a song lyric.

The role is `counterexample-hunter` (`.claude/agents/`). Scripts of each sweep are kept under
`docs/atlas/sweeps/<date>/disproof-scripts/`.

## Cross-repo issues

- [x] **Sibling requires are local paths** (rule 7), switched 2026-11-26. Before the switch each
      project pinned an older sibling rev (erdos-985 at `9538edb` and others); every project now
      builds against the sibling folders as they stand. The per-project "Requires X at `<rev>`"
      notes below record the pins that were checked, not what is built now.
- [x] **Unconditional checks run on the build box**, 2026-11-24 and 2026-11-25,
      riemann-hypothesis `507a75d91d` (linked from the community cache, not rebuilt from
      source): erdos-985 `57436d3`, lindelof-rh `3975bbb`, density-rh `637fd12`,
      grosswald-grh `82ba03c`, weinberger-grh `683d245`, abelian-erh `9f68034`,
      robin-rh `535c9be`, nicolas-rh `4229e63`, li-criterion-rh `f058257`,
      speiser-rh `3c73ba5`, mertens-rh `4e9a6ba`, lls-grh `2fd3311`,
      bach-sorenson-grh `bbb0184`, schoenfeld-rh `62ea23a`, cramer-rh `fb22f0a`,
      erdos-770 `a640482`, erdos-233 `651e094`; on 2026-11-26: legendre-exceptions-rh `d673d91`,
      ramanujan-rh `24c7ca4`, prime-powers-rh `972f715`, bach-corollaries-grh `e9aba6d`, abundant-rh `8ce94d1`. No `sorryAx` in any log.
      The shell's hard open-file limit (524288) is too low for the import: run
      `sudo prlimit --pid $$ --nofile=2000000:2000000` first. Up to four checks fit in RAM at once.
- [x] **Licence.** This repository and every project folder carry the GNU GPL v3 (`LICENSE`,
      added 2026-11-25). Vendored files keep their own licences (Apache-2.0, MIT).
- [ ] riemann-hypothesis has no licence. Its hypothesis definitions are copied word for word
      (rule 2); check that this is acceptable.
- [ ] No CI anywhere. Add a GitHub Action that runs `lake build` and checks
      `#print axioms` against an allow-list (the cheap build, not the unconditional one).
- [ ] `RH_FULL_BUILD=1` (rebuilding riemann-hypothesis from source) has never been run.

## Per-repo checklist

### erdos-985: every odd prime has a prime primitive root `q < p` · **tier U, complete, verified** · *RH-consequence*
- [x] Statement matches formal-conjectures `erdos_985` verbatim
- [x] `erdos_985_of_GRH` (C), no `sorry`
- [x] `Unconditional/`: `erdos_985` (U), standard three + 20 `native_decide`. The `sorryAx` seen
      on 2026-11-22 came from a stale checkout and is not present on `main`
- [x] Finite check `p < 10^8` with a proved-sound checker
- [x] Paper (`paper/erdos985.pdf`)
- [x] README: Credits section and tier line
- [ ] Clean up the old checkout `~/work/personal/erdos-985` (branch `audit-proof-63d6818`, untracked `worktrees/`)

### grosswald-grh: Grosswald's conjecture, `g(p) < √p − 2` for every prime `p > 409` · **tier U, complete, verified** · *RH-consequence*
- [x] `grosswald_of_GRH : DirichletLNonvanishingRightOfHalf → GrosswaldStatement` (C), with no
      computational hypothesis; `prime_primitive_root_of_GRH_above` (`p > 10^13`),
      `verifiedUpTo_10_13 : VerifiedUpTo 10000000000000` (D). The finite range is redone in
      Lean: `409 < p < 10^13` prime by prime (2502 chunks, a segmented sieve with Lucas tests,
      soundness `Grosswald.Direct.range_sound`), `p > 10^13` by McGown–Treviño–Trudgian's
      Algorithm 1 (447 chunks). Standard three + 2950 `native_decide`; about `3.5·10^6` CPU-s
- [x] `Unconditional/`: `grosswald : GrosswaldStatement` (U, same axioms) and
      `prime_primitive_root_large_unconditional` (U, 448 `native_decide`). Checked 2026-11-25
      at `82ba03c` against riemann-hypothesis `507a75d91d`, no `sorryAx`
- [x] Pins erdos-985 at `9538edb` over HTTPS; `scripts/__pycache__` removed
- [ ] The README on `main` post-dates the plain-language pass and has not been through it

### robin-rh: Robin's inequality `σ(n) < e^γ n log log n`, `n > 5040` · **tier U, complete, verified** · *RH-equivalent*
- [x] `robin_of_RH_of_verified` (C + H), standard three only; `RobinVerifiedRange` is the range
      `5040 < n`, `log n ≤ e^30` (inside Morrill–Platt's)
- [x] `robin_verified_range : RobinVerifiedRange` (D), standard three + 624 `native_decide`: a
      compiled segmented sieve over every `m < 1.0703·10^13` with 15,746 checkpoints comparing the
      colossally-abundant envelope with `γ + log log x`, plus `5041 ≤ n ≤ 10000` directly. The
      checker (`RobinCompute/Core.lean`, Lean core only, `precompileModules`) is proved sound in
      `Robin/Compute/`; the 624 intermediate states are untrusted data re-checked transition by
      transition. About 54 core-hours to build
- [x] `robin_of_RH : RiemannHypothesis → RobinStatement` (C), same axioms; `lagarias_of_RH` (C),
      1 more `native_decide` (`13 ≤ n ≤ 5040`)
- [x] `Unconditional/`: `robin_unconditional`, `lagarias_unconditional` (U), no hypothesis left.
      Checked 2026-11-24 at `535c9be` (one comment-only commit before the merged head)
- [x] No `sorry` in the repo (the cited `robin_small_range` is deleted); `lake build RobinChecks`
      enforces the axiom allow-list
- [ ] Out of scope: the converse (Robin's inequality ⇒ RH)

### lindelof-rh: Lindelöf from RH/GRH, for ζ and Dirichlet L · **tier U, complete, verified** · *RH-consequence*
- [x] `lindelof_of_RH` (C) and `Unconditional/` `lindelof_hypothesis` (U), standard three only
- [x] `dirichletLindelof_of_GRH` (C) proved, target statement unchanged; `Unconditional/`
      `dirichletLindelof` (U), standard three only
- [x] README has the standard sections

### li-criterion-rh: Li's criterion, RH ⇒ `λ_n > 0` · **tier U, complete, verified** · *RH-equivalent*
- [x] `nontrivialPosZeros`, `lambda` copied verbatim from formal-conjectures (`86a2f58a`)
- [x] `li_criterion_rhs_of_RH` (C) and `Unconditional/` `li_criterion_rhs` (U), standard three
      only. This is the entry formal-conjectures lists as open
- [ ] Out of scope so far: the converse (positivity ⇒ RH, Bombieri–Lagarias)

### bach-sorenson-grh: least prime `p ≡ a (mod q)` · **tier U with the paper's constant 2, complete, verified** · *RH-consequence*
- [x] `bachSorenson_of_GRH : BachSorensonBound (7/2)` (C), `p < (7/2)(q log q)²` for `q ≥ 2`
- [x] `Unconditional/`: `bachSorenson_unconditional` (U), standard three + 16 `native_decide`
      (every class for `q < 2^15`, proved-sound checker)
- [x] The paper's constant: `bachSorenson_two_of_GRH : BachSorensonBound 2` (C),
      `p < 2(q log q)²` for every `q ≥ 2`, `a` coprime to `q` (Bach–Sorenson 1996, strict `<`
      as in the paper); `Unconditional/` `bachSorenson_two_unconditional` (U). Standard three +
      16 `native_decide` (`BachSorenson/Compute2/`, every class for `q < 2^15`, checker
      `BachSorensonCheck2` with soundness in `BachSorenson/Checker2.lean`, about 5 CPU-minutes).
      Analytic range `q ≥ 2^15` in `BachSorenson/Two/`: weight `log(x/n)`, zero sums summed over
      all characters at `s = 21/20`. Requires lls-grh at `b8c5afa`. Checked 2026-11-24 at `bbb0184`
- [ ] The trailing comment in `BachSorenson/Statement.lean` still says constant `2` is not
      proved; statement files are fixed, so it needs the owner's sign-off to edit

### density-rh: zero counting and the density hypothesis · **tier U (library tier D), complete, verified** · *RH-consequence; the zero count is known*
- [x] Zero-counting library `Density.ZeroCount`, unconditional (D), standard three only:
      `N(T) ≪ T log T` (`zeroCountOn_riemannZeta_le_of_subset_strip`) and
      `N(T+1) − N(T) ≪ log T` (`zeroCountOn_riemannZeta_le_of_subset_box`), with multiplicity.
      Other repos require density-rh for it instead of copying `Complex.zeroCountOn`
- [x] `densityHypothesis_of_RH` (C) and `Unconditional/` `density_hypothesis` (U), standard three
      only; statement verbatim from formal-conjectures `density_hypothesis_zeta_zeros` (open there).
      Checked 2026-11-24 at `637fd12`. Under RH the count is zero for `σ > 1/2`, and `σ = 1/2`
      is the unconditional `N(T)` bound

### nicolas-rh: Nicolas' inequality `N_k/φ(N_k) > e^γ log log N_k`, all `k ≥ 1` · **tier U, complete, verified** · *RH-equivalent*
- [x] `nicolas_of_RH` (C) and `Unconditional/` `nicolas_unconditional` (U): standard three + 1
      `native_decide` (`Nicolas.Check.loop_ok`: rational interval check at the 9591 primes
      `3 ≤ p ≤ 10^5`, proved-sound checker). Checked 2026-11-24 at `4229e63`
- [x] No formal-conjectures statement exists; `kthPrimorial` copied verbatim from it
- [x] Requires robin-rh at `dfa8d63` for its Mertens and RH estimates; does not import `Robin/Small.lean`
- [ ] Bump the robin-rh pin (robin PR #3 merged 2026-11-24, `main` at `343518c`); lls-grh pins `dfa8d63` too

### cramer-rh: Cramér's prime-gap theorem under RH with the literature's constant `22/25`; Cramér's mean-square theorem · **tier U, complete, verified** · *RH-consequence*
- [x] `primeInShortInterval_of_RH : PrimeInShortInterval 2` (a prime in `(x, x + 2√x log x]` for
      every `x ≥ 2`), `primeGapExplicit_of_RH`, and `cramer_of_RH` (the conclusion of
      formal-conjectures `cramer_conjecture.variants.conditional_rh`, `primeGap` verbatim) (C)
- [x] `Unconditional/`: `cramer_primeInShortInterval`, `cramer_primeGapExplicit`,
      `cramer_gapBound` (U), standard three only, no `native_decide` (the range below `10^6` is a
      kernel `decide` over a chain of 99 primes). Checked 2026-11-24 at `2a94117`
- [x] Cramér's mean-square theorem (`Cramer/Statement2.lean`, `Cramer/MeanSquare/`):
      `dyadicMeanSquare_of_RH` (`∫_X^{2X} (ψ(x) − x)² ≪ X²`), `meanSquare_of_RH`
      (`∫_1^X (ψ(x) − x)² ≪ X²`), `logMeanSquare_of_RH` (`∫_1^X ((ψ(x) − x)/x)² ≪ log X`) (C);
      `Unconditional/` `cramer_dyadicMeanSquare`, `cramer_meanSquare`, `cramer_logMeanSquare`
      (U). Standard three only, no computation. Requires erdos-233 at `1ff9f39`. Checked
      2026-11-24 at `7daadad`
- [x] `logMeanSquareAsymptotic_of_RH : RiemannHypothesis → CramerLogMeanSquareAsymptotic` (C)
      and `Unconditional/` `cramer_logMeanSquareAsymptotic` (U):
      `∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X`, `c₁ = Σ_ρ m_ρ/|ρ|²`, with the series proved
      convergent (`Cramer/Statement3.lean`). Standard three only. Checked 2026-11-24 at `7fbc1c7`
- [ ] Not proved: the `O(1)` error term (ours is `o(log X)`), the number `c₁ ≈ 0.046`, and
      Brent–Platt–Trudgian's constant `0.8603`
- [x] Constant `3/2`: `primeInShortInterval_three_halves_of_RH : PrimeInShortInterval (3/2)`
      (a prime in `(x, x + (3/2)√x log x]`, every `x ≥ 2`), `primeGapExplicit_three_halves_of_RH`,
      `primeInClosedInterval_three_halves_of_RH` (C) and their `Unconditional/` one-liners (U).
      Standard three only; the range below `6.4·10^7` is a kernel `decide` over a chain of 696
      primes. Each zero is bounded by a Lorentzian majorant of `sin²x/x²` (`Cramer/Sharp/`).
      Checked 2026-11-24 at `4f7655c`
- [x] Constant `107/100`: `primeInShortInterval_107_of_RH : PrimeInShortInterval (107/100)`
      (a prime in `(x, x + (107/100)√x log x]`, every `x ≥ 2`), `primeGapExplicit_107_of_RH`,
      `primeInClosedInterval_107_of_RH` (C) and their `Unconditional/` one-liners (U).
      Standard three only, no `native_decide`: a majorant of 53 shifted Lorentzian pairs is
      certified on 4033 cells by kernel `decide` in integer arithmetic (393 s), and the range
      below `10^8` is a chain of 1176 primes (182 s). `Cramer/Shift/`, `Cramer/Main5.lean`;
      a complex digamma bound is vendored from calr3/ternary-goldbach (Apache-2.0,
      `Cramer/Vendor/`). Below Dudek's `4/π`. Checked 2026-11-24 at `39bfbb1`
- [x] The literature's constant: `cmsPrimeInterval_of_RH : CMSPrimeInterval` (a prime in
      `[x, x + (22/25)√x log x]` for every `x ≥ 4`; Carneiro–Milinovich–Soundararajan 2019
      Thm 5) and `cmsPrimeGap_of_RH : CMSPrimeGap` (C); `Unconditional/`
      `cramer_cmsPrimeInterval`, `cramer_cmsPrimeGap` (U). Standard three only, no
      `native_decide`. A 33-knot piecewise-linear weight, negative outside the gap
      (`1/J = 0.8644`); the zero sum by a step majorant certified on 7076 cells by kernel
      `decide` (708 window modules in `CramerCompute/`) against Rosser's `N(T)` from
      schoenfeld-rh; primes outside the gap by a Brun–Titchmarsh bound from the large sieve,
      vendored from calr3/ternary-goldbach `330a61c` (Apache-2.0, `Cramer/Vendor/LS/`);
      analytic range `x ≥ 10^8`, a chain of 1426 primes below (`Cramer/CMS/`,
      `Cramer/Main6.lean`). Requires schoenfeld-rh at `b2c3137`. Checked 2026-11-25 at `fb22f0a`
- [ ] `docs/BLUEPRINT.md` does not describe the `22/25` route yet

### weinberger-grh: Euler's idoneal numbers are the 65 known ones, under GRH · **tier U, complete, verified** · *RH-consequence*
- [x] `idoneal_completeness_of_GRH` (C): formal-conjectures `idoneal_numbers_completeness`
      verbatim (Weinberger 1973 under GRH; unconditionally at most two more could exist)
- [x] `Unconditional/`: `idoneal_completeness` (U), standard three + 10 `native_decide`
      (every `n < 10^8`, proved-sound checker); `isIdoneal_iff` adds 1 more for the converse.
      Checked 2026-11-24 at `683d245`
- [x] Route: the split-prime witness lemma plus a GRH bound for the least split prime; no class
      number formula, no genus theory (neither can be stated against the Mathlib pin)
- [ ] Not a target (resolved theorem, owner's decision 2026-11-24): the class-number-one side
      result `starkHeegner_of_GRH` stays C + H (`ClassNumberOneNorms`, `HeegnerClassNumberOne`)
      and is not extended

### mertens-rh: `M(x) = O(x^{1/2+ε})`, Riesz, Hardy–Littlewood, Redheffer, Möbius series, Liouville, Franel–Landau · **tier U, complete, verified** · *RH-equivalent*
- [x] `mertens_of_RH : MertensBound` (`∀ ε > 0, M =O[atTop] x^(1/2+ε)`), `invZeta_bound_of_RH`
      (`1/ζ(s) ≪ |t|^ε` on `Re s ≥ 1/2 + δ`), `riesz_of_RH`, `hardyLittlewood_of_RH`,
      `redheffer_of_RH` (C); `det_redheffer : det R_n = M(n)` for `n ≥ 1` (D, *known*)
- [x] Second batch (`Mertens/Statement2.lean`, 2026-11-24), each from `MertensBound` alone:
      `moebiusSeries_of_RH` (`Σ μ(n)n^{-s}` converges to `1/ζ(s)` on `Re s > 1/2`, as a limit of
      partial sums; Littlewood 1912), `liouville_of_RH` (`L(x) = O(x^{1/2+ε})`),
      `franel_of_RH` (`Σ (f_k − k/A)² = O(N^{-1+ε})`) and `franelLandau_of_RH`
      (`Σ |f_k − k/A| = O(N^{1/2+ε})`) for the Farey sequence (Franel, Landau 1924) (C)
- [x] `Unconditional/`: all nine theorems (U), standard three only, no `native_decide`.
      Checked 2026-11-24 at `c87ad7d` (one README-only commit before the merged head)
- [x] No formal-conjectures statements exist; targets are this repo's own. Conditionally
      convergent sums are stated as limits of partial sums (a `tsum` would be the junk value 0)
- [x] Titchmarsh's bound (`Mertens/Statement3.lean`, `Mertens/Sharp*.lean`), *RH-consequence*:
      `mertensSharp_of_RH : RiemannHypothesis → MertensSharpBound`,
      `|M(x)| ≤ √x·exp(25 log x / log log x)` for large `x` (Titchmarsh 1927, improving Landau
      1924), and `invZetaSharpWith_of_RH : InvZetaSharpBoundWith 8`
      (`1/|ζ| ≤ exp(C log t/log log t)` on `σ ≥ 1/2 + 8/log log t`) (C); `Unconditional/`
      `mertens_sharp_bound`, `invZeta_sharp_bound` (U). Standard three only. Checked
      2026-11-24 at `95be863`
- [x] Requires lindelof-rh at `9165bfe`
- [x] `invZetaSharp_of_RH : RiemannHypothesis → InvZetaSharpBound` (Titchmarsh's region
      `σ ≥ 1/2 + 1/log log t`, `C = 9`) and `liouvilleSharp_of_RH : LiouvilleSharpBound`
      (`|L(x)| ≤ √x·exp(25 log x/log log x)`, `Mertens/Statement4.lean`) (C); `Unconditional/`
      `invZeta_sharp_bound_titchmarsh`, `liouville_sharp_bound` (U). Standard three only.
      Checked 2026-11-24 at `4e9a6ba`
- [ ] Not started: Simonič's explicit constant (`C ≈ 5.23`)
- [ ] Not started: the converses (each bound ⇒ RH). Littlewood 1912 and the Liouville
      equivalence are cited through secondary sources

### schoenfeld-rh: Schoenfeld's explicit `ψ`, `θ`, `π − li` bounds under RH, constant `1/(8π)` · **tier U, complete, verified** · *RH-consequence*
- [x] `psiBound_of_RH : PsiBound (1/8) 73.2`, `thetaBound_of_RH : ThetaBound (1/4) 599`,
      `piBound_of_RH : PiBound (9/20) 2657` (C); Schoenfeld's thresholds, larger constants
- [x] `Unconditional/`: `psi_bound`, `theta_bound`, `pi_bound` (U), standard three only, no
      `native_decide`, no finite range. Checked 2026-11-24 at `a72aed5`
- [x] `Real.logIntegral` vendored verbatim from formal-conjectures (no Schoenfeld statement exists there)
- [x] Schoenfeld's own constant: `schoenfeld_of_RH : RiemannHypothesis → RosserZeroCount →
      PsiCert → PsiSmallRange → ThetaSmallRange → PiSmallRange → SchoenfeldStatement` (C + H),
      and `schoenfeldPsi_of_RH`, `schoenfeldTheta_of_RH`, `schoenfeldPi_of_RH`; standard three
      only, no `native_decide`. `Unconditional/`: `schoenfeld_statement` and the three parts
      (U + H). Checked 2026-11-24 at `6d7e828`
- [x] Four of the five inputs proved (D): `Check.psiSmallRange`, `Check.thetaSmallRange`,
      `Check.piSmallRange` (1 `native_decide` each, checkers `checkA`/`checkB` with soundness
      proofs) and `psiCert : PsiCert` (a proved-sound segmented sieve to `10^10`, 21
      `native_decide`, 13.9 CPU-minutes). So `schoenfeld_of_RH_of_rosser : RiemannHypothesis →
      RosserZeroCount → SchoenfeldStatement` (C + H) and `Unconditional/`
      `schoenfeld_statement_of_rosser` (U + H), standard three + 24 `native_decide`.
      Checked 2026-11-24 at `40513b3`
- [x] The last input: `rosserZeroCount : RosserZeroCount` (D, standard three), Rosser's 1941
      Theorem 19, from a vendored proof in `Vendor/Rosser/` (216 files, about 95,000 lines:
      Garald1/RSBounds `82d7a55`, calr3/ternary-goldbach `192ca57`, teal-sea/zeta-lab
      `b09fa4dd`; Apache-2.0/MIT, licences and `PORTING.md` beside it; 188 files unchanged, 28
      with proof repairs, no statement changed). So `schoenfeld_of_RH : RiemannHypothesis →
      SchoenfeldStatement` (C) and `Unconditional/` `schoenfeld_statement` (U) hold with no
      other hypothesis: standard three + 24 `native_decide`. Checked 2026-11-24 at `62ea23a`.
      The vendored closure costs about 3 CPU-hours to build from cold
- [ ] cramer-rh requires schoenfeld-rh, so it builds the vendored libraries too

### erdos-233: `Σ_{n<N} d_n² = O(N log⁴ N)` under RH · **tier U, complete, verified** · *RH-consequence*
- [x] `erdos_233_upper_bound_of_RH` (C): formal-conjectures `erdos_233.variants.upper_bound`
      verbatim (Cramér 1936, Selberg 1943; the attribution was not checked against the sources)
- [x] `Unconditional/`: `erdos_233_upper_bound` (U), standard three only. Checked 2026-11-24 at `a4230f2`
- [x] Selberg 1943, primes in almost all short intervals (`Erdos233/Statement2.lean`,
      `Erdos233/AlmostAll.lean`): `selberg_almost_all_of_RH : RiemannHypothesis →
      SelbergAlmostAllStatement` (C): if `h(x)/log² x → ∞`, the `x ∈ [X, 2X]` with no prime in
      `(x, x + h(x)]` have measure `o(X)`. Also `primeless_measure_le` (measure
      `≤ C X log² X / H`), `smoothed_asymptotic_of_RH`, `large_gaps_of_RH`. `Unconditional/`:
      `selberg_almost_all`, `smoothed_selberg_asymptotic`, `large_gaps` (U). Standard three
      only. Checked 2026-11-24 at `57abe66`
- [x] `selberg_asymptotic_of_RH : RiemannHypothesis → SelbergAsymptoticStatement` (C) and
      `Unconditional/` `selberg_asymptotic` (U): `π(x+h) − π(x) ~ h/log x` for almost all `x`
      (`Erdos233/Selberg/`, a four-point difference of `ψ₁` and a geometric grid of ratios).
      Standard three only. Checked 2026-11-24 at `651e094`. Selberg's paper was read through
      secondary sources
- [ ] Erdős 233 itself (`N log² N`) is NOT proved and stays open even under RH: the mean-square
      bound is sharp for this method and the dyadic summation costs the extra logs

### lls-grh: Lamzouri–Li–Soundararajan under GRH: every theorem of the paper with the paper's constants (Thm 1.1, Cor 1.2, Cor 1.3, Thm 1.4, Thm 1.5), and Bach's constant `2` · **tier U, complete, verified** · *RH-consequence*
- [x] `LLS/Statement.lean` transcribes Lamzouri–Li–Soundararajan 2015 Thm 1.1 (1), 1.1 (2),
      Cor 1.2, Thm 1.4 and Thm 1.5 (arXiv:1309.3595 v3); no formal-conjectures statements exist
- [x] `leastNonresidueBelowLogSq_of_GRH` (C): Cor 1.2 as the paper states it (prime `q ≥ 5`,
      a non-residue `≤ (log q)²`), standard three only; `5 ≤ q < 4096` by kernel `decide`
- [x] `bach_of_GRH : Ankeny.BachSubgroupBound (11/4)`, `leastNonresidue_of_GRH`,
      `miller_of_GRH : Miller.MillerStatement (11/4)` (C), + 16 `native_decide` (a
      proved-sound checker run with `11/4` for `q < 2^18`, 8235 s CPU)
- [x] `Unconditional/`: `leastNonresidueBelowLogSq_unconditional` (U, standard three),
      `bach_unconditional`, `leastNonresidue_unconditional`, `miller_unconditional` (U, + the
      16 `native_decide`). Checked 2026-11-24 at `9e0adb8`
- [x] `l1UpperBoundWith_of_GRH : L1UpperBoundWith 5`, `l1LowerBoundWith_of_GRH : L1LowerBoundWith 5`
      (C) and their `Unconditional/` one-liners (U), standard three only: for primitive `χ` mod
      `q ≥ 10^10`, `|L(1,χ)|` and `1/|L(1,χ)|` are both `≤ 2e^γ(log log q + 5)`. Weaker than
      Thm 1.5 (additive constant, and `2e^γ` instead of `12e^γ/π²` in the lower bound).
      Checked 2026-11-24 at `6f10c52`
- [x] Class numbers: `classNumberUpperBoundOddWith_of_GRH_of_formula` and
      `classNumberLowerBoundOddWith_of_GRH_of_formula` (C + H `ClassNumberFormula`), standard
      three only: for every imaginary quadratic field of odd discriminant `−q`, `q ≥ 10^10`,
      `√q/(2πe^γ(log log q + 5)) ≤ h(−q) ≤ (2e^γ/π)√q(log log q + 5)`. `Unconditional/`:
      `classNumberFormula` (U₀, Dirichlet's formula from riemann-hypothesis's
      `GlobalTheory.LFunction_one_and_mean_log_eta`) and the two `_unconditional` bounds (U),
      standard three only. `jacobiChar_isPrimitive` (D). Checked 2026-11-24 at `d676318`
- [x] Every imaginary quadratic field: `classNumberUpperBoundWith_of_GRH_of_formula`,
      `classNumberLowerBoundWith_of_GRH_of_formula : ClassNumber…BoundWith 5` (C + H
      `ClassNumberFormula`) with hypotheses only `finrank ℚ K = 2`, `discr K = −q`, `10^10 ≤ q`;
      `discr_isFundamentalDiscr`, `kroneckerChar_isPrimitive` (D); `Unconditional/`
      `classNumber…BoundWith_unconditional` (U). Standard three only. Checked 2026-11-24 at `d14645b`
- [x] Bach's constant `2`: `bach2_of_GRH : Ankeny.BachSubgroupBound 2`,
      `leastNonresidue2_of_GRH`, `miller2_of_GRH : Miller.MillerStatement 2` (C), standard three
      + 15 `native_decide` (`LLS/Compute2/`, checker `LLSCheck` in exact `Rat` arithmetic,
      soundness `LLS.Check.checkChunk_sound`, 1342 s CPU for every `q < 2^2500`; a polynomial
      tail covers the rest). `Unconditional/`: `bach2_unconditional`,
      `leastNonresidue2_unconditional`, `miller2_unconditional` (U). Checked 2026-11-24 at `26ff448`
- [x] Requires robin-rh at `dfa8d63`
- [x] The paper's constants: `Sharp.l1UpperBound_of_GRH : L1UpperBound`,
      `Sharp.l1LowerBound_of_GRH : L1LowerBound` (Thm 1.5, C) and
      `Sharp.classNumberUpperBound_of_GRH_of_formula`, `…LowerBound…` (Cor 1.3, C + H
      `ClassNumberFormula`); `Unconditional/` `l1UpperBound_unconditional`,
      `l1LowerBound_unconditional`, `classNumberUpperBound_unconditional`,
      `classNumberLowerBound_unconditional` (U). Standard three only, no `native_decide`
      (`LLS/Sharp/`). Smallest margin left in Lean `0.00057`. Checked 2026-11-24 at `57e2d2a`
- [x] Theorem 1.1, both parts, with the paper's `A(q)`, `B(q)` and `q ≥ 3000`:
      `Thm11.leastPrimeOutsideSubgroup_of_GRH : LeastPrimeOutsideSubgroup` (least prime
      `ℓ ∤ q` outside `H` is `≤ (log q + B(q))²`) and
      `Thm11.leastPrimeOutsideSubgroupRough_of_GRH` (C); `Unconditional/`
      `leastPrimeOutsideSubgroup_unconditional`, `leastPrimeOutsideSubgroupRough_unconditional`
      (U). Standard three only, no `native_decide`, no finite check over `q` (`LLS/Thm11/`).
      The paper's proof treats `χ̃(p) = 1` for primes `p | q`, `p ∤ q̃`, where the value is
      unknown; charging those primes twice still closes it. Checked 2026-11-24 at `b12dee8`
- [x] Theorem 1.4: `Thm14.leastPrimeInCoset_of_GRH : LeastPrimeInCoset` (for `q ≥ 20000`,
      `H` of index `h > 1` and a coset `aH`, the least prime in `aH` is `≤ 10^9` or
      `≤ ((h−1) log q + 3(h+1) + (5/2)(log log q)²)²`) (C) and `Unconditional/`
      `leastPrimeInCoset_unconditional` (U). Standard three only, no `native_decide`, no
      finite check over `q` or `h` (`LLS/Thm14/`). Smallest certified box margin `7.0`.
      Checked 2026-11-25 at `2fd3311`
- [ ] `bach_of_GRH (11/4)` now follows from `bach2_of_GRH` by monotonicity, so its 16 chunks
      (2.3 CPU-hours) could leave the default build

### erdos-770: Erdős 770(iii) under GRH, `h(n) ≤ max(P(n), ⌈200 log² n⌉)` for `n ≥ 2` · **tier U with constant 200, complete, verified** · *RH-consequence*
- [x] Statement matches formal-conjectures `erdos_770.parts.iii` verbatim
- [x] `explicitBound_of_bach` (H; input `Ankeny.BachSubgroupBound (21/5)`), `erdos_770_iii_of_bach`:
      no `sorry`, standard three only, no finite check
- [x] `explicitBound_of_GRH`, `erdos_770_iii_of_GRH` (C), + 8 `native_decide`
- [x] `Unconditional/`: `explicitBound`, `erdos_770_iii` (U), standard three + 8
      `native_decide`. Checked 2026-11-24 at `2257436` (51 min wall on a loaded box, no `sorryAx`)
- [x] README has the standard sections
- [ ] Literature: the GRH implication is a remark in Korsky's August 2026 notes and is proved
      under a weaker hypothesis in a Zenodo note; the explicit all-`n` form was not found in
      those sources, which were read through secondary pages. Read the originals before saying
      so publicly. Not a resolution of Erdős 770: parts (i) and (ii) are untouched
- [x] Constant `200`: `explicitBound200_of_bach` (H; input `Ankeny.BachSubgroupBound 2`,
      standard three), `explicitBound200_of_GRH : ExplicitBound200` (C) and `Unconditional/`
      `explicitBound200` (U), standard three + lls-grh's 15 `native_decide`
      (`Erdos770/Statement2.lean`, `Numerics200.lean`, `Main200.lean`, `GRH200.lean`).
      `K = ⌈100·c·log² n⌉` from `BachSubgroupBound c`, so `200` from `c = 2`. Requires lls-grh
      at `8a2924f`. Checked 2026-11-25 at `a640482`
- [ ] The splitting exponent `10` is not optimised; any exponent above 2 works
      asymptotically, so the constant could approach `4c = 8`
- [x] Constant `5`: `Sharp.explicitBound5_of_lls : LLS.LeastPrimeOutsideSubgroup → ExplicitBound5`
      and `Sharp.erdos_770_iii_of_lls` (H; input LLS Theorem 1.1 (1), imported from lls-grh's
      `LLS/Statement.lean`), with `ExplicitBound5 := ExplicitBound 5 2` (`Erdos770/Sharp/`).
      Standard three only; the finite checks (`n < 216`, primes `r < 3000`, 1019 block
      certificates up to `n < 2⁷⁰⁹`) are kernel `decide`. Audited 2026-11-26 at `7c03eda`
      (every `Sharp/*.lean` but `GRH.lean` re-elaborated from source, 86 s wall), PR #26
- [ ] `Sharp/GRH.lean` (`explicitBound5_of_GRH`, C) not built: needs lls-grh's `LLS.Thm11`
      modules rebuilt in the shared build
- [ ] `Unconditional/` `explicitBound5` (U) not run
- [ ] The constant-`5` method's limit is `C → 4`; the data (`n ≤ 10⁵`) allow any `C > 2/log² 3 ≈ 1.657`

### speiser-rh: RH ⇒ `ζ'(s) ≠ 0` in `0 < Re s < 1/2` · **tier U, complete, verified** · *RH-equivalent*
- [x] `SpeiserStatement` (the fixed target), `SpeiserAbove T₀`, `SpeiserBelow T₀`, and
      `SpeiserBand a b` (added; the earlier definitions are unchanged); no formal-conjectures
      statement exists (Speiser 1934; Levinson–Montgomery 1974)
- [x] `speiserAbove_of_RH : SpeiserAbove 7` (C), standard three only: the sign of `Re ζ'/ζ`
      with sharper digamma bounds. The method stops near `|t| ≈ 6.52`
- [x] `speiserBelow_of_RH : SpeiserBelow (5/2)` (C), standard three only, real segment included:
      a size argument anchored at `ξ'(1)`, which gives `γ² ≥ 16` for every zero under RH
- [x] `Speiser.Band.speiserBand : SpeiserBand (5/2) 7` (D, no RH), standard three + 2
      `native_decide` (`coverOK_upper`, `coverOK_lower`): 71,223 cells per half, 186 s CPU. The
      checker (fixed-point complex discs at `2^-64`, Lean core only, `precompileModules`) is
      proved sound; ζ comes from a fourth-order Euler–Maclaurin step at `N = 9`
- [x] `speiser_of_RH : RiemannHypothesis → SpeiserStatement` (C) and `Unconditional/` `speiser`
      (U), standard three + the 2 `native_decide`. Checked 2026-11-24 at `3c73ba5`
- [ ] Out of scope: the converse (`ζ'` zero-free ⇒ RH); a kernel-only (`decide`) band check

### abelian-erh: ERH for every finite abelian extension of ℚ · **tier U, complete, verified** · *RH-consequence (equivalent to GRH for Dirichlet L)*
- [x] `ERH.IsDedekindZeta`, `ERH.ExtendedRiemannHypothesis` verbatim from formal-conjectures
      `Millennium/RiemannHypothesis.lean` (`9097e2f9`), whose all-number-fields
      `ERH.extended_riemann_hypothesis` stays open; `AbelianERHStatement` is this repo's own
- [x] `abelianERH_of_GRH : DirichletLZerosOnLine → KroneckerWeberStatement → AbelianERHStatement`
      (C + H; the H input is Kronecker–Weber, a known theorem Mathlib lacks at this pin),
      `cyclotomicERH_of_GRH` (C), standard three only, no computation. About 750 lines:
      `log ζ_K` against the imprimitive characters mod `N`, ramified primes in a zero-free factor
- [x] `Unconditional/`: `abelianERH`, `cyclotomicERH` (U); `kroneckerWeber` (U₀) from
      riemann-hypothesis's `kwHom`; `isDedekindZeta_continuedDedekindZeta` shows the statement
      is not vacuous. Checked 2026-11-24 at `9f68034` (one README-only commit before the merged head)
- [x] TauCeti's cyclotomic factorisation is credited as prior work; nothing was copied from it
- [ ] Tier C without H: Kronecker–Weber from Mathlib once Mathlib PR #46376 lands and the pin moves
- [ ] Washington Thm 4.3 was cited from the scoping report, not re-read


### prime-powers-rh: a prime between `x^α` and `(x+1)^α`, real `α ≥ 3` · **tier U, complete, verified** · *RH-consequence*
- [x] `primeBetweenRealPowers_of_RH`, `primeBetweenIntegerPowers_of_RH` (C), from mills-rh's `primeStrictlyBetweenCubes_of_RH`.
      Rebuilt 2026-11-26 at `61635fb`: standard three + 22 `native_decide` inherited from schoenfeld-rh
- [x] `Unconditional/PrimePowersUnconditional.lean` (U): standard three + 22 `native_decide`, no `sorryAx`. Checked 2026-11-26 at `972f715`
      against riemann-hypothesis `507a75d91d` (2323 s wall, including a wait for the RH-import slot)
- [ ] Literature: the RH result for `α ≥ 9/4` is Chamberland–Straub (arXiv:2602.22502), read from the listing only.
      Which integer exponents are open without RH was not confirmed. No prior-Lean search was done
- [ ] Not proved: `9/4 ≤ α < 3` (needs a prime-gap computation far beyond a proved-sound checker)

### bach-corollaries-grh: generators of `(ℤ/m)ˣ`, Solovay–Strassen, Miller's factoring · **tier U, complete, verified** · *RH-consequence*
- [x] `generators_of_bach`, `solovayStrassen_of_bach`, `solovayStrassenTest_iff_prime`, `millerFactoring_of_bach`,
      `eulerLiars_ne_top`, `jacobiCalc_eq`: from `Ankeny.BachSubgroupBound c`, standard three only. Rebuilt 2026-11-26 at `23ffd52`
- [x] `BachCorollaries/GRH.lean` (through `LLS.bach2_of_GRH`, C) compiled with no edits, and `Unconditional/` (U): standard three +
      lls-grh's 15 `native_decide` (`LLS.chunk2_ok_0` to `_14`), no `sorryAx`. Checked 2026-11-26 at `e9aba6d` against
      riemann-hypothesis `507a75d91d` (2987 s wall, including a wait for the RH-import slot). lls-grh, ankeny-grh and miller-grh builds
      were replayed from existing builds of byte-identical sources
- [ ] Literature: the generator bound with constant `2` sharpens the `3` of Bach 1990 §6. Whether factoring from `φ(n)` is
      known without ERH was not checked

### abundant-rh: Solé–Planat, extremely abundant numbers, extraordinary numbers · **tier U, complete, verified** · *RH-equivalent*
- [x] `solePlanat_of_RH`, `extremelyAbundantInfinite_of_RH`, `fourOnlyExtraordinary_of_RH`; the last two take
      `Robin.RobinStatement` as an argument so the main library never builds robin-rh's sieve. Rebuilt 2026-11-26 at `3b1cb54`;
      axiom lists pinned by `#guard_msgs` in `AbundantChecks`: standard three + `Nicolas.Check.loop_ok` (+ `Abundant.Check.check_ok`
      for the extraordinary-number theorem, one `native_decide`, 92 s, proved-sound checker over `n ≤ 5040`)
- [x] `Unconditional/AbundantUnconditional.lean` (U): standard three + `Nicolas.Check.loop_ok`; the last two theorems add robin-rh's 624
      `native_decide` (`RobinCompute.small_ok`, `chunk_0` to `chunk_622`), the extraordinary-number one also `Abundant.Check.check_ok`. No
      `sorryAx`. Checked 2026-11-26 at `8ce94d1` against riemann-hypothesis `507a75d91d` (2430 s wall, including a wait for the RH-import
      slot). robin-rh's sieve was replayed from an existing build of byte-identical sources (finality worktree), not recomputed
- [ ] The separate GA2 statement of Caveney–Nicolas–Sondow is not stated (its definition was not confirmed)

### ramanujan-rh: Ramanujan's inequality `π(x)² < (e·x/log x)·π(x/e)` · **tier U for `x ≥ e⁴⁰`, verified; full statement tier H** · *RH-consequence*
- [x] `ramanujan_of_RH : RiemannHypothesis → RamanujanInequalityFrom (Real.exp 40)` (C), no computation. Rebuilt 2026-11-26 at
      `d2d9ea0`: standard three + 23 `native_decide` inherited from schoenfeld-rh; `ramanujan_of_schoenfeldPi` standard three only
- [x] `ramanujan_of_RH_of_verified`: the Dudek–Platt statement (`x ≥ 38,358,837,683`) with `RamanujanVerifiedRange`
      (`[38,358,837,683, e⁴⁰]`, about `6·10¹⁵` primes) as a tier-H hypothesis
- [x] `Unconditional/RamanujanUnconditional.lean` (U): `ramanujan_inequality_from_exp40` and `ramanujan_of_verified` (the latter with
      `RamanujanVerifiedRange` as hypothesis): standard three + schoenfeld-rh's 23 `native_decide`, no `sorryAx`. Checked 2026-11-26 at
      `24c7ca4` against riemann-hypothesis `507a75d91d` (2106 s wall, including a wait for the RH-import slot)
- [ ] Literature not confirmed: Axler's `e^3158.442`, Platt–Trudgian's `exp(3915)`. Two unrefereed unconditional claims
      exist (arXiv:2408.02591, Zenodo 23440770), not checked
- [ ] Lowering `e⁴⁰` to Dudek–Platt's `1.15·10¹⁶` needs `π(x) < li(x)` for `x ≤ 1.2·10¹⁷`, which we do not have in Lean

### legendre-exceptions-rh: exceptional sets for Legendre, Oppermann, Andrica, Brocard · **tier U, complete, verified** · *RH-consequence*
- [x] `legendre_exceptions_of_RH`, `oppermann_exceptions_of_RH`, `andrica_exceptions_of_RH`, `brocard_exceptions_of_RH`:
      `O(log³ N)` exceptions among the first `N` indices, from erdos-233's `large_gaps_of_RH`. Rebuilt 2026-11-26 at `f3c0776`,
      standard three only. Conjecture statements verbatim from formal-conjectures
- [x] `Unconditional/LegendreExceptionsUnconditional.lean` (U): the four `*_exceptions` theorems, standard three only, no `sorryAx`.
      Checked 2026-11-26 at `d673d91` against riemann-hypothesis `507a75d91d` (1087 s wall)
- [ ] Bazzanella (2000, Thm 2) has `O(f(N) log² N)` for Legendre under RH, one logarithm better; not proved here
- [ ] The Oppermann, Andrica and Brocard bounds were not found in the literature (search list in the README)

### cookson-hills: the Cookson Hills and Flint Hills series converge · **tier D, verified** · *consequence of `μ(π) = 2` (OpenAI 2026)*
- [x] `cookson_hills_series_converges`, `flint_hills_series_converges`: statements verbatim from formal-conjectures (both `research open`
      there). Replayed 2026-11-26 at `8fd961f` (19,998 jobs), standard three only, no `native_decide`
- [x] Premise vendored: openai/math `PiExponent` tree at `3344da5` (Apache-2.0, 869 files), ported to our pin; 29 files changed, listed in
      `NOTICE`; two `rfl` lemmas the kernel did not finish were removed and their one use re-proved
- [x] The link Flint ⇒ Cookson (`sin² 2x ≤ 4 cos² x`) is ours, about 60 lines; not found written down, no novelty claimed
- [ ] A cold rebuild from source in the primary checkout has not been timed
- [ ] OpenAI's proof of `μ(π) = 2` has had no human review that we know of; our kernel accepts it

### sun-prime-density-rh: Sun's conjecture, `π(n^k)/n^k` strictly decreasing (OEIS A038098) · **tier C for `k ≥ 4` verified, U check pending; `k = 3` partial** · *RH-consequence; no proof found in the literature*
- [x] `sun_of_RH`: every `k ≥ 4`, `n ≥ 2`; statement verbatim from formal-conjectures `OeisA38098.conjecture1` (`research open`).
      Rebuilt 2026-11-26 at `71e7505`: standard three + 23 `native_decide` from schoenfeld-rh + 2 of its own
      (`Check.chainOK_piTable`, primes below 2,825,761, 32 s; `Check.allOK_eq_true`, 0.9 s), proved-sound checkers
- [x] `sun_three_of_RH`: `k = 3` for `2 ≤ n ≤ 140` and `n ≥ 10⁷`; `sunConjecture_iff_of_RH` reduces the whole conjecture to the gap
- [ ] `k = 3`, `141 ≤ n < 10⁷`: needs `π(n³)` up to about `10²¹` or a sharper explicit bound; not in Lean
- [ ] `Unconditional/SunPrimeDensityUnconditional.lean` written; check started 2026-11-26, result not yet read
- [ ] Novelty search of 2026-11-26 found no proof of any case (OEIS page, MathOverflow 301662, arXiv, formal-conjectures PRs,
      GitHub, solved-conjectures). The label *new* needs the owner's sign-off before the README uses it
- [ ] `Check` is a root namespace in this package; move it under `SunPrimeDensity` before another project copies the name

### primitive-root-sq-grh: a prime primitive root `q < p` modulo `p²` and every `p^k` · **tier C verified, U check pending** · *RH-consequence; the all-`p` statement was not found in the literature*
- [x] `primitiveRootSq_of_GRH`, `primitiveRootPow_of_GRH`: every odd prime, no exceptions. Replayed 2026-11-26 at `7f76f54`:
      standard three + 20 `native_decide` (`PrimitiveRootSq.Compute.chunk_ok_*`, all `p < 10⁸`, about 26 CPU-minutes, proved-sound checker)
- [x] Threshold stays at `10⁸`: one extra character of order `p` modulo `p²`; tightest margin 1.6% at `ω(p − 1) = 9`
- [x] `Lift.lean`: a primitive root mod `p²` is one mod every `p^k` (not in Mathlib)
- [ ] `Unconditional/PrimitiveRootSqUnconditional.lean` written; check started 2026-11-26, result not yet read
- [ ] Literature: Martin (Acta Arith. 80, 1997, Cor. 3.1) gives it for all sufficiently large `p` under GRH with no explicit constant.
      The label *new* needs the owner's sign-off
- [ ] Next in the cluster, not started: Grosswald's conjecture modulo `p²` (Kerr–McGown–Trudgian), about 1000 CPU-hours of checks

### sun-pi-inequalities: Sun's Conjectures 2.7(i) and 2.14(ii) on `π(x)` (arXiv:1402.6641; OEIS A238165 (ii), A038107 (i)) · **tier D, complete, audited** · *no proof found in the literature*
- [x] `sun_2_7_i`, `oeis_A238165_ii`, `sun_2_7_i_nat`: `π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}` for `n > 4`, `1 ≤ k ≤ n`. Rebuilt from source
      2026-11-26 at `98a1b97` (merged as PR #23, `9594f71`): standard three only; finite range (391 pairs, `n ≤ 63`) by `decide +kernel`
- [x] `sun_2_14_ii`, `oeis_A038107_i` (with limit 1), `sun_2_14_ii_nat`: `π(n²)^{1/n}` strictly decreasing for `n ≥ 3`. Standard three
      + 1 `native_decide` (`SunPi.checkB_ok`, `n ≤ 699`, prime counting to 490000, about 10 s; proved-sound `checkB_sound`, read)
- [x] Statements transcribed from arXiv:1402.6641 v12 and the OEIS comments, compared by the auditor 2026-11-26 (ranges, direction,
      strictness); `a` verbatim from formal-conjectures `OeisA38107.a`, which states neither conjecture. Python check: both hold on
      small cases and fail just outside their ranges (`n = 4, k = 1`; `n = 1, 2`)
- [x] Novelty search 2026-11-26 (arXiv/Exa, OEIS, MathOverflow, formal-conjectures PRs, GitHub code): no proof found. The label *new*
      needs the owner's sign-off
- [ ] Other parts of Conjectures 2.7 and 2.14 (2.7(ii), 2.14(i), 2.14(iii)) and A238165 (i) not attempted

### bach-sharp-grh: Bach's sharp generator constant `2/log² 3` for `(ℤ/m)ˣ` · **tier D + C outside `2^17 ≤ m < 5·2^49`, verified; full statement not proved; U check pending** · *RH-consequence; the sharp constant was not found in the literature*
- [x] `SharpSubgroupBound`, `SharpGeneratorBound` are `Ankeny.BachSubgroupBound` and `BachCorollaries.GeneratorBound` at `2 / Real.log 3 ^ 2`
      (every modulus); `SharpOptimal` (no `c < 2/log² 3` works) is proved at `m = 3`. Read by the auditor 2026-11-26; Python check
      `3 ≤ m ≤ 3000`: worst ratio `G(m)/log² m` is 1.657071 at `m = 3`, then 1.561 (`4`), 1.557 (`6`)
- [x] `sharpOptimal` (D), standard three only. Rebuilt 2026-11-26 at `9a18f66` (merged as PR #24, `ee15c22`), 33 s replay
- [x] `sharp_small` (D, every `q < 2^17`, no GRH): standard three + 4 `native_decide` (`small_ok_S0..S3`, ankeny-grh's generation
      search, 18 s to 1335 s CPU; sound by `checkSmall_sound`, read)
- [x] `sharp_large_of_GRH` (C, every `q ≥ 5·2^49`): from `bach1657_large_of_GRH` (constant `1657/1000`) and `c1657_le_sharpConst`
      (`1.657 < 1.6570709`); standard three + 2 `native_decide` (`chunk_ok_L0`, `chunk_ok_L1`, lls-grh's block checker at `cn/cd`,
      sound by `checkChunkC_sound`, read) + polynomial tail `goodQ_tailS` for `q ≥ 2^7400`
- [x] `sharp_outside_gap_of_GRH`, `generators_outside_gap_of_GRH`, `sharp_of_GRH_of_gap` (C; `SharpGap` an explicit argument),
      `bach_sharp_of_GRH` (C, + lls-grh's 15 `chunk2_ok_*`)
- [ ] `SharpGap` (`2^17 ≤ q < 5·2^49`) not proved: the GRH budget fails at `c = 1.657` for smooth moduli up to about `10^13.2`;
      needs a kernel-enumerating block checker and structural generation certificates (`docs/PLAN.md`)
- [ ] `Unconditional/BachSharpUnconditional.lean` written, not run
- [ ] Literature: Bach 1990 §6 gives `2/log² 3` for his Theorem 2 (run of integers) and leaves the prime-to-`m` form open; read
      through a web copy of the paper, not the journal PDF

### implications: `X → Y` between open conjectures · **every theorem tier C or H, verified** · *premise open*
- [x] PRs #1 to #6, #11, #13 and #14, each rebuilt on `main` and its axioms read (standard three): Rotkiewicz; Erdős 382 (i) from Cramér /
      Firoozbakht; Butson ⇒ Hadamard; four exponentials ⇒ `2^t` or `3^t`; abc ⇒ Erdős 936 and 977 (factorial);
      Dickson / Schinzel consequences (Erdős 891 Weisenberg, Erdős 647 infinite variant, twin primes and relatives);
      Erdős 142 lower variant and all-`k` Erdős 140 from the quantitative density bound; abc ⇒ non-Wieferich primes
      (Silverman), powerful triples, Brocard, Erdős 366 forms; Dickson ⇒ admissible patterns at consecutive primes
      (Erdős 141, 218 variant, balanced primes); Firoozbakht ⇒ Oppermann, Andrica, Legendre, Brocard
- [x] PR #12 (merged 2026-11-26, `42c8652`), refutation lane route b: Richards' incompatibility,
      `HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture` verbatim from formal-conjectures
      (first Hardy–Littlewood conjecture ⇒ the second is false). Standard three axioms, no `native_decide`:
      the 447-tuple's admissibility and `π(3159) ≤ 446` are kernel checks. Both conjectures stay open
- [x] PR #12 audited 2026-11-26 at `768fd21`: pass. The three modules were rebuilt from source, the axioms
      re-read (standard three), the statement re-elaborated against a fresh copy of the formal-conjectures
      text, and no earlier Lean proof was found (GitHub code search, formal-conjectures PRs, 1337). Not
      checked: the proof at formal-conjectures' own pin (Lean v4.33.1, Mathlib `0df444a`)
- [ ] Erdős 855 (the form eventual in both `x` and `y`) does not follow from one tuple: it needs dense
      admissible tuples of every large width (the Hensley–Richards sieve). Sized L in
      `docs/atlas/sweeps/2026-11-26/disproof-erdos.md`; not started
- [x] Statements copied word for word from formal-conjectures `9097e2f`; the table is in the root `README.md`
- [ ] `scripts/erdos142-discharge/` (the link to openai/math's `manuscriptQuantitativeDensityTheorem`) has not been typechecked
- [ ] Some modules define copied names in root namespaces (`Nat.Full`, `Set.IsAPOfLength…`, `ABC`, `Erdos936`); move them
      under `Implications.` before a second module copies the same definition
- [ ] None of these is a result about the consequence by itself. Never describe one as solving its Erdős problem

### hajos-catlin: Hajós' conjecture is false (Catlin 1979), witness `C₅[K₃]`, `k = 8` · **tier D, complete, audited** · *known* (refutation route c, owner sign-off 2026-11-26)
- [x] `HajosConjecture.hajos_conjecture`: formal-conjectures statement verbatim (`9097e2f`), standard three, no `native_decide`
- [x] `hajos_conjecture.variants.catlin_eight` (`CatlinVariant 8`); `χ ≥ 8` and no `K₈`-subdivision proved by a column-counting argument, finite checks by `decide`
- [x] Audited 2026-11-26 at `8841eaf`, pass: rebuilt from source, axioms re-read (standard three, no `native_decide`), statement re-elaborated against a fresh paste of formal-conjectures `9097e2f`, an independent exhaustive search over all 6,435 branch sets confirmed no `K₈` subdivision and χ = 8, no earlier unconditional Lean disproof found. The owner signed off on this *known*-label target on 2026-11-26
- [ ] `variants.catlin` for the other `k ≥ 7` (Catlin's other graphs, `k = 7` included) not done

### polya-liouville: Pólya's and von Sterneck's conjectures are false · **tier D, complete, audited** · *known* (refutation lane, route e: a witness checked by `native_decide`, owner sign-off 2026-11-26)
- [x] Statements written here (no formal-conjectures statement): `PolyaConjecture` (`L(n) ≤ 0`, `n ≥ 2`), `VonSterneckConjecture` (real) and `VonSterneckConjectureInt` (`4M(x)² < x`), `x > 200`
- [x] `liouvilleSum_906150257`, `polya_conjecture_false` (D): standard three + 1 `native_decide` (23–37 s)
- [x] `mertens_7725038629`, `vonSterneck_conjecture_false`, `vonSterneck_conjecture_int_false` (D): standard three + 1 `native_decide` (110–170 s; full build 2.5–4 min on a loaded box)
- [x] Checker `Polya.Check` proved sound (`runLiouville_sound`, `runMertens_sound`, standard three): table check of `Σ_{k≤y} M(⌊y/k⌋) = 1` on `V`, `λ * ζ = 𝟙_□`; the table builders are untrusted
- [x] Audited 2026-11-26 at `2106d53`, pass: rebuilt from source (3:58 wall, 2.5 GB), axioms re-read (standard three + 2 `native_decide`; both soundness theorems standard three), checker call graph read, tamper tests reject altered tables, and an independent segmented sieve in C reproduced L(906150257) = 1 and M(7725038629) = 43947 and found both are the least counterexamples (that minimality is checked in C only, not in Lean)
- [ ] Not proved in Lean: minimality of `906150257` (Tanaka 1980) and `7725038629` (Cohen–Dress, CNRS report 1979). Pólya-side citations are from secondary sources; Jurkat (1960) is unverified
- [x] Prior art: formal-conjectures open PR #8202 (same Pólya statement plus a least-counterexample statement, no proof; no statement exists at `9097e2f`); wappy-x/Mathematics `checks/what_counts_as_a_proof_check.lean` assumes `L(906150256) = 0` as a hypothesis, so it is not a complete proof

### gmu-binary-partitions: Conjecture 5.6 of Gawron–Miska–Ulas is false · **tier D, complete, audited, awaiting owner's decision** · *new* (refutation lane, route e: a finite witness; the label needs owner sign-off)
- [x] Statement written here (no formal-conjectures statement), transcribed from the arXiv v1 source (`GMU_MOFM_Revision_II.tex`, label `cong:powerof2-1`); `b m n` is the coefficient of `X^n` in `∏_{i≤n} (∑_j X^{2^i j})^m` in `ℤ⟦X⟧`, tied to the paper's `∏ (1 − x^{2^i})^{−m}` by `one_sub_mul_geomPow2`, `coeff_truncatedSeries`, `b_eq_coeff_of_mul_eq_one`
- [x] `gmu_conjecture_5_6_false` (D), witness `m = 1, k = 3, n = 1` (`b₁(16) − b₁(4) = 32`, modulus `2^6`): standard three, no `native_decide`
- [x] `…_fails_at_m1_k5`, `…_fails_at_m3`, `…_fails_at_m4`, `…_fails_at_m5` (D): standard three, values by `decide +kernel` through `bList`, proved sound (`bList_sound`); `…_fails_at_m6` adds 2 `native_decide` (same checker)
- [x] README says: `m = 1` is a corollary of Churchhouse's congruence (Rødseth 1970, Gupta 1971); only `m ≥ 3` is new; `m = 2` holds for `4 ≤ k ≤ 24`, `2^{k+1} n < 2^26` (C, outside Lean); a minor correction
- [ ] Audit pending: rebuild, re-read the axioms, re-transcribe the conjecture from the source, recompute the witnesses independently
- [ ] The journal text (Monatsh. Math. 185 (2018)) was not read; Rødseth's and Gupta's exactness statement is cited through Ulas–Żmija arXiv:1904.03398
- [ ] Owner sign-off on the *new* label

## Working here

- Changes to this superproject's own files (`AGENTS.md`, `README.md`, `docs/`, `scripts/`) go
  straight to `main`: no worktree, no PR.
- Work inside the project folders goes on a branch made with `worktree <slug>` here, and lands
  through one PR to this repository, however many folders it touches.
- Adding a conjecture: create `conjectures/<name>/` as its own Lean package (`lakefile`, `lean-toolchain`,
  `README.md`), then give it a row in `README.md` and a section in the checklist below.
- Projects require their siblings by local path (`path = "../<name>"` in `lakefile.toml`), so a
  change to one folder is seen by every project that depends on it at the next build, with no pin
  to bump. Run `lake update <Pkg>` in a dependent after adding or removing a sibling require.
- Lean projects with no `.lake` here yet: run `lake exe cache get` first in erdos-985. The
  siblings will build only after the pins are fixed.
- Build one module at a time when iterating (`lake build LLS.ClassNumber`). The `native_decide`
  modules dominate build time (grosswald-grh about 3.5 million CPU-seconds, robin-rh about 54
  core-hours, lls-grh about 2.7 CPU-hours).
- After any change to a headline theorem, re-run `#print axioms` and update the README block in
  the same PR.
