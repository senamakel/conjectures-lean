# Lane `disproof-kozma-nitzan`: counterexample hunt for the Kozma–Nitzan percolation inequalities

Lane `disproof-kozma-nitzan`, 2026-11-26. Research only. No Lean file and no existing file was
edited. No search was run: the step-0 prior-art check found that the targets were settled in
public in September–October 2026, so the lane stopped there, as its brief required.

## Main finding

**No hit, and the lane is closed: the conjectures are proved.** Kozma–Nitzan's Conjectures 1,
2, 4 and 6 and Questions 5, 7 and 9 (arXiv:2401.12397) have public proofs with a Lean
development. Question 8 has a published counterexample, but only under the every-minimiser
reading, where one of two tied minimisers fails. A proved statement has no counterexample, so
no compute was spent (0 CPU-h).

- **Bou-Rabee's Lean development.** GitHub `nitromannitol/percolation-after-anthropic`
  (Apache-2.0, created 2026-09-05) has an accompanying manuscript, "Kozma–Nitzan Connection
  Inequalities for Bernoulli Percolation" (dated 5 September 2026; credited to ChatGPT 5.6
  Sol and Claude Fable 5.1, prompted by Ahmed Bou-Rabee). It states:
  - Conjectures 1, 2, 3, 4 and 6 are proved, with the strong pre-FKG form (display (3)) and
    Conjecture 4 with the minimiser chosen before conditioning.
  - Questions 5, 7 and 9 are answered yes, and Question 5 holds with a single coefficient
    vector that works for every `b`.
  - Question 8 is refuted on 4 vertices: `A = {a₁, a₂}`, `p(o,a₁) = p(a₂,b) = 1`,
    `p(a₁,a₂) = 1/2`. Both points of `A` minimise `P(x ↔ b, o ↮ A) = 0`, and `a₂` fails
    with `1/2 < 1`.
  - The repo's README says the Lean development builds on Anthropic's formalisation of
    `θ(p_c) = 0` for bond percolation, pinned as a git dependency.
- **Blanc-Renaudie, arXiv:2610.10502** (2026-10-07), "Notes on Kozma and Nitzan's proof of
  θ(p_c)=0". A human-written proof of a strengthened Conjecture 4: for increasing `F`, if `a`
  minimises `E[F(C_a)]` over `A`, then `E[F(C_0); 0 ↔ A] ≥ E[F(C_a); 0 ↔ A]`. Conjectures 1
  and 2 and Question 7 follow from it.
- **Gouéré, arXiv:2610.30063** (2026-10-21), "On the proof of the Kozma-Nitzan conjecture".
  An exposition of the Conjecture 1 proof, which it describes as "provided by an AI".
- **Kalai's blog** "Combinatorics and more", 2026-09-03: "The θ(p꜀) = 0 conjecture is solved
  in all dimensions", with the caveat "if verified".
- **Not read beyond search highlights.** Toledo, Zenodo 10.5281/zenodo.24168178 (2026-11-12),
  reports an independent check of the Lean proofs. There is also an OpenAI preprint,
  "Critical bond and site percolation on the cubic lattice", on `openai/math` on GitHub, and
  Flammant, arXiv:2609.03492, a related finite-graph conjecture.

The sibling lane's report (`disproof-inequalities.md` §5, written the same day) said "Exa
found no refutation". That was correct but incomplete: the conjectures had already been
*proved*. Its "best unfinished lead" should be withdrawn.

**What I did not check.** I did not read the proofs or build the Lean development. The
statements above come from the abstract pages, the GitHub README and Exa search highlights of
the manuscripts. Before any project relies on these results, read the PDFs and run
`lake build` on the repo.

## Step 0: the statements, transcribed from the arXiv source

The source is arXiv:2401.12397, which has only one version (v1, 2024-01-22). I read the source
file `the_set_inequality.tex` with `python3 -I`; it sits in the sibling's scratchpad
`/tmp/claude-1000/-home-ubuntu-work-personal-conjectures/e6c3a6a3-3702-43d3-8640-5f8f102b5329/scratchpad/hunt-ineq/dl/2401.12397/`.

**Numbering.** The paper numbers conjectures and questions with one global counter
(`\newtheorem{conj}{Conjecture}`, `\newtheorem{quest}[conj]{Question}`). The numbering is
therefore Conjecture 1, 2, 3, 4, Question 5, Conjecture 6, Questions 7, 8, 9. The sibling's
labels "Conjecture 5.1" and "Questions 5.5–5.7" are wrong, and it did not test Question 5 or
Conjecture 6. There are **four** Questions, not three.

Setting: `G` is a finite graph, each edge `e` is open independently with probability
`p(e) ∈ [0,1]`, and `0 ↔ A` means that 0 is joined by an open path to some point of `A`.

- **Conjecture 1 (post-FKG).** "Let G be a finite graph with arbitrary probabilities on its
  edges, let 0, b ∈ G be two vertices and let A ⊂ G be a set of vertices. Then
  P(0↔b) ≥ P(0↔A) min{P(a↔b) : a ∈ A}."
- **Conjecture 2 (pre-FKG).** Same `G`, `0`, `b`, `A`: P(0↔b) ≥ min{P(0↔A, a↔b) : a ∈ A}.
  The paper also states the formally stronger display (3),
  P(0↔b, 0↔A) ≥ min_a P(0↔A, a↔b), and notes that the two are equivalent when b ∈ A.
- **Conjecture 3 (ε–δ).** "For every ε>0 there exists δ>0 such that for any graph G, any A ⊂ G,
  and any 0,b ∈ G which satisfy P(0↔A) > 1−δ and P(a↔b) > 1−δ for all a ∈ A, we have
  P(0↔b) > 1−ε." This is the only conjecture used for θ(p_c)=0 (Theorem "conjtotheta"). It
  is asymptotic, so it has no finite witness. It follows from Conjecture 1 with δ = ε/2.
- **Conjecture 4 (monotone cluster property, "might be true").** "For any graph G, any monotone
  cluster property f, any A ⊂ G and any 0 ∈ G,
  E(f(0)·1{0↔A}) ≥ min_{a∈A} E(f(a)·1{0↔A})." Here f(v,ω) depends only on the vertex set
  Cl_ω(v), is increasing in it, and satisfies f(v,ω) = f(w,ω) when {v,w} ∈ ω.
  - Proved by the authors: |A| = 2; 0 isolated in G∖A; and f = 1{|Cl| ≥ k} for k ≤ 4.
  - Conjecture 4 for f = |Cl| implies Conjecture 2.
  - Remark (mine). By LP duality, Conjecture 4 for all f at once is equivalent to this: some
    probability vector λ on A makes the law of Cl(0) on {0↔A} stochastically dominate the
    λ-mixture of the laws of Cl(a) on {0↔A}, in the poset of connected vertex sets. Taking
    f = 1{b ∈ Cl} then gives Question 5 in its strong form.
- **Question 5 (coefficients).** "Is it true that for any graph G, any A ⊂ G and any 0 ∈ G
  there are nonnegative coefficients (c_a : a ∈ A) with Σc_a = 1 such that
  P(0↔b) ≥ Σ_a c_a P(0↔A, a↔b) holds for all b ∈ G?"
- **Conjecture 6 (gluing).** Let a minimise P(a↔b) over A. Let {v,w} be an edge with
  P_G(x↔b) ≥ P_G(x↔A) P_G(a↔b) for x ∈ {v,w}. Then the same inequality holds at v in G with
  {v,w} contracted. The authors show that Conjecture 6 implies Conjecture 1. Their theorem in
  §"Counterexamples" refutes the variant that takes an arbitrary a ∈ A.
- **Questions 7–9 (candidates).** The authors introduce them as "Numerical evidence points
  towards an answer of 'yes' for all of them, but we are rather hesitant". Each asks whether
  P(0↔b, 0↔A) ≥ P(0↔A, a↔b) holds for a particular choice of a:
  - Question 7: a minimises P(a↔b) over A.
  - Question 8: a minimises P(a↔b, 0↮A).
  - Question 9: a minimises P_H(a↔b), where H is G with every edge at 0 removed.

**Reductions (§5 "Simple reductions"), with their scope.** All four are "without loss of
generality" reductions for a *proof*. For a search they work the other way: a counterexample
exists if and only if one exists in the reduced class, possibly only on a larger graph.

1. **p = 1/2 everywhere.** Each edge of probability p is replaced by a parallel-paths gadget
   whose connection probability is within ε of p, and the argument lets ε → 0. This works for
   the connection-probability statements (Conjectures 1 and 2). It is approximate and makes the
   graph larger. Dyadic p can be simulated exactly by series-parallel gadgets. For
   Conjecture 4 with f = |Cl| the gadget adds vertices and changes f, so the reduction does
   not apply verbatim.
2. **All degrees equal to 3.** High degrees are simulated by cubic gadgets with probability-1
   edges, and low degrees are padded with dangling gadgets. The authors say: "It would be
   interesting to combine these two reductions, but it seems that this would require a new
   idea." So **p = 1/2 and degree 3 together is not a proven reduction.** A search over
   subcubic graphs at p = 1/2 would have covered a subfamily, not a reduced class.
3. **0 not adjacent to b.** This holds for Conjectures 1 and 2 by concavity in the post-FKG
   version and linearity in the pre-FKG version.
4. **A a superlevel set {a : P(a↔b) > p}.** This is stated without saying which conjecture it
   covers. It is clearly valid for Conjecture 1: enlarging A to the superlevel set of its
   minimum raises P(0↔A) and keeps the minimum.

The authors also note that for Conjecture 2 one may assume b ∈ A, by passing to A ∪ {b}.

## What stays open

- **Question 8 with a unique minimiser, |A| ≥ 3.** The Bou-Rabee manuscript (Theorem 9.4)
  proves Question 8 for |A| ≤ 2 when the minimiser is unique, or when P(0↮A) > 0. Its Remark
  9.5 says the argument "does not determine whether (4) holds for the unique minimiser of ρ_x
  when |A| ≥ 3". I read this only through a search highlight.
  - **What earlier searches cover.** The sibling's `src/percq.py` counts a violation only when
    *every* tied minimiser fails, which for a unique minimiser is exactly this reading. It
    found none: all connected graphs with n ≤ 6 at p = 1/2 and at random per-edge p, and
    n = 7 with 3 random draws. Ties were decided in double precision with tolerance 10⁻¹².
  - **Why it is not a strong target.** This is a "question" that the authors were "rather
    hesitant" about. Its only failure so far is a degenerate case of ties at probability 0
    or 1. An exact integer-count C search over n ≤ 9 with dyadic p would be the natural next
    step if someone wants it, but it does not meet the refutation lane's bar of a conjecture
    the authors believed.
- **The existential-tie reading of Question 8** (some minimiser works) is not addressed by the
  published counterexample.

## Searches run (do not repeat)

| Target | Range | CPU-h | Outcome |
|---|---|---|---|
| Kozma–Nitzan Conjectures 1, 2, 4, 6; Questions 5, 7, 9 | none: the step-0 prior-art check found them proved (Bou-Rabee Lean development, 2026-09; Blanc-Renaudie arXiv:2610.10502) | 0 | closed, **taken** (proved) |
| Kozma–Nitzan Question 8 | none run here; sibling coverage above | 0 | every-minimiser reading refuted in public; unique minimiser with \|A\| ≥ 3 open |

## Proposed edges

```jsonl
{"premise": "Kozma-Nitzan Conjectures 1, 2, 4, 6 and Questions 5, 7, 9 (arXiv:2401.12397) are proved: Lean development nitromannitol/percolation-after-anthropic (2026-09-05) with manuscript 'Kozma-Nitzan Connection Inequalities for Bernoulli Percolation'; human-written proof of strengthened Conjecture 4 in Blanc-Renaudie arXiv:2610.10502", "premise_status": "solved", "premise_lean_source": "https://github.com/nitromannitol/percolation-after-anthropic (not built here)", "consequence": "no counterexample exists to the Kozma-Nitzan post-FKG, pre-FKG, monotone-cluster-property or gluing conjectures; the refutation lane for them is closed", "consequence_ref": "Kozma-Nitzan, arXiv:2401.12397 v1, Conjectures 1, 2, 4, 6, Questions 5, 7, 9", "consequence_status": "solved", "implication_source": "prior-art check, this sweep (Exa web search; arXiv abs pages 2401.12397, 2610.10502, 2610.30063; GitHub README)", "effort": "S", "lean_exists": "claimed (not checked)", "in_1337": false, "class": 1, "notes": "taken; proofs and Lean build not checked here; supersedes the 'best unfinished lead' of disproof-inequalities.md section 5, whose numbering (5.1, 5.5-5.7) is wrong (global counter: Conj 4, Questions 7-9)", "novelty": "published", "novelty_searched": "Exa web search (Kozma Nitzan conjecture proof counterexample); arXiv; GitHub; gilkalai.wordpress.com; Zenodo 24168178 (highlight only); 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-kozma-nitzan"}
{"premise": "Four-vertex graph A = {a1, a2}, p(o,a1) = p(a2,b) = 1, p(a1,a2) = 1/2: both points of A minimise P(x <-> b, o !<-> A) = 0, and a = a2 gives P(o<->b, o<->A) = 1/2 < 1 = P(o<->A, a2<->b)", "premise_status": "theorem", "premise_lean_source": "https://github.com/nitromannitol/percolation-after-anthropic (Proposition 9.1 per the manuscript; not built here)", "consequence": "Kozma-Nitzan Question 8 is false under the every-minimiser reading; the unique-minimiser case with |A| >= 3 and the existential-tie reading remain open", "consequence_ref": "Kozma-Nitzan, arXiv:2401.12397 v1, Question 8", "consequence_status": "open", "implication_source": "Bou-Rabee manuscript, Proposition 9.1, Theorem 9.4, Remark 9.5 (read through search highlights)", "effort": "S", "lean_exists": "claimed (not checked)", "in_1337": false, "class": 2, "notes": "residual open case is a 'question' the authors were 'rather hesitant' about; sibling percq.py covered connected n <= 6 (p = 1/2 and random p) and n = 7 (3 random draws) in double precision with no unique-minimiser violation", "novelty": "published", "novelty_searched": "Exa web search; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-kozma-nitzan"}
```
