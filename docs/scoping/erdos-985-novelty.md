# Erdős 985 under GRH: is it already in the literature?

Written 2026-11-24. Research only: no repo was edited and lake was not run. Every claim is
checked against a primary source unless it is marked (unverified).

**Short answer: yes.** "GRH ⇒ every odd prime has a prime primitive root `q < p`" follows at
once from Theorem 1 of McGown–Treviño–Trudgian (Funct. Approx. Comment. Math. 55(2), 2016,
215–225; arXiv:1508.05182). That theorem says the least prime primitive root satisfies
`ĝ(p) < √p − 2` for every prime `p > 2791` under GRH. For `p > 2791` we have `√p − 2 < p`, and
the primes `p ≤ 2791` are a trivial check. The implication has also been written down in so
many words online, since July 2026 at the latest. **The `new` label must not be used for
erdos-985.** The correct label is **RH-consequence**.

---

## 1. The problem

**erdosproblems.com/985** (read through Exa on 2026-11-24, because the live site sits behind a
Cloudflare challenge):

> Is it true that, for every prime $p$, there is a prime $q<p$ which is a primitive root modulo $p$?
>
> Artin conjectured that $2$ is a primitive root for infinitely many primes $p$, which Hooley
> [Ho67b] proved assuming the Generalised Riemann Hypothesis. Heath-Brown [He86b] proved that at
> least one of $2$, $3$, or $5$ is a primitive root for infinitely many primes $p$.

- Status: OPEN. erdosproblemaday.com (July 2026) and erdosproblems.ai (accessed 2026-09-04)
  both report the site's label as OPEN with 0 claimed proofs. I could not read the label on the
  live page myself because of the Cloudflare challenge.
- Erdős's source, as quoted by erdosproblems.ai: [Er65b], p. 233: *"As far as I know it is not
  even known whether to every $p$ there is a prime $q<p$ which is a primitive root of $p$."*
  Also [Er61e], p. 11. I have not seen the original (unverified).
- The page lists no references on prime primitive roots. It cites only Hooley and
  Heath-Brown, both on Artin's conjecture.
- **Discussion thread** (two comments):
  - Woett, 17 Aug 2025: `p > 2` is needed; a naive heuristic.
  - AronBhalla, 6 Mar 2026, an AI-generated summary from "GPT-5.4 Thinking": Nongkynrih
    (almost all `p`); Martin 1997 (under GRH, `G(p) ≪ (log p)^C` for all large `p`, "Under
    GRH this would therefore imply the statement of the problem for all sufficiently large
    p"); Oliveira e Silva's computations up to `10^14`. It ends with "the site has been updated
    to address this comment". The thread does **not** mention McGown–Treviño–Trudgian. It does
    not mention the workspace's result, and does not say that GRH implies the problem for
    *every* `p`.

**formal-conjectures** `FormalConjectures/ErdosProblems/985.lean` (last commit `7db2ea3b`,
2026-10-14):

```lean
/--
Is it true that, for every prime $p$, there is a prime $q \leq p$ which is a primitive root modulo $p$?
-/
@[category research open, question, AMS 11]
theorem erdos_985 : ∀ᵉ (p : ℕ) (hp_prime : p.Prime) (hp_nontrivial : p ≠ 2),
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  sorry
```

It has a variant `erdos_985.variants.two_three_five_primitive_root` (Heath-Brown, `research
solved`) and a TODO for Hooley. There is no GRH-conditional variant and no `formal_proof`
attribute. The docstring says `q ≤ p`, but the Lean statement has `q < p`.

## 2. What is already known

Write `ĝ(p)` (also written `G(p)` or `g*(p)`) for the least prime primitive root mod `p`.

### Under GRH

| Result | Source | Bearing on 985 |
|---|---|---|
| `g(p) ≪ ω(p−1)^4 (log ω(p−1)+1)^4 (log p)^2`, so `≪ (log p)^{6+ε}` | Shoup, Math. Comp. 58 (1992) 369–380 | about `g(p)`, not `ĝ(p)` |
| Shoup's bound also holds for `ĝ(p)` | Martin, *The least prime primitive root and the shifted sieve*, Acta Arith. 80 (1997) 277–288, p. 279; Cor. 3.1 per erdosproblemaday (number unverified) | gives 985 under GRH for `p` beyond an uncomputed threshold |
| Under ERH the least `q`-th power nonresidue is prime and `≤ 2(log p)^2`, plus explicit constructions; Lemma 2.1 is the weighted prime-sum estimate | Bach, *Comments on search procedures for primitive roots*, Math. Comp. 66 (1997) 1719–1727 | source of the analytic lemma; no statement about `ĝ(p) < p` |
| **Theorem 2.** For `p ≥ 10^9`, `ĝ(p) ≤ ((8/5)(2^{ω(p−1)} − 1) log p)^2` | McGown–Treviño–Trudgian (MTT), FACM 55(2) (2016) 215–225, arXiv:1508.05182 | fully explicit |
| **Theorem 1.** *"Assume GRH. Then ĝ(p) < √p − 2 for all primes p > 2791 and g(p) < √p − 2 for all primes p > 409."* | MTT, same paper | **gives 985 under GRH for all `p > 2791`** |

MTT's Theorem 1 for `ĝ` uses the computation of Cohen–Oliveira e Silva–Trudgian, *On
Grosswald's conjecture on primitive roots*, Acta Arith. 172(3) (2016) 263–270,
arXiv:1503.04519, §4: *"It was found that ĝ(p) < √p − 2 for 2791 < p < 2.5 × 10^15."* So the
GRH statement for `ĝ` is published in full: analysis for `p ≥ 2.5·10^15` and computation below.
The analytic input is MTT's Lemma 1 (Bach), which MTT describe as *"easily established
following the proof of Lemma 2.1 in [Bach]"*. They give no proof of it. That is the one gap in
the published record (see §3).

### Unconditional

- Ha, *On the least prime primitive root*, J. Number Theory 133(11) (2013) 3645–3669:
  `ĝ(p) ≪ p^{3.1}`, uniformly. The exponent is above 1, so it does **not** give `ĝ(p) < p`,
  even for large `p`.
- Linnik's theorem gives `ĝ(p) ≪ p^{L}` (Greg Martin, MathOverflow 112594, cites `p^{5.2}`).
- Martin 1997 Thm 1 and Nongkynrih (Acta Arith. 72 (1995) 45–53): `ĝ(p) ≤ (log p)^{C}` for
  all `p ≤ Y` outside `O(Y^ε)` exceptions, so the statement holds for almost all `p`. The
  exceptions are not named, so this settles no particular prime (secondary sources; I did not
  read these papers).
- Under a Siegel zero, Martin: `ĝ(p) ≪ p^{3/4+ε}` (via Ha's thesis; unverified).
- Computation: Oliveira e Silva tested every prime up to `10^14` (largest `ĝ` is 617), per the
  archived page that erdosproblemaday reports (unverified by me). COeST verified
  `ĝ(p) < √p − 2` for `2791 < p < 2.5·10^15` (primary). The workspace's own Lean check covers
  `p < 10^8`.
- Carella's claimed unconditional proofs (IJMCS 2015; arXiv:2509.19309) are refuted in detail
  by erdosproblemaday §2.5. I did not audit them myself. They are not accepted results.

So **unconditionally the problem is open even for all sufficiently large `p`**, and "open"
here means the whole statement, not only a finite range. Cohen–Trudgian, J. Number Theory 170
(2017) 10–16 (arXiv:1602.02440), §1:

> *"It is not known whether ĝ(p) < p for all p, or even for all sufficiently large p. The best
> unconditional result is due to Ha, namely, that ĝ(p) ≪ p^{3.1}. On the Generalised Riemann
> Hypothesis it is known that ĝ(p) ≪ (log p)^{6+ε}, and, recently, it was shown in [MTT]
> that ĝ(p) < √p − 2 for all p > 2791."*

### The key question: is "GRH ⇒ Erdős 985" published?

**Yes, as an immediate corollary of a published theorem**, and it has been stated outright
online. In detail:

1. **MTT Theorem 1 (2016, refereed) proves a strictly stronger statement for `p > 2791`.** The
   sentence that settles it:
   > *"Assume GRH. Then ĝ(p) < √p − 2 for all primes p > 2791 …"*

   Since `√p − 2 < p`, the conclusion for `p > 2791` is a one-line deduction. For the 405 odd
   primes `p ≤ 2791`, `ĝ(p) ≤ 53 < p`. I checked this with a few lines of Python this session;
   the maximum is `ĝ(2791) = 53`, matching the record tables in Western–Miller 1968 and
   Paszkiewicz–Schinzel 2002. Neither MTT nor COeST mention
   Erdős's question.
2. **The deduction has been written out explicitly.** erdosproblemaday.com/report/985 (dated
   2026-07-28, four months before the workspace paper), §2.3:
   > *"An explicit later result is stronger: K. McGown, E. Treviño, and T. Trudgian, Resolving
   > Grosswald's conjecture on GRH, arXiv:1508.05182, Theorem 1, proves G(p) < √p − 2 (p > 2791)
   > under GRH. Together with the finite check below, this proves (E985+) under GRH. It is not
   > an unconditional solution."*

   And §6: *"GRH proves it for every odd prime."* This is a web report, not a refereed paper,
   but it is public, dated and specific.
3. Morgan Hunter's ANU thesis, *The Least Square-free Primitive Root Modulo a Prime* (2016),
   puts Erdős's question ("do all primes p have a prime primitive root less than p?") on the
   same page as MTT's `ĝ(p) < √p − 2 (p > 2791)` on GRH. It does not draw the conclusion
   explicitly. I read this in an Exa extract.
4. Before MTT, the GRH result for large `p` was folklore through Martin 1997 (MathOverflow
   112594, 2012: *"the word 'almost' can be removed if we assume GRH"*).
5. Zenodo notes by "dr vengy" (2026-10-24, not refereed) claim 985 for large `p` under the
   weaker Quasi-RH (`Re s > 7/8`), with a threshold of `10^41`. Not checked. If correct, a
   weaker hypothesis than GRH already gives the large-`p` case.

The workspace paper itself (`erdos-985/paper/erdos985.tex`, §1) already says: *"McGown,
Treviño and Trudgian proved under GRH the stronger statement that the least prime primitive
root is below √p − 2 for all p > 2791 … Our argument follows their strategy but is simpler."*
The paper cites the result that makes its own theorem a corollary, without saying so. A reader
will notice this at once.

## 3. Genuineness verdict

**(a) Published conditional theorem, which we formalise. Label: RH-consequence.**

Strictly, the literature has the stronger statement (MTT Thm 1, `p > 2791`) and leaves the
final step to the reader: `√p − 2 < p` plus a table for `p ≤ 2791`. No referee would accept
"GRH ⇒ Erdős 985" as a new theorem. They would call it an immediate corollary of MTT 2016, and
the erdosproblemaday report shows it has already been noticed publicly. Announcing it as new
would be exactly the embarrassment the user wants to avoid.

What the workspace does add, honestly stated:

1. **The first machine-checked proof** of the GRH-conditional statement (tier C), and of the
   unconditional form given the unverified riemann-hypothesis repo (tier U). "First in Lean"
   needs its own search before it is claimed: formal-conjectures has no `formal_proof` on 985.
   I did not search GitHub for other Lean proofs.
2. **A complete written proof of MTT's Lemma 1 (Bach) with MTT's constants.** MTT only say it
   is "easily established following the proof of Lemma 2.1 in [Bach]". The paper's §4, and its
   Lean formalisation, supply that proof in full: Hadamard product, weighted Perron, zero sum at
   `s = 3/2`. That is a modest, real contribution to rigour, of type (b) for this lemma alone.
   Do not oversell it: it is the standard Bach argument.
3. **A route with a smaller computation.** Because the target is `q < p` rather than
   `q < √p − 2`, the analysis closes at `10^8` with no sieve, instead of MTT's sieve plus COeST's
   `2.5·10^15` computation. This makes it a convenient proof to formalise. It is not new
   mathematics: the argument is MTT's proof of their Theorem 2. The "indicator with the sharp
   constant `2^ω − 1`" is also not new. MTT's display before Theorem 2 already carries
   `(2^{ω(p−1)} − 1)`, coming from the `2^ω − 1` squarefree `d > 1`, each contributing
   `φ(d)·(1/φ(d))`. The product-form derivation is a presentational variant.

The README and paper also overclaim, separately from novelty, and need correcting:

- README line 4: *"This project proves in Lean that it does"*. This states Erdős 985 as proved
  outright. It breaks the workspace rule that nothing is "solved" on the strength of
  riemann-hypothesis.
- Paper title: *"…a formalized proof of Erdős Problem 985"*. Same problem, and the abstract
  calls the unconditional statement "an unconditional formal statement" without the
  verification caveat.
- Paper §1: the theorem should be presented as a corollary of MTT Theorem 1, and the paper
  should say so.
- `docs/LITERATURE_STATUS.md` ("The one candidate for 'new'") and `AGENTS.md` ("With one
  possible exception …") should both be resolved to: no candidate. erdos-985 is
  RH-consequence, following MTT 2016.

### Proposed "status in the literature" paragraph for the erdos-985 README

> **Status in the literature.** Erdős Problem 985 is open: unconditionally it is not even
> known that every sufficiently large prime has a prime primitive root below `p` (the best
> uniform bound is Ha's `ĝ(p) ≪ p^{3.1}`, J. Number Theory 133 (2013)). The implication proved
> here, "GRH for Dirichlet L-functions implies Erdős 985", is not new: it is an immediate
> corollary of Theorem 1 of McGown, Treviño and Trudgian, *Resolving Grosswald's conjecture on
> GRH*, Funct. Approx. Comment. Math. 55 (2016) 215–225 (arXiv:1508.05182). Under GRH that
> theorem gives a prime primitive root below `√p − 2` for every prime `p > 2791`, and the
> primes up to 2791 are a finite check. Our proof follows the argument of their Theorem 2, with
> the search range `[1, p)` in place of `[1, √p − 2)`, so the analysis closes at `p ≥ 10^8`
> without their sieve and the rest is a machine check. What this repository adds is a Lean
> proof: `erdos_985_of_GRH`, with GRH as an explicit hypothesis (label **RH-consequence**,
> tier C), including a complete proof of the Bach-type estimate that McGown–Treviño–Trudgian
> state as their Lemma 1 without proof. `Unconditional/` derives `erdos_985` from the Lean proof
> of GRH in leanprover-community/riemann-hypothesis, which has not been independently
> verified, so Erdős 985 should not be described as solved.

## 4. Proof route

Nothing to scope: the proof is finished in `erdos-985/` (no `sorry`; the README reports
`#print axioms` as the standard three plus 20 `native_decide`; not rebuilt on this box). For the
record, the route matches MTT's Theorem 2:

1. Indicator inequality, `Erdos985/Indicator.lean`. With no prime primitive root `< x ≤ p`,
   `S₀(x) ≤ (2^ω − 1)·max_{χ≠χ₀}|S_χ(x)|`. This is MTT's §2 display with the same constant.
2. Bach's bounds under GRH, `Erdos985/Analytic/`: `|S₀(x) − x/2| ≤ √x/20 + 3` and
   `|S_χ(x)| ≤ c(p,x)√x log p`. This is MTT Lemma 1, proved here in full.
3. Numerics for `p ≥ 10^8`, `Erdos985/Numerics.lean`, in three cases on `ω(p−1)`; the tight case
   `ω = 9` has about a 4% margin.
4. Finite check for `p < 10^8`, `Erdos985/Compute.lean`, with a checker proved sound and 20
   `native_decide` chunks.

An even shorter route exists. The workspace's `grosswald-grh` already has
`Grosswald.prime_primitive_root_of_GRH_large`, MTT's `ĝ` statement for `p > 2.5·10^15`. It does
not cover `p ≤ 2.5·10^15` without the COeST computation, so erdos-985's own route is the right
one to keep.

## 5. Target Lean statements

Unchanged. `Erdos985/Statement.lean` already matches formal-conjectures `erdos_985` verbatim
(`p ≠ 2`, `q < p`) and takes `hGRH : DirichletLNonvanishingRightOfHalf` copied from
riemann-hypothesis `src/Statements.lean`. Optional, purely to align the docs with the literature
(not a new target): a Lean corollary `ĝ(p) < p` stated as "MTT Theorem 1 ⇒ Erdős 985". It adds
nothing mathematically.

## 6. Effort and risk

- Effort: S. Only the README, paper and workspace docs need editing; no Lean work.
- Risk: the only real risk is reputational. The README and paper currently suggest both that
  the problem is solved and that the conditional theorem is new. A referee or an
  erdosproblems.com moderator would reject both claims, pointing to MTT 2016 and to the public
  erdosproblemaday report of July 2026.
- **Recommendation: no-go on the `new` label. Go on relabelling** erdos-985 as
  RH-consequence, following McGown–Treviño–Trudgian 2016, before anything is announced.

## 7. Open questions for the user

1. Retitle the paper? Suggested: *"A formal proof in Lean that GRH implies Erdős Problem 985"*,
   with an abstract that cites MTT Theorem 1 as the source of the implication.
2. Should the README keep "the first machine-checked proof"? If so, someone has to search
   GitHub, Zulip and the Lean community for other formalisations first. I did not.
3. Before any public post, should we leave a comment on the erdosproblems.com thread? It
   currently cites only Martin's ineffective bound, and pointing to MTT Theorem 1 would be a
   neutral contribution that doesn't overclaim.
4. The Quasi-RH notes on Zenodo (2026-10-24) are unrefereed. Should they be checked? If right,
   they would mean even a weaker hypothesis than GRH settles the large-`p` case.

## Sources read

- MTT, arXiv:1508.05182 (full text) and author PDF dated 2016-02-21 (Treviño's site); Crossref:
  FACM 55(2) 215–225, Dec 2016.
- Cohen–Oliveira e Silva–Trudgian, arXiv:1503.04519 (§1, §4); Acta Arith. 172(3) 263–270.
- Cohen–Trudgian, arXiv:1602.02440 (§1); J. Number Theory 170 (2017) 10–16.
- Bach 1997, Math. Comp. 66, 1719–1727 (abstract, §§1–4 via the AMS page).
- Ha 2013, JNT 133(11) 3645–3669 (via the 2014 Stanford thesis, Thm 2.1); Crossref metadata.
- erdosproblems.com/985 and its thread (Exa extract); formal-conjectures `985.lean` (gh api).
- erdosproblemaday.com/report/985 (curl, full text); erdosproblems.ai wiki E0985 (Exa extract).
- MathOverflow 112594; Hunter 2016 ANU thesis (Exa extract); Zenodo 23621867 and 23623383
  (abstracts only).
- Workspace: `erdos-985/README.md`, `Erdos985/Statement.lean`, `paper/erdos985.tex`,
  `docs/LITERATURE_STATUS.md`, `AGENTS.md`, `grosswald-grh/README.md`; LivingBrain search (no
  earlier note on novelty).
