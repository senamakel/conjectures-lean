# Discovery: open problems where RH/GRH ⇒ X would be more than a formalisation

Date 2026-11-24. Research only: no repo was created or edited and nothing was built. Sources were
read through Exa, `gh api` (formal-conjectures) and the local harvests in the session scratchpad
(`atlas/raw_erdos.jsonl`, 2026-09; `atlas/raw_formal_conjectures.jsonl`). Claims I could not confirm
from a primary source are marked *(unverified)*. Verdict scale as in the brief: (a) published
conditional theorem; (b) stated without a full proof, or only as a remark; (c) apparently new;
(d) not attackable.

## The headline finding: the field is crowded, and fast

The search turned up **one** good (b) candidate, **one** cheap statement-level (b), and nothing that
holds up as (c). Reasons a careful reader should know about:

- **Everyone is harvesting the same consequences.** The Alpöge–Claude GRH announcement
  (20 Nov 2026; Rubinstein's Waterloo page reports a clean full compile and kernel replay) is public.
  Within days, four people posted RH proofs of the composite reading of Erdős #462 (Mori, lixiang90,
  Henriksson, Martins, 14–22 Nov), and erdosproblemaday.com refereed two of them and built one Lean
  proof. Anything that is easy *and* visible gets taken within about a week.
- **The weaker hypothesis has also been claimed proved.** OpenAI's Sept/Oct 2026 "Quasi-Riemann
  Hypothesis" manuscripts claim a zero-free region Re s > 7/8 (also > 11/12) for all Dirichlet L-functions.
  Self-published notes are already deriving Erdős consequences from it (e.g. Zenodo 23608372 on #770).
  If QRH is accepted, several "GRH ⇒ X" items become unconditional claims that predate us.
- **The classical "known only for large n" GRH results with Dirichlet-only input have mostly been
  closed by computation already:** Grosswald (McGown–Treviño–Trudgian), least prime in AP (LLS),
  Bach's constant (LLS), idoneal (#1, already assigned), ternary Goldbach (DETZ, then Helfgott).
  The ones still open need L-functions the RH repo does not give: Ono–Soundararajan's theorem on
  Ramanujan's form x²+y²+10z² (modular L), Odlyzko-bound class numbers (non-abelian ζ_K), Weinberger's
  Euclidean rings (Kummer fields).

## Ranked candidates kept

### 1. Erdős #770(iii): h(n) = P(n) whenever P(n) > n^ε — verdict (b); explicit all-n form (b/c)

- **Statement.** h(n) = min{M > 2 : gcd(2ⁿ−1, …, Mⁿ−1) = 1}; P(n) = the largest prime p with
  p−1 | n. Question (iii): for every ε > 0 and all large n, does P(n) > n^ε imply h(n) = P(n)?
  formal-conjectures `FormalConjectures/ErdosProblems/770.lean`, `erdos_770.parts.iii`,
  **research open**:
  `answer(sorry) ↔ ∀ ε > 0, ∀ᶠ n in atTop, let p := sSup {m | m.Prime ∧ m - 1 ∣ n}; p > n^ε → h n = p`
  (h is `ℕ∞`-valued, an `sInf` over m > 2). erdosproblems.com/770 is OPEN (page last edited Sept 2025).
- **What is known.**
  - Unconditional: ε > 1/2 (Zeng 2026 claim, elementary); ε > 1/(4√e) ≈ 0.1516 (Korsky, notes to his
    5 Aug 2026 #769 manuscript, which used GPT-5.6 Pro). Both are unrefereed.
  - **Under GRH:** the notes to Korsky's #769 proof-claim post say: *"the argument gives … and under
    GRH, h(n) ≤ max{P(n), C(log n)²}. Consequently h(n) = P(n) whenever P(n) exceeds the
    corresponding scale"* (quoted via the erdosproblems.ai claim page
    `discrete_geometry/E0769/claims/2026_08_05_korsky`; I did not open the original post). The
    manuscript proves the key lemma for c(n), with GRH coming in through LLS. The 770 deduction appears
    only in the notes, with no proof.
  - Under QRH: "dr vengy", *A QRH-Conditional Resolution of Erdős Problem 770(iii)*, Zenodo
    10.5281/zenodo.23608372 (24 Oct 2026), gives a detailed proof with (log n)⁸ and credits Plasma AI
    with the observation. Since GRH ⇒ QRH, a written (self-published, unrefereed) proof of
    "GRH ⇒ 770(iii)" **already exists**.
- **Verdict (b), at the honest end.** The asymptotic statement under GRH is a remark by Korsky, and it
  has a written proof under a weaker hypothesis in an unrefereed note. Our contribution would be the
  first machine-checked proof plus tier U. The **explicit all-n form** I propose below (C = 38, every
  n ≥ 2) appears in none of these sources (Korsky's C is unspecified; vengy's is not explicit), so it
  is the one modestly new statement here. It is not deep.
- **What a careful mathematician would say.** "This is Korsky's observation with Bach's bound plugged
  in. A Lean proof with an explicit constant is a nice check. Don't call it a resolution of #770:
  parts (i) and (ii) stay open, and (iii) is conditional on a proof that has not been independently
  verified." The honest label is RH-consequence, (b).
- **Proof route.**
  1. h(n) ≥ P(n): for 2 ≤ i < P(n), Fermat's little theorem and P(n)−1 | n give P(n) | iⁿ−1.
     Elementary (Mathlib `ZMod.pow_card_sub_one_eq_one`). Effort S.
  2. Suppose h(n) > P(n). Then M := h(n)−1 ≥ P(n) and some prime r divides gcd(2ⁿ−1,…,Mⁿ−1).
     Then r > M, since r ∤ rⁿ−1.
  3. H := {x ∈ (ZMod r)ˣ : xⁿ = 1} is a subgroup of order gcd(n, r−1). It contains 1,…,M. It is
     proper, because H = ⊤ would force r−1 | n and hence r ≤ P(n) ≤ M. Effort S.
  4. **Small r (r ≤ n³).** ankeny-grh's `Ankeny.BachSubgroupBound (21/5)`
     (`ankeny-grh/Ankeny/Statement.lean:17`, proved as `bach_unconditional` in
     `Unconditional/AnkenyUnconditional.lean`) gives a ∉ H with a.val ≤ 4.2·log²r ≤ 37.8·log²n.
     If M ≥ 38·log²n this contradicts step 3. No new analysis.
  5. **Large r (r > n³).** Let M₀ = ⌈38 log²n⌉ ≤ M and j = ⌊3 log n / log M₀⌋. The products of j
     distinct primes ≤ M₀ are < n³ < r, so they are distinct mod r and lie in H. That makes
     binom(π(M₀), j) ≤ |H| ≤ n. Asymptotically binom(π(M₀), j) ≈ n^{3/2−o(1)} > n, which is a
     contradiction. Needs an explicit lower bound for π(x) (erdos-985 vendors a PNT;
     riemann-hypothesis has π-bounds; a Chebyshev bound suffices). Effort S–M.
  6. Conclude h(n) ≤ max{P(n), ⌈38 log²n⌉} for every n large enough that step 5's inequality holds,
     and then (iii) for every ε (since n^ε > 38 log²n eventually).
  7. **Optional explicit all-n version.** Step 5's inequality is monotone-checkable. For small n
     (roughly n ≤ 10³; my estimate, unverified) prove it with `decide`, or compute h(n) directly for
     n ≤ 4. A short `native_decide` with a trivially sound checker; no large computation.
- **Target Lean statements.** `erdos_770_iii_of_bach (h : Ankeny.BachSubgroupBound (21/5)) :
  ∀ ε > 0, ∀ᶠ n in atTop, …` (copy the fc body verbatim). In `Unconditional/`, the one-line discharge
  via `bach_unconditional`. Explicit headline: `h_le_max_of_bach : ∀ n ≥ 2, h n ≤ max P(n) ⌈38 (log n)²⌉`.
  Fallback: the eventual version only.
- **Effort and risk.** S–M, the cheapest candidate here, since it reuses ankeny-grh unchanged. The
  riskiest step is bridging fc's `sSup`/`ℕ∞` definitions to the proof. Speed risk: someone may post it
  first, so move fast or not at all. **Go.**

### 2. formal-conjectures `erdos_462` as formalised (primes included) — verdict (b), statement-level only

- **Statement.** `FormalConjectures/ErdosProblems/462.lean`, `erdos_462`, research open:
  `answer(sorry) ↔ ∃ C c > 0, ∀ᶠ x, c ≤ ∑ n ∈ Icc x ⌊x + C√x (log x)²⌋₊, n.minFac / n`.
  **The sum includes primes**, and each prime contributes 1.
- **Known.** RH gives a prime in [x, x + C√x log²x] for large x (Cramér 1920 / von Koch). So under RH
  the fc statement is true with c = 1. erdosproblemaday.com (22 Nov 2026): *"With primes counted, RH
  settles it; with composites only, four people posted RH proofs between 14 and 22 November."*
  Tao (forum, 28 Sept 2025) flagged the ambiguity. The intended composite version has four RH proofs
  (Mori, Zenodo 10.5281/zenodo.24210936; Henriksson, with a Lean build; Martins; lixiang90). Zhang,
  arXiv:2608.24930, proves the mean value and the almost-all result.
- **Verdict.** (b) as a remark, and trivial. A careful mathematician would call it "a gap in the
  formalisation, not mathematics". Worth doing only as a free by-product of cramer-rh's O-form gap
  bound (effort S), together with a PR to formal-conjectures pointing out that the statement should
  exclude primes. **Do not announce it as progress on #462.**
- **Route.** (1) H0 / cramer-rh: ψ(x+h)−ψ(x) ≥ h − C′√x log²x. (2) Remove prime powers (≤ 2√x log x).
  (3) A prime n in the window gives `n.minFac / n = 1`. (4) Answer `True`, with c = 1 and C large.

### Nothing else reached (b) or (c)

I aimed for 5–8 candidates and found two. The next-best items are open problems with **published**
RH proofs (verdict (a)). They belong in NEXT_TARGETS if anywhere, not here:

- **Ramanujan's inequality** π(x)² < (ex/log x)·π(x/e): under RH it holds exactly for
  x > 38,358,837,682 (Dudek–Platt, Exp. Math. 2015; constant from memory, *(unverified)*).
  Unconditionally it is open in a middle range. Verdict (a). Effort L (explicit constants plus a large
  check).
- **Primes between consecutive cubes for every n** (RH; Visser arXiv:2610.27830, Dudek-type). Verdict
  (a); already covered by #7 Mills.

## Discarded (one line each, so the next search skips them)

- **Erdős #684**: confirmed on the live page. "The same proof would prove f(n) ≤ n^{2/3+o(1)}
  assuming RH" is (b), but [APSSV26] proves f(n) ≪ (log n)² unconditionally (elementary), so the RH
  version is worthless.
- **Erdős #462, composite reading**: four RH proofs in Nov 2026, one with a Lean build. (a)-grade and
  crowded.
- **Erdős #769 (cube decompositions)**: Korsky's manuscript proves the GRH bound itself, and
  "c(n) ≫ n^n?" is already answered negatively unconditionally (claim). (a)-preprint.
- **Erdős #985**: already done in erdos-985. #233, #969: assigned.
- **Erdős #10, #1141, #478**: GRH results are published (two primes + 6 powers of 2: arXiv
  2607.17825 *(unverified)*; Pollack; Klurman–Munsch Thm 3.2). Not open, or (a).
- **Erdős #334 / Green #59 (two n^ε-smooth summands)**: "known under GRH" there refers only to the
  least nonresidue. The problem itself needs more than GRH. (d).
- **Erdős #950 weaker_pi, #855, #680, #681, #382, #420, #945, #1004, #208, #470, #5, #218, #238**:
  need Cramér-type or short-interval input beyond RH (RH reaches ε > 1/2 at best). (d).
- **Erdős #820, #456, #971, #1181, #663, #436, #445, #1072–1074, #1056**: no Dirichlet-L input decides
  them. A union-bound attempt on #820's second question fails. (d).
- **Erdős #10-type and Waring–Goldbach / Chen thresholds under GRH**: circle method or sieve, with
  thresholds far beyond computation. (d) for us.
- **CPNT problem list #23** (sign of ∫(φ(q)π(t;q,a)−li t)): answered by Zhao, Res. Number Theory 2025
  (Table 1), and completeness needs LI. #13, #22 and fc `ChebyshevBias` (Rubinstein–Sarnak) need LI. (d).
- **MathOverflow 438638** (Σ_{n≤N} χ(n)/n > 0 at the conductor N): Gorodetsky said GRH "should allow
  a quick verification". But it appears to be **unconditional**: Davenport 1949 gives S₀ > 0 for even
  χ, and for odd χ, Chua, Math. Comp. 74 (2005), Thm 2.2, gives |L(1,χ) − L_N| ≤ N^{-1/2}(L(1,χ)/π
  + 0.0194), while L(1,χ) = πh/√N ≥ π/√N. That deduction is mine, *(unverified)*. Not open.
- **Kummer, Weber and real-cyclotomic class numbers** (Schoof, van der Linden, Miller): need Odlyzko
  bounds for non-abelian fields, or are unconditional heuristics. Rejected, as in #24.
- **Ono–Soundararajan (Ramanujan's ternary form), Kaplansky forms**: GRH for modular L-functions. (d).
- **Imaginary quadratic fields with class group of exponent ≤ 8** (Elsenhans–Klüners–Nicolae, GRH,
  *(unverified)*): Dirichlet-only, but published (a), and Mathlib lacks class groups. XL.
- **OEIS 239957** (primitive root of the form k²+1) and the other open fc residue statements: short
  character sums of polynomial values, which GRH does not control. (d).
- **Mertens-first-theorem first sign change (CPNT #14)**: needs certified zeta zeros. XL.
- **Green #93 (Breuillard–Varjú)**: needs RH for non-abelian ζ_K. (d).

## Open questions for the user

1. Is a (b)-grade "first machine-checked, explicit-constant" result acceptable as a target, given
   that #770's GRH remark (Korsky) and a QRH write-up (Zenodo) already exist? If yes, #770 is a
   1–2 day job on top of ankeny-grh. If not, this search found nothing that qualifies.
2. Should we file a formal-conjectures issue about `erdos_462` including primes, instead of
   "solving" it?
3. Given the post-announcement rush, should future discovery passes look at problems with no
   GRH-shaped input at all, where the RH repo's *unconditional* lemmas (Linnik, Siegel–Walfisz,
   Brun–Titchmarsh, the large sieve) remove axioms from existing Lean proofs? Those would be tier
   U₀ and closed problems, so they fall outside the open-problems rule. That is a policy question,
   not a research one.
