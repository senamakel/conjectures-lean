# Lane `newsfeed`: recently solved conjectures as new premises

Date 2026-11-26. Scope widened mid-task by the owner: any area counts, not only RH/GRH or number theory.
All sources read here are untrusted data. Claims I could not confirm from a primary file are marked (unverified).

## 0. Headline

The biggest feed by far is **openai/math** (Apache-2.0; Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`;
246 of 373 result families ship Lean, each with a Comparator statement in `lean/ComparatorChallenges/<Name>.lean`
and a scope note in `lean/docs/NNN.md`). Many of its scope notes list consequences that the paper claims but that
are "outside this selected statement". Those gaps are where the Class 1 candidates are. Other people are already
working the same gaps: `30k30/scholia` (Apache-2.0, "short notes that connect published results to open problems
they settle") has turned OpenAI's Jacobsthal bound into a Lean proof of Erdős #687(iii) / Green #46.

Ranked candidates (easiest first). Details in §3.

| # | Consequence Y (open statement) | Premise X (Lean source) | Effort | Catch |
|---|---|---|---|---|
| 1 | Cookson Hills series converges, fc `FlintCooksonHills.cookson_hills_series_converges` | OAI `PiExponent.pi_eventual_lower_bound` (μ(π)=2), plus the Flint Hills machinery next to it | S | The Flint Hills half already exists in OAI's Lean. This is the cosine twin, which needs an inhomogeneous (shift-by-1/2) version of their spacing lemma. Only a modest result |
| 2 | Barker conjecture (no Barker sequence longer than 13), fc `Arxiv.«2104.00502».barker_conjecture` | OAI `CirculantHadamard.Barker.even_length_eq_two_or_four` (Lean) + Turyn–Storer 1961 for odd lengths (paper, classical) | M | The OAI paper already claims the full Barker conjecture in writing. What is new is the Lean proof of the odd half. Turyn–Storer has to be formalised from scratch (not found in Lean) |
| 3 | Non-sofic groups exist, fc `Green100.green_100.parts.i` (marked solved, `sorry`, no `formal_proof`) | OAI `OddKaplansky.main_theorem`: an injective, non-surjective linear cellular automaton on `K^G` with `K` finite. Plus Gromov–Weiss (sofic ⇒ surjunctive, written) | L | Gromov–Weiss surjunctivity for sofic groups is not in Mathlib or anywhere I found. It is about a page of counting, but the sofic and CA infrastructure has to be built. A famous question, and the answer is already announced (OpenAI, Fournier-Facio, Kun–Thom), so this would be the first Lean proof, not a new result |
| 4 | Forcing conjecture (Skokan–Thoma / Conlon–Fox–Sudakov) is false | OAI `SidorenkoCounterexample` (Lean) + "forcing ⇒ Sidorenko" (published, graph-limit argument) | M–L | No formal-conjectures statement exists, so we would have to state it ourselves. The OAI paper claims the consequence in writing |
| 5 | Erdős–Turán for primes: every set of primes with Σ1/p = ∞ contains arbitrarily long APs | OAI `ErdosReciprocal` (fc `erdos_3`, linked) | S (trivial) | A one-line specialisation, so too thin to count as a result. I found no open fc statement to attach it to |

Everything else I checked is either already in Lean, or needs inputs nobody has formalised. See §4 (rejected) and §5 (Class 2).

## 1. 1337isnot1337/solved-conjectures inventory (clone at 43152d52)

### 1(a) Do-not-repeat list
Every entry in `CONTENTS.md` on `main` is in `newsfeed-1337-inventory.md` (169 lines, one per entry: name, section,
Lean flag, path). The Lean code lives in `lean/Conjectures/*.lean` (Lean `v4.35.0`, Mathlib tag `v4.35.0`, MIT).
Lean status per entry is tracked in `docs/lean-status.md`. The collection is overwhelmingly combinatorics, special
functions and polynomial zeros: Ehrhart theory, Laguerre–Pólya, lonely runner, permanents, Lüroth sumsets, Stern
polynomials, Waring gaps and similar. Number-theory-flavoured entries: Benfield–Lippard Waring gaps (Lean), Hajdu–Sárközy
(Lean), Gravgaard–Lee Lüroth (Lean), Ulas square products (Lean), Pomerance–Sárközy fluctuations (Lean partial),
Ma–Tang subset sums (Lean), Erdős 607 (Lean), Batista Egyptian fractions (Lean), Hegyvári (written only).
The "Zeros of polynomial transforms" block (Nuttall [Lean], Coffey–Smith, Chaudhary–Khmiri–Mazhouda, Merlini–Sala–Sala,
Wang–Yang [written only], Csordas–Vishnyakova, Cardon–FPSW, Wagner, Vishnyakova [Lean]) is RH-adjacent.

There are about 260 other remote branches (`lean/*`, `review/*`). They are Lean work in progress on the same
entries (Pomerance–Sárközy, Novelli–Thibon, Cyrusian–Kaplan, Mazák–Zrubák, Shumyatsky, Nuttall, Wachs, Tom–Vailaya
and others), plus the `research` branch.

### 1(b) Listed as unresolved or wanted
- Partial results on open problems (CONTENTS §"Partial results"): wild number of K_n for 13 ≤ n ≤ 154; shifted lonely
  runner for 58 ≤ n ≤ 94; Steinke–Zakynthinou iid VC; Erdős essential component (2^m3^n); Erdős–Sauer; Bollobás–Erdős–Tuza;
  Erdős–Oler; Erdős–Granville–Pomerance–Spiro (full); Frankl (general); lonely runner (general); Erdős–Gyárfás
  (general); Hadamard order 2396.
- RH-transfer "unresolved" table (`research/rh-transfer/README.md` on branch `research`): Goldbach (spectral bridge),
  Gaiotto positivity, Kudra, Carmichael totient, Bellemare–Langlois–Ransford, Granville–Soundararajan, Erdős–Odlyzko–Sárközy,
  Chowla least prime, Martin, Resnikoff–Saldaña, Vandiver, Greenberg, Schneider/Jannsen/Soulé, Artin density,
  GRH for Hecke L, Selberg/Ramanujan/Artin/Fontaine–Mazur.
- The `research` branch's working catalogue has "Open complexity research" campaigns (BSS permanent, VP vs VNP and
  others). They take Anthropic's 2026-11-23 VP ≠ VNP result as a "standing research assumption".

### 1(c) RH-transfer inventory (branch `research`, `research/rh-transfer/`, 69 files, no Lean anywhere: "No Lean verification is performed")
24 named outcomes, each written only:
Nuttall (proved; note that main's CONTENTS does say Lean-complete), Coffey–Smith (disproved), Merlini–Sala–Sala (disproved),
Chaudhary–Khmiri–Mazhouda (disproved, interval certificate), Csordas–Vishnyakova (disproved; Lean on main), Cardon–FPSW
(disproved; Lean on main), Wang–Yang (disproved), Wagner (disproved; Lean on main), Pomerance 1974 nonexistence (via
Ford–Luca + GRH), Jutila character-sum moments (GRH), Fujii (oscillation, refutation of the reported equivalence family),
Banks–Friedlander–Luca–Pappalardi–Shparlinski (Carmichael λ: every value has at least 2 preimages; Ford–Luca under ERH),
Riffaut (singular moduli and trinomials; Bilu–Luca–Pizarro-Madariaga under GRH), Coffey upper bound, Keiper asymptotic,
Csordas–Dimitrov Laguerre inequalities, Brent mean, Robin, Nicolas, Soundararajan smooth-number equidistribution
(Banks–Shparlinski), Grosswald, Knapowski–Turán (refuted, Kaczorowski), Chebyshev bias (Abel-weighted), Lindelöf.
Explicitly excluded there as prior art: Vinogradov (QRH paper), Euler idoneal (QRH paper 2 + Liang), Patterson cubic
(OpenAI), Zhu xi log-concavity (Liu–Mao), Montgomery–Vaughan character sums, Ankeny–Artin–Chowla (Reinhart),
Hooley variance (Fiorilli–Martin), Artin infinitude (OpenAI 029 and others).
Robin, Nicolas, Grosswald, Lindelöf and idoneal overlap our finished projects. Pomerance, BFLPS, Riffaut, Jutila,
Soundararajan, Brent, Chebyshev, Knapowski–Turán, Keiper, Coffey and Csordas–Dimitrov are written only, so Lean
versions would not duplicate their Lean. They are still on their list, though, so the brief says do not repeat them.

## 2. Other feeds of 2026 solved results

| Feed | Lean? | Licence | Notes |
|---|---|---|---|
| openai/math (`lean/OAI/**`, `lean/ComparatorChallenges/`) | yes, 246 families | Apache-2.0 | Lean v4.34.1, Mathlib d13f23b7. Number-theory families with Lean: 003 QRH, 005 Catalan's constant irrational, 007 two-point Chowla/Elliott, 012 joint Dickman / P⁺(n) vs P⁺(n+1), 013 Ostmann, 015 torus packets, 017 μ(π)=2 + Flint Hills, 020 power-free polynomial values, 021 Jacobsthal, 023 Patterson, 024 totient count, 025 short Egyptian fractions, 026 large prime gaps, 028 Gaussian moat, 159 Erdős #3, 179 circulant Hadamard + even Barker, 182 Sárközy power saving. Many more in combinatorics, algebra, geometry, analysis and complexity (Kaplansky counterexamples, Sidorenko, Borsuk in dim 9, Hadwiger–Nelson ≥ 6, UGC, L = BPL, ETH disproof, …). |
| **QRH Lean code** | **yes** | Apache-2.0 | `OAI.LFunction_ne_zero_of_seven_eighths_lt_re` and `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in `OAI.NumberTheory.DirichletL.Nonvanishing`. Hecke L over Q(√−3) in `OAI.NumberTheory.DirichletL.Hecke.Nonvanishing`. Landau–Siegel gap `exists_absolute_real_zero_gap` in `OAI.NumberTheory.SiegelZeros.Main`. For us this is subsumed by riemann-hypothesis, except for Hecke over Q(√−3), where I found no open consequence. |
| anthropics/zeta-23-lean v1.0 | yes | (not checked) | More than 2/3 of ζ-zeros simple and on the line (fc `Paper/RiemannZetaZeros.lean`). The `_lt` and `_one_hundred` variants stay open. I found no short consequence. |
| 30k30/scholia | yes | Apache-2.0 | Same method as this lane. One item so far: Erdős 687(iii) from OAI Jacobsthal. |
| plby/lean-proofs (432 fc links), plby/Erdos90 | yes | (not checked) | Erdős 90 unit-distance disproof (n^{1+c}) in Lean. Do-not-repeat. |
| AxiomMath (gdm-formal-conjectures, TanArctan) | yes | MIT (TanArctan) | Borwein sine series, conditional on Zeilberger–Zudilin's bound for μ(π). Ono's tan-arctan results. |
| logical-intelligence/proofs, epoch-research/LeanOpenProblems-results, facebookresearch/atlas-lean, n-yamaguchi-0729/SawinTotallyRealTowers | yes | (not checked) | Seen as fc `formal_proof` targets. Not mined further. |
| formal-conjectures log (200 commits to 9097e2f) | n/a | Apache-2.0 | 2026-11-24 `6bc2f74`: RH/GRH set to solved, adding `erdos_233.variants.upper_bound_unconditional` (sorry) and `erdos_985` solved. Many "link a formal proof" commits in Nov 2026. |

Not checked, for lack of a working fetch or budget: erdosproblems.com recent changes, Lean Zulip / Lean blog / Xena posts.
GitHub code search ran out of rate limit partway through (the 2026-11-26 09:50 UTC quota).

## 3. Class 1 candidates in detail

### 1. Cookson Hills series (S)
- **Statement** (fc `FormalConjectures/Wikipedia/FlintCooksonHills.lean`, `@[category research open, question, AMS 40]`):
  ```lean
  theorem cookson_hills_series_converges :
      Summable (fun n : ℕ =>
        1 / ((((n + 1) : ℝ)^3) * (Real.cos (n + 1)^2))) := by
    sorry
  ```
- **Premise**: μ(π) = 2. Lean: openai/math `lean/OAI/NumberTheory/PiExponent/Main.lean`, `OAI.PiExponent.pi_eventual_lower_bound : PiEventualLowerBound`
  and `OAI.PiExponent.main`, with axioms limited to the standard three by the Comparator config `PiExponent.json`.
  The reusable machinery is in `lean/OAI/NumberTheory/PiExponent/Analysis/`: `FlintConsequence.lean`
  (`uniform_pi_distance_of_eventual_lower_bound`, `flintHills_summable_of_eventual_lower_bound`), `FlintSine.lean`, `DyadicSpacing.lean`,
  `summable_inverse_cube_integerDistance`, `flintHills_summable_of_distance_summable`.
- **Deduction**: |cos n| = |sin(n − π/2)| ≍ ‖n/π − 1/2‖. Near-zeros are n ≈ (2k+1)π/2, so the μ(π) bound applied
  to the denominators 2k+1 gives |cos n| ≫ n^{1−ν}. In a dyadic block, the points n/π − 1/2 mod 1 are separated by
  ≫ N^{1−ν}, again from μ(π), applied to differences. Summing 1/(j·sep)² over each block gives N^{2ν−2}, and dividing
  by N³ makes the block sums summable for ν < 2.5. This is the argument Alekseyev (arXiv:1104.5100) gave for Flint
  Hills. That the same argument handles Cookson Hills is my reading (unverified as a published statement).
- **Known unconditionally**: Cookson Hills convergence is open without μ(π) < 5/2 (MathWorld, Alekseyev) (unverified for Cookson).
- **Existing Lean**: Flint Hills only (`OAI.PiExponent.flint_hills_summable`, same file; fc still lists Flint Hills
  open, which is just a missing link). No Cookson Hills Lean found: GitHub code search for "cookson" turned up nothing in Lean,
  and "cookson" does not appear in openai/math.
- **Missing lemmas**: the shifted (inhomogeneous) versions of OAI's `FlintSine` and `DyadicSpacing` lemmas.
- **Finite computation**: none. **Port**: OAI is at Lean v4.34.1 and Mathlib d13f23b7, we are at v4.36.0 and fc4f59e5. Vendor the PiExponent tree (large: the μ(π) proof imports
  many modules) or depend on openai/math as a lake package.
- **Catch**: OAI did the hard part. This is a cheap but small result, and the paper's Flint Hills corollary makes the
  method obvious, so someone else may do it first.

### 2. Barker conjecture (M)
- **Statement** (fc `FormalConjectures/Arxiv/2104.00502/BarkerSequence.lean`, open):
  ```lean
  theorem barker_conjecture (a : List ℤ) (ha : IsBarkerSequence a) : a.length ≤ 13 := by
    sorry
  ```
- **Premise**: circulant Hadamard conjecture. Lean: openai/math solution for Comparator `EvenBarker.lean`:
  ```lean
  theorem even_length_eq_two_or_four {n : ℕ} (h : Fin n → ℤ)
      (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4
  ```
  (namespace `OAI.CirculantHadamard.Barker`; doc `lean/docs/179.md`). The odd part is "outside this selected statement".
- **Missing**: odd Barker sequences have length at most 13 (Turyn–Storer, Proc. AMS 12 (1961) 394–399). The proof is
  elementary (sign-pattern identities a_i a_{n−1−i} plus a case analysis), but has to be formalised from scratch. I did not find
  it in Lean (code search was rate-limited, so this is not exhaustive). Also needed: the `List ℤ` to `Fin n → ℤ` translation.
- **Literature**: OAI's 179 abstract states the full Barker conjecture as a consequence, in writing.
- **Catch**: the consequence is claimed in OAI's paper, so the Lean proof would be new but the result would not. That
  fits the rule that nothing here is new mathematics. Not in 1337.

### 3. Non-sofic groups exist (L)
- **Statement** (fc `GreensOpenProblems/100.lean`, marked `research solved` with `sorry`, no formal proof link):
  `theorem green_100.parts.i : ¬ ∀ (G : Type) [Group G], IsSofic G`, with `IsSofic` the Pestov 3.5 characterisation
  quoted in the file.
- **Premise**: openai/math Comparator `OddKaplansky.lean`, `OAI.OddKaplansky.main_theorem : MainClaim`, giving a finite field
  `K`, a finitely generated `G`, and `a b : MonoidAlgebra K G` with `a*b = 1`, `b*a ≠ 1`, `Function.Injective (cellular b)`
  and `¬ Function.Surjective (cellular b)`.
- **Deduction**: Gromov (1999) / Weiss (2000): sofic groups are surjunctive. A G-equivariant injective cellular automaton
  over a finite alphabet is surjective. The proof counts patterns over a sofic approximation. For linear CA there is a
  dimension-count version (Ceccherini-Silberstein–Coornaert) (unverified that it is simpler in Lean). Then `G` is not sofic.
- **Missing**: sofic approximations as used in fc's `IsSofic`, a finite-window CA framework, the counting
  argument, and a check that `cellular b` (right-multiplication convolution) is equivariant for the left shift.
- **Catch**: L effort. Already answered in 2026 preprints, so the value is that it would be the first machine check
  of a famous answer.

### 4. Forcing conjecture is false (M–L)
- **Premise**: openai/math `SidorenkoCounterexample` (doc 161). A bipartite H with 35 vertices and 66 edges, and a finite G
  with t(H,G) < t(K₂,G)^66. H has a cycle, since 66 > 34.
- **Deduction**: forcing graphs are Sidorenko (Conlon–Fox–Sudakov; Lovász) (unverified exact attribution).
  Equivalently, take a non-quasirandom sequence interpolating between G-blow-ups and random graphs, hitting
  t(H) = p^66 by continuity. OAI's doc 161: "The separate forcing-conjecture consequence in the paper is outside this statement."
- **Missing**: a definition of forcing, a quasirandomness statement, and the interpolation and continuity argument (graphons, or blow-ups
  with explicit densities). No fc statement exists.
- **Catch**: we would have to state the target ourselves.

### 5. Primes with divergent reciprocal sum contain long APs (S, trivial)
- Premise: fc `erdos_3`, linked to openai/math `lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean#L38`.
  Specialise it to subsets of the primes.
- Catch: a one-liner, and I found no open fc statement for it. I would record it, not pursue it.

## 4. Rejected edges (already in Lean, or not usable)
- Flint Hills series: `OAI.PiExponent.flint_hills_summable` already exists. fc lists it open only because the link is missing.
- Borwein sine series: AxiomMath `BorweinSineSeries/solution.lean` (fc marks it solved).
- Erdős 687(iii) / Green 46 from Jacobsthal: done by 30k30/scholia, and fc links the Lean.
- Erdős 978 (iii) n⁴+2 squarefree and Erdős 416 V(2x)/V(x) → 2: fc already links OAI's Lean.
- QRH ⇒ Vinogradov, idoneal, Miller and similar: subsumed by riemann-hypothesis GRH, and done here (weinberger-grh, lls-grh).
  The QRH paper is also prior art (1337's `qrh-prior-art.md`).
- Siegel-zero gap ⇒ anything: GRH already gives it.
- Artin infinitude (fc `artin_primitive_roots.parts.i`, open): OpenAI 029 claims it on paper only, with no Lean. Our
  artin-grh is at its ceiling. Class 2, XL.
- Two-point Chowla (OAI 007) ⇒ fc `chowla_liouville_conjecture` at k = 2: that is the premise restated, not a consequence.
  Corollaries like "λ(n) = λ(n+1) has density 1/2" are trivial and not listed open anywhere I found.
- Zeta-23 (2/3 simple zeros): no short open consequence found.
- Tan-arctan (Amdeberhan–Medina–Moll): has no Diophantine link to μ(π) that I could see.

## 5. Class 2 (premise claimed on paper only)
- OpenAI 029 (Artin infinitude for every base) ⇒ fc `artin_primitive_roots.parts.i` itself. The infinitude of full
  reptend primes (a = 10) would follow too, but I found no fc statement for it.
- 1337's written RH-transfer list (Pomerance 1974, BFLPS Carmichael-λ two preimages, Riffaut, Jutila): the premise X is a
  published GRH-conditional theorem (Ford–Luca, Bilu–Luca–Pizarro-Madariaga), with GRH itself Lean-proved. These
  are do-not-repeat per the brief. They are also XL, because the conditional theorems are not in Lean.
- OpenAI papers without Lean whose stated consequences are open problems (for example 006 Goldfeld, 011 prime factors of p−1,
  022 Duffin–Schaeffer inhomogeneous, 164 Hindman): not screened for elementary consequences, for lack of budget.

## 6. What I searched
1337: CONTENTS.md, HISTORY.md (sizes only), the `lean/` toolchain and licence, every remote branch name, and on `research`
the `research/rh-transfer/README.md`, `qrh-prior-art.md` and `analytic-applications.md`. formal-conjectures: PROOFS.md, `git log` since
2026-09, every `formal_proof` target host (grep), every fc file citing openai/math, sin/cos/tan-of-integer statements,
irrationality exponent, Barker, sofic, Chowla, Artin, squarefree n⁴, Erdős 3/89/90/604/687/978/416.
openai/math: CONTENTS.md, `lean/formalization.yaml`, all 248 `lean/docs/*.md` (scope notes), the Comparator statements for
about 25 number-theory items, OddKaplansky, CirculantHadamard and EvenBarker, and `PiExponent/Main.lean` and `Analysis/FlintConsequence.lean`.
GitHub code search: `flint_hills`, `FlintHills`, `cookson`, `flintHills_positive_summable_of_eventual_lower_bound`. Then the rate limit ran out:
sofic and surjunctive searches failed, so "not in Lean elsewhere" for Turyn–Storer and Gromov–Weiss is unchecked.
