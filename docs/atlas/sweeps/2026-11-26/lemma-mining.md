# Lane `lemma-mining`: intermediate lemmas of big Lean proofs, matched to open statements

Date 2026-11-26. Research only: nothing was built, no `#print axioms` was run. "File sorry-free" means
a grep of that one file. Scope follows the owner's update: any area counts, not only RH/GRH.

Supporting inventories written in this lane (read them for quoted statements and paths):
- `lm_external_inventory.md`: PNT+, teorth/IEANTN, FLT, Carleson, PFR, equational theories, sphere
  packing (math-inc), LeanAPAP, Kakeya, ExponentialRamsey, Brownian motion, RiemannHypothesisCurves,
  empty hexagon, Erdős-proof repos. Toolchain, licence and 5–15 quoted lemmas per project.
- `lm_local_inventory.md`: 1337isnot1337/solved-conjectures Lean (lonely runner, Frankl, Hadamard,
  Pomerance–Sárközy, distance graphs) and formal-conjectures' `FormalConjecturesForMathlib`.
- `lm_plby/`: tree listing, `Axioms.lean` and headline Util files of **plby/lean-proofs**, a 2026
  AI-produced proof repository (about 210 Erdős problems, 45,676 files) that the other lanes only
  cite as a `formal_proof` source. Its reusable library is inventoried in section C below.

## Headline

The second pass on riemann-hypothesis found nothing that the 2026-11-24 inventory missed and that
unlocks an open statement. The other big proofs are full of strong lemmas (Maynard–Tao, Linnik,
Weil bound for hyperelliptic curves, PFR over ℤ^d, Kelley–Meka over 𝔽_q, Cohn–Elkies in every
dimension, explicit Chebyshev and Brun–Titchmarsh), but every open statement they touch needs more
than the lemma. Under the open-problems-only rule, the lemma-mining yield is low, and the honest
result is: **no class-1 edge settles an open statement.** The cheapest real outputs are two class-2
hubs where the "big-proof" input is a Mathlib or CRT lemma, and neither deduction exists in Lean
anywhere I could find:

| Rank | Candidate | Premise X | Open consequences (formal-conjectures) | Class | Effort |
|---|---|---|---|---|---|
| 1 | Firoozbakht ⇒ Oppermann ⇒ (Legendre, Brocard); Firoozbakht ⇒ Andrica | Firoozbakht (open) | `Oppermann.oppermann_conjecture`, `Andrica.andrica_conjecture`, then fc's own proved `oppermann_implies_legendre` / `oppermann_implies_brocard` | 2 | S |
| 2 | Dickson ⇒ every admissible pattern occurs as consecutive primes | Dickson (open) | `erdos_141`, `erdos_141.variants.eleven`, `.infinite_three`, `.infinite_general_case`; `erdos_218.variants.infinite_equal_prime_gap`; `BalancedPrimes.balanced_primes`, `.balanced_primes_order` (7 open statements) | 2 | S–M |
| 3 | WOWII Conjecture 84, case δ ≥ 2 | none (fc's own geodesic lemma) | `conjecture84` restricted to `2 ≤ G.minDegree` | 1 (partial) | S |
| 4 | Lonely runner for ≤ 6 runners, real speeds | solved-conjectures `five_speed_lonelyRunnerBound` | `lonely_runner_conjecture` for `n ≤ 6` | 1 (known case) | M |

Everything else is in "Rejected" with a reason, and all of it is in `lemma-mining.edges.jsonl`.

---

## A. Second pass on riemann-hypothesis (`507a75d91d`)

Method: keyword counts over all `.lean` files (Burgess, Pólya–Vinogradov, subconvexity, zero
density, Bombieri, Vaughan, Barban–Davenport–Halberstam, Minkowski bound, Odlyzko, Selberg/Brun
sieve, Weyl/van der Corput, Kloosterman, Ramanujan–Petersson, Sato–Tate, Gallagher, Montgomery,
Halász, Chowla, mean values, moments, large sieve), then reading the statements behind each hit
and checking each against `docs/rh-lemmas/`.

- **Zero hits:** Burgess, Pólya–Vinogradov, subconvexity, Bombieri, Vaughan, Barban–Davenport–
  Halberstam, Odlyzko, Selberg or Brun sieve by name, Ramanujan–Petersson, Sato–Tate, Montgomery,
  Halász. So there are still no character-sum bounds beyond the large sieve, and no Type I/II
  machinery.
- **Name ≠ content, again:** the 20 "Kloosterman" files
  (`Formalism/HermitianCurvature/HermitianCurvatureProofs/KloostermanDensity.lean`,
  `…/CokernelGLCounts/RankPointCounts/KloostermanCosetSumLe.lean`) are internal `D7` lattice-count
  bounds, not Kloosterman sums. `ReciprocityTheory/…/PieriRules/WeylSum.lean` is a Weyl character
  sum, not an exponential sum.
- **Under-used but real, all already in the inventory:**
  - `zero_density` (`Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogFreeZeroDensityDirichletOneModulus.lean:327`):
    `∃ A C η, … ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ))`
    for `1 − η ≤ σ ≤ 1`. Log-free density for one modulus, with existential A.
  - `zero_density_mult` (`…/GlobalInterpolation/ReLtOneOfZero.lean:42`): at most `C·Q^{1/4}` zeros
    (with multiplicity) of primitive L-functions of conductor ≤ Q in `Re ≥ 1 − 1/400`, `|Im| ≤ Q`.
  - `QH.twistK` (`Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean:158`): Jacobi-symbol
    sums over primes in a progression are small except for one modulus.
  - `exists_short_vector_minkowski`, `minkowski_discriminant_ineq`
    (`Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean:262,238`),
    `minkowski_det_bound_posDef`: Minkowski lattice lemmas on Mathlib `IsZLattice`.
  - Chowla–Selberg (`GlobalTheory.T.chowla_selberg_period`, `ChowlaSelbergPeriodStatement.lean:14`).
- **Verdict.** Under GRH, which the repo also proves, zero-density statements near σ = 1 add
  nothing. Unconditionally they give only results that are already theorems (Linnik, weak
  Bombieri–Vinogradov), which the open-problems-only rule excludes. No open formal-conjectures or
  Atlas statement has any of these as its missing input. Edges recorded as rejected.

## B. Ranked candidates

### 1. Firoozbakht ⇒ Oppermann, and so Legendre and Brocard; Firoozbakht ⇒ Andrica (class 2, S)

- **Statements** (all `research open` in fc):
  - `FormalConjectures/Wikipedia/Firoozbakht.lean`, `firoozbakht_conjecture (n : ℕ) : firoozbakhtSeq (n+1) < firoozbakhtSeq n`,
    where `firoozbakhtSeq n := (n.nth Prime)^(1/(n + 1) : ℝ)`.
  - `Wikipedia/Oppermann.lean`, `oppermann_conjecture (x : ℕ) (hx : 2 ≤ x) : (∃ p ∈ Ioo (x * (x - 1)) (x^2), p.Prime) ∧ (∃ p ∈ Ioo (x^2) (x * (x + 1)), p.Prime)`.
  - `Wikipedia/Andrica.lean`, `andrica_conjecture (n : ℕ) : Real.sqrt ((n+1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1`.
  - fc already **proves** `oppermann_implies_legendre` and `oppermann_implies_brocard`
    (`Oppermann.lean:64,106`, category textbook, no `sorry`). So one new edge `oppermann_of_firoozbakht`
    closes Legendre and Brocard under Firoozbakht too.
- **Deduction (my own, to check).** Write p = p_n. Firoozbakht iterated gives p_{n+1} < p^{1+1/(n+1)}
  with fc's indexing, so g_n < p(p^{1/(n+1)} − 1) ≤ p(exp(log p/π(p)) − 1). Mathlib at the pin has
  `Chebyshev.theta_ge` (`θ n ≥ n log 2 − log(n+1) − 2√n log n`) and `theta_le_pi_mul_log`
  (`θ n ≤ π n · log n`), so π(p) ≥ c·p/log p with c ≈ 0.69 for large p. Hence g_n ≲ 1.45 log²p.
  - Oppermann needs a gap below about √p near x², and 1.45 log²p < √p once p ≳ 5·10⁴ (estimate).
  - Andrica needs g_n < 2√p_n + 1: the same threshold.
  - Below the threshold, a finite check: Oppermann for x up to a few hundred, Andrica for primes up to
    about 10⁵. Both are `decide`/`native_decide` sized. The exact threshold has to be computed with
    the error terms in `theta_ge`, which are large for small n.
- **Big-proof input.** Mathlib's `NumberTheory/Chebyshev.lean` (in the workspace pin). Neither PNT+'s
  Dusart file (33 `sorry`) nor plby's `dusart_pi_lower` (an `axiom`) is needed.
- **Literature.** "Firoozbakht implies Andrica, Legendre, Brocard, Oppermann" is attributed to
  Ferreira–Mariano (unverified; I did not open the paper). The fc-scan lane recorded only the Kourbatov
  consequence `firoozbakht_conjecture_consequence` (M, needs p_n > n log n). This route avoids that.
- **Existing Lean.** `gh search code` for "firoozbakht" (Lean) hits only fc. For "andrica" it hits fc
  and `davidleon/Gaseous-Prime-Universe` `core_formalization/Conjectures/Andrica/ILDA_Lemmas.lean`
  (not opened; check it before starting). Not in solved-conjectures CONTENTS.md.
- **Catch.** Firoozbakht is open and believed only heuristically (it contradicts some Cramér-type
  models for huge gaps), so the result is a tier-C link between open conjectures. The fc entries
  `*.ferreira_large_n` cite arXiv:2307.08725 as proving Legendre, Andrica, Brocard and Oppermann for
  large n. That claim is not accepted in the literature as far as I know (unverified). Do not build
  on it.

### 2. Dickson ⇒ consecutive-prime patterns: one CRT hub, seven open statements (class 2, S–M)

- **Statements:**
  - `ErdosProblems/141.lean`: `erdos_141 : ∀ k ≥ 3, ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k`,
    `.variants.eleven`, `.variants.infinite_three : (consecutivePrimeArithmeticProgressions 3).Infinite`,
    `.variants.infinite_general_case`. All `research open`.
  - `ErdosProblems/218.lean`: `erdos_218.variants.infinite_equal_prime_gap : {n | primeGap n = primeGap (n + 1)}.Infinite` (open).
  - `Wikipedia/BalancedPrimes.lean`: `balanced_primes : {n : ℕ | Prime ((Nat.nth Prime n + Nat.nth Prime (n + 2)) / 2)}.Infinite`,
    and `balanced_primes_order` (all orders k). Both open. A prime strictly between p_n and p_{n+2}
    must be p_{n+1}, so `balanced_primes` is the equal-gap statement again.
- **Premise.** `Dickson.dickson_conjecture (fs : Finset ℤ[X]) (hfs : ∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) (hfs' : SchinzelCondition fs) : Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}`,
  used as `(h : type_of% Dickson.dickson_conjecture)`, as `erdos_891.variants.weisenberg` already does.
- **Hub lemma.** For an admissible offset set H ⊆ [0, L], Dickson gives infinitely many m such that
  m + h is prime for every h ∈ H and m + j is composite for every other j ∈ [0, L]. So the primes in
  [m, m+L] are exactly m + H, and they are consecutive. Construction:
  - give each non-offset j its own prime q_j > L;
  - let M be the product of all primes ≤ L and all q_j;
  - choose c by CRT with c ≡ −j (mod q_j), and c + h ≢ 0 (mod p) for p ≤ L (possible by admissibility);
  - take the forms f_h = M·X + (c + h).

  SchinzelCondition holds: for p | M by the choice of c, and for p ∤ M because then p > L ≥ |H|.
  Irreducibility of a linear form needs gcd(M, c + h) = 1, which the CRT choice gives. For x ≥ 1,
  M·x + c + j is a proper multiple of q_j.
- **Instantiations.**
  - k-term CPAP: H = {0, d, …, (k−1)d} with d = ∏_{p≤k} p, which is admissible.
  - Equal gaps: H = {0, 6, 12}.
  - Balanced primes of order k: the symmetric admissible set {iP : |i| ≤ k} with P = ∏_{p ≤ 2k+1} p,
    shifted. Symmetry gives 2k·p_n = Σ(p_{n−i} + p_{n+i}).
- **Literature.** Folklore. The k-tuples conjecture ⇒ CPAP-k is stated on erdosproblems.com/141 and
  in Wikipedia's CPAP section (not re-read today). FC's 218 docstring records the 218 ⇔ 141(3)
  equivalence.
- **Existing Lean.** `gh search code` for "balanced_primes", "dickson_conjecture" and "erdos_141"
  (Lean) hits only formal-conjectures. Not in solved-conjectures. The other lanes list only the
  trivial Dickson specialisations (twin, cousin, sexy, Sophie Germain), the Erdős 891 variants and
  Erdős 647.
- **Missing.** The CRT construction with Finset bookkeeping. The `Nat.nth Nat.Prime` index of m + h
  (use `Nat.count` and the composite gaps). A decidable admissibility check for the concrete H.
  No finite computation.
- **Catch.** Dickson is open, so this links open problems only. The value is breadth: seven fc
  statements, and the hub is reusable for any "pattern of consecutive primes" OEIS conjecture.

### 3. WOWII Conjecture 84 for minimum degree ≥ 2 (class 1, partial, S)

- **Statement.** `WrittenOnTheWallII/GraphConjecture84.lean`, `conjecture84 (G) (h : G.Connected) (hδ : 0 < G.minDegree) : 2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ)` (research open, WOWII status O).
- **Lemma.** fc's own `Walk.induce_support_isTree_of_length_eq_dist` (an induced geodesic is an induced
  tree), from `FormalConjecturesForMathlib` (see `lm_local_inventory.md`, item 6).
- **Deduction.** For δ ≥ 2: 2·rad/δ ≤ rad ≤ diam < diam + 1 ≤ tree(G).
- **Catch.** This is the trivial half. The δ = 1 case needs tree(G) ≥ 2·rad(G). C_{2k} with one
  pendant vertex attains equality, so the case is tight, and I do not know whether it is true.
  Before anything else, run a brute-force search over small connected graphs with δ = 1 (cheap). A
  partial variant is not "done" under the workspace rules.

### 4. Lonely runner for at most 6 runners, real speeds (class 1, known case, M)

- **Lemma.** solved-conjectures `Loneliness.Renault.five_speed_lonelyRunnerBound` and
  `Loneliness.Modular.FiveRunner.five_runner_bound : CoordinateSubspace.LonelyRunnerBound 5`
  (integer speeds, file sorry-free, MIT licence, Lean v4.35.0).
- **Target.** fc `LonelyRunnerConjecture.lonely_runner_conjecture` (real speeds, `Fin n ↪ ℝ`) for n ≤ 6.
- **Missing.** The reduction from real to integer speeds (Bohman–Holzman–Kleitman; Henze–Malikiosis;
  not checked). It is not in solved-conjectures. Also the translation from "runner r lonely among n"
  to "n − 1 speed differences".
- **Catch.** Six runners is a known theorem (Bohman–Holzman–Kleitman 2001; Renault 2004), and seven
  is Barajas–Serra 2008. The labels are *known*, so this fails the open-problems-only rule. It is a
  formalisation project, not a target.

## C. Big-proof libraries worth knowing (inventory, no open target found)

- **plby/lean-proofs** (`src/latest`, Lean v4.33.0, Mathlib v4.33.0). The licence covers only "some
  files" (Apache-2.0); the rest is unlicensed, so import only.
  - `ErdosProblems/Axioms.lean` re-exports **proved** theorems: `maynard_tao` (Maynard–Tao, with
    threshold `exp (8*m+4) < B.card * log B.card`), `maynardTaoBFT` / `shiu_consecutive_primes`
    (Banks–Freiberg–Turnage-Butterbaugh, Shiu), `tao_teravainen` (ω ≤ Ω ≤ Ck on N+1..N+k infinitely
    often), `bernays` (integers represented by a binary quadratic form ~ C x/√log x), and
    `linnik_dvd` (from `Util/Linnik/Theorem.lean`, `exists_polynomial_prime_dvd_sub_one`).
  - It still declares four `axiom`s: `dusart_mertens_product`, `dusart_pi_lower`, `dusart_pi_upper`,
    `dusart_chebyshev`. Code search found no use outside `Axioms.lean` (search coverage is partial,
    unverified).
  - `Util/` also holds FranklRodl, Ramsey, MertensThird, IncidenceGeometry (610 files),
    PolynomialEgyptianSums and BinQuadForm.
  - Matching: every consequence of Maynard–Tao, Shiu and Linnik I checked against fc's open prime-gap
    statements (`erdos_5`, 218, 234, 238, 852–854, 1137, balanced primes) needs more than the lemma.
    plby is already the `formal_proof` source for the ones it settles.
- **math-inc/RiemannHypothesisCurves** `riemann_hypothesis_hec`. No licence, Lean v4.26.0-rc2.
  - It states `|q − #{y² = f(x)}| < 5·deg f·√q` (Stepanov), which fills the "no Weil bound" gap
    recorded in `rh-lemmas/README.md`.
  - It feeds Burgess-type least-non-residue bounds, consecutive residues and Paley-graph bounds. All
    of these are known theorems. The one open neighbour, Vinogradov's n₂(p) ≪ p^ε, needs far more.
- **teorth/IEANTN** (Apache-2.0). Nodes with no imports are unconditional, Comparator-checked
  explicit Chebyshev bounds (`Chebyshev.v1.psi_lower`, a ≈ 0.9213) and the FKS2 θ → π transfer.
  - CH2.v3 extremal majorants (Beurling–Selberg) match the Guinand–Weil inputs that cramer-rh (22/25)
    and lls-grh (Bach's 2) once listed. The workspace README now marks both projects ✅, so that
    match is moot.
- **PNT+** has the same pin as the workspace (Lean v4.36.0, Mathlib `fc4f59e5`). It offers
  `primesBetween_le` (explicit Brun–Titchmarsh), `selberg_bound_simple`, Mertens 2 and 3, the
  rectangle argument principle and Hadamard for ξ. Those are inputs for our own repos, not for open
  statements.
- **PFR** (`weak_PFR_int_sumset`, `torsion_PFR`), **LeanAPAP** (`ff`; the integer `int` is a
  `sorry`), **math-inc Sphere-Packing** (`LinearProgrammingBound` in every dimension),
  **KakeyaFiniteFields**, **ExponentialRamsey**, **Carleson**: each headline is a known theorem.
  - The open neighbours (Marton over ℤ, integer Kelley–Meka for Erdős 3 with k ≥ 4, packing in
    other dimensions, Euclidean Kakeya, the Erdős 77 limit) need inputs that no lemma here supplies.

## D. Rejected (kept so the next sweep skips them)

- **Hadamard order 668 via a Legendre pair.** solved-conjectures
  `HadamardLegendre.exists_hadamard_of_legendre_pair` gives order 2|G|+2, so 668 needs a Legendre pair
  of length 333. 668 is open, so no such pair is known. That is a search problem, not a lemma
  connection.
- **Erdős 726, 890(b), 950(iii)** from Mertens' second theorem (Pomerance–Sárközy files, PNT+
  `sum_prime_div_eq_log_log`). Necessary but nowhere near sufficient.
- **Erdős 1029, 87** from the lopsided LLL (`Frankl.Lopsided.conditional_card_bound`). Only the
  classical lower bound, which these problems must beat.
- **Union-closed** (`UnionClosed.union_closed`) from the Frankl high-girth and local-certificate
  lemmas. Special families only.
- **Erdős 64** from `ErdosGyarfasUniversal.universal_cover_power_of_two_cycle`. One family only.
- **WOWII Conjecture 72.** Two partial bounds whose combination is the open content.
- **riemann-hypothesis zero density, `twistK`, Minkowski, Chowla–Selberg.** No open target; see A.
- **plby Dusart axioms → discharge with IEANTN/PNT+.** The PNT+ Dusart file has 33 `sorry`, and no
  dependent plby proof was found. If one turns up, IEANTN's `RosserSchoenfeld1962` nodes are the place
  to look.
- **fc `*.ferreira_large_n` (Legendre, Andrica, Brocard, Oppermann for large n).** These rest on
  arXiv:2307.08725, which I believe is not accepted (unverified). Not a premise.

## What was searched, and what could not be checked

- **Searched:**
  - riemann-hypothesis source by keyword (section A).
  - The formal-conjectures tree at `9097e2f`: open statements on consecutive primes, residues,
    Dickson/Schinzel/abc uses, and the Firoozbakht/Andrica/Oppermann/Legendre/Brocard files.
  - solved-conjectures CONTENTS.md and Lean (via the local inventory).
  - plby/lean-proofs: tree, `Axioms.lean`, Util headlines, README, LICENSE.
  - `gh search code` (Lean) for `firoozbakht`, `andrica`, `balanced_primes`, `dickson_conjecture`,
    `erdos_141`.
  - The other lanes' `*.md` and `*.edges.jsonl`, to avoid duplicates.
- **Not checked:**
  - Exact thresholds and finite-check sizes for candidate 1.
  - The Ferreira–Mariano paper.
  - `davidleon/Gaseous-Prime-Universe`'s Andrica file.
  - Whether WOWII 84 holds for δ = 1.
  - plby's use of its Dusart axioms (code search is partial).
  - The real-to-integer lonely-runner reduction.
  - Any `#print axioms`.
- The external inventory's code search was rate-limited, so its Lean-existence checks rest on
  tree listings only.
