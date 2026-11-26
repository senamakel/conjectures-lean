# fc-scan: implication edges in formal-conjectures (9097e2f)

Lane `fc-scan`, 2026-11-26. Research only. Nothing was built and no repository was edited.
Scope follows the owner's update: every area counts, ranked equally.

## Method and coverage

- The files were parsed with `python3 -I` (scripts in `discovery/fc-scan-work/`). The parse found
  9,069 attributed declarations, including 1,952 `research open` (grep counts 1,955; the three
  missing are re-exports in `Subsets/FC100*`) and 1,819 `research solved` that are still `sorry` with
  no `formal_proof`.
- The scan read every docstring, statement and module docstring of those 3,771 declarations, using
  four passes:
  1. Named premises (RH/GRH/ERH, abc, Schinzel, Bunyakovsky, Dickson, Elliott–Halberstam,
     Hardy–Littlewood/k-tuples, Cramér/Firoozbakht/Andrica/Legendre/Oppermann, Goldbach, twin primes,
     Chowla, pair correlation, Artin/Hooley, and about 30 other named conjectures).
  2. Implication words ("implies", "follows from", "conditional", "assuming", "equivalent",
     "consequence", "would give", "suffices", "under the").
  3. Lean-level hypotheses: `type_of%`, and `(h… : …Conjecture/Hypothesis…)` and `hRH`-style binders.
  4. Backtick cross-references between declarations, and same-file checks of open versus solved-in-Lean pairs.
- All 212 + 376 + 84 + 38 hits were read. Hit lists: `fc-scan-work/strong.txt`, `rest2.txt`, `extra.txt`,
  `typeof2.txt`, `hyps.txt`, `xref.txt`, `samefile.txt`.
- 70 edges are recorded in `fc-scan.edges.jsonl`, rejected ones included.

**Main finding.** formal-conjectures holds very few RH/GRH-conditional statements, and every one has
been taken: by our projects (985, 233, Mills, idoneal, Cramér, density, Li, Robin/Lagarias), by
earlier scoping (powerful numbers), or by rejection (Knapowski–Turán, Montgomery, Breuillard–Varjú,
Rubinstein–Sarnak). fc now relabels RH consequences "solved" by citing [Al26] (985, 233, Mills,
idoneal, PowerfulNumbersDensity).

The only new Class 1 edge is RH ⇒ `simple_prop_lt` / `distinct_prop_lt` (Bui–Heath-Brown), and it is
XL. Everything cheap is Class 2.

## Ranked candidates (easiest first)

### 1. abc ⇒ Erdős 977, factorial variant: P(n!+1)/n → ∞ (S)
- **Statement.** `ErdosProblems/977.lean`, `erdos_977.variants.factorial` (**research open**):
  `Tendsto (fun n : ℕ ↦ (Nat.maxPrimeFac (n.factorial + 1) : ℝ) / n) atTop atTop`.
- **Premise.** `ABC.abc` (`Wikipedia/ABC.lean`, open), or `abc.variants.lt_constant_mul`.
- **Source.** Murty–Wong 2002 prove abc ⇒ P(n!+1) > (1+o(1)) n log n. It is cited in the fc docstring;
  the page numbers in the paper were not checked.
- **Deduction.**
  1. Apply abc with ε = 1 to the triple (1, n!, n!+1). It is coprime, and it is injective in n ≥ 2,
     so it is not an exception for large n.
  2. rad(n!) | primorial(n) ≤ 4ⁿ, by Mathlib `primorial_le_4_pow`.
  3. Every prime factor of n!+1 is ≤ P, so rad(n!+1) ≤ primorial(P) ≤ 4ᴾ.
  4. Hence n! < 4^{2(n+P)}, so P ≥ log(n!)/(2 log 4) − n ≫ n log n.
- **Missing.** A lower bound log n! ≥ n log n − n (Mathlib's Stirling file, or (n/2)^{n/2} ≤ n!), and
  `ncard`/finiteness bookkeeping.
- **Known unconditionally.** limsup P(n!+1)/n ≥ 7.238 (Lai 2021).
- **Lean.** Nothing found in fc. GitHub code search was rate-limited and did not run. Not in 1337
  CONTENTS.
- **Catch.** Class 2: the theorem reads "abc ⇒ Y" and abc stays open. It is short, so expect it to be
  claimed quickly once noticed.

### 2. Cramér ⇒ Erdős 382(i) (S)
- **Statement.** `ErdosProblems/382.lean`, `erdos_382.parts.i` (open):
  `∀ ε > 0, ∀ᶠ v in atTop, ∀ u, LargestPrimeRepeated u v → ((v - u : ℕ) : ℝ) ≤ v ^ ε`.
- **Premise.** `CramerConjecture.cramer_conjecture` (open). A gap bound `primeGap n ≤ p_n^{o(1)}` is
  enough, so Firoozbakht, Shanks or the Cramér strict bound would also do.
- **Source.** Cambie's observation, quoted in the fc docstring (erdosproblems.com/382).
- **Deduction.** fc already proves `lt_two_mul_of_largestPrimeRepeated` (v < 2u). Then [u, v] holds
  no prime: a prime q there would force the largest prime p ≥ q > v/2, which appears once. So v − u
  is less than one prime gap, and that gap is O(log² v) ≤ v^ε.
- **Missing.** Locating u, v between consecutive primes (`Nat.nth` / `primeGap` API).
- **Catch.** Class 2. Scoping part 1 discarded #382 as "needs beyond RH", which is a different
  question from this one. The same route via cramer-rh gives the *solved* Ramachandra variant
  (v^{1/2+ε}), but that is a known theorem, so it is excluded by policy (edge recorded).

### 3. Squarefree Mersenne numbers ⇒ infinitely many non-Wieferich primes (S)
- **Statement.** `Wikipedia/Mersenne.lean`,
  `rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne`. fc labels it research solved, but it
  is `sorry` with no formal_proof. Its conclusion is open unconditionally.
- **Premise.** `{n | Squarefree (mersenne n)}.Infinite` (open). It follows trivially from
  `squarefree_mersenne_of_prime`.
- **Source.** Rotkiewicz 1965.
- **Deduction.** If p is Wieferich and p | Mₙ, then ord_{p²}(2) = ord_p(2) | n, so p² | Mₙ. With
  only finitely many non-Wieferich primes, every squarefree Mₙ would be a product of them, so it
  would be bounded.
- **Missing.** The lifting fact `sq_dvd_mersenne_iff_isWieferichPrime`. It is stated in fc as
  textbook, `sorry`, and is short.
- **Catch.** Class 2, and the implication is already stated in fc, so this is a proof contribution.

### 4. Butson H(4,2m) ⇒ Hadamard conjecture (S, combinatorics)
- **Statements.** `Wikipedia/ButsonHadamardMatrix.lean` `butson_hadamard_fourth_roots_conjecture`
  ⇒ `Wikipedia/Hadamard.lean` `HadamardConjecture` (`∃ M, IsHadamard (n := 4*k) M`). Both are open.
- **Source.** Turyn 1970 doubling, cited in the fc docstring.
- **Deduction.** Write M = A + iB with A, B ∈ {0,±1} on disjoint supports. Then MM* = nI gives
  AAᵀ + BBᵀ = nI and ABᵀ = BAᵀ, and the 2×2 block matrix built from A ± B is a real Hadamard matrix
  of order 2n. The case k = 0 is `exists_hadamard_zero`.
- **Missing.** Block-matrix algebra (`Matrix.fromBlocks`) and matching fc's `IsHadamard` definition.
- **Catch.** Class 2. It is a famous target, but the deduction is classical and elementary.

### 5. Four exponentials ⇒ 2^t or 3^t transcendental (S)
- **Statement.** `Wikipedia/Exponentials.lean`, `two_pow_three_pow_transcendental` (open), from
  `four_exponentials_conjecture` (open).
- **Deduction.** Take x = (1, t) and y = (log 2, log 3). Both pairs are ℚ-independent (unique
  factorisation; t irrational). exp(log 2) = 2 is algebraic, so 2^t or 3^t is transcendental.
- **Missing.** Coercion between real `2^t` and complex `exp`, and ℚ-independence of log 2, log 3.

### 6. Trivial specialisations (S each; low value, belong in fc as `test`/`API` lemmas)
- Dickson ⇒ `twin_primes`, `generalized_twin_primes`, `infinite_safe_primes`,
  `infinite_cousin_primes`, `infinite_sexy_primes`.
- Schinzel H ⇒ Dickson; Schinzel H ⇒ Bunyakovsky.
- Minoli–Bear ⇒ `infinitely_many_hyperperfect_numbers`.
- OEIS A091591 conjecture ⇒ Legendre (plus a `decide` check for n ≤ 122) and ⇒ twin primes.
- OEIS A053000 conjecture ⇒ Oppermann part (ii).
- `green_76` / `green_76.variants.weak_net` ⇒ `green_76.variants.exists_constant`.
- `green_75` ⇒ `green_75.variants.exists_constant`.
- `erdos_604.variants.average` ⇒ `sqrt_log`; `erdos_963.parts.ii` ⇒ `erdos_963.variants.positive`.

Each needs only the hypotheses checked: SchinzelCondition for {X, X+c}, or a floor estimate.

### 7. First Hardy–Littlewood ⇒ ¬ second Hardy–Littlewood (M)
- **Statement.** `Wikipedia/HardyLittlewood.lean`, `not_first_and_secondHardyLittlewoodConjecture`.
  fc labels it solved, but it is `sorry` with no formal_proof.
- **Source.** Hensley–Richards 1974.
- **Deduction.** Take an admissible tuple of more than π(y) even offsets in [0, y]. Engelsma's
  447-tuple of width 3159 should work (unverified; the data has to be fetched). First HL (with
  C_P > 0) gives some p with every p + mᵢ prime. Then x = p − 1 violates π(x+y) ≤ π(x) + π(y).
- **Missing.**
  - Admissibility of the tuple by `decide`: 88 primes × 447 offsets.
  - C_P > 0: fc's `tprod` is the junk value 1 when not multipliable, but a multipliable product
    tending to 0 must be excluded, which needs a Σ 1/q² bound.
  - Divergence of ∫ dt/log^{k+1} t.

### 8. Dickson ⇒ Erdős 891, Weisenberg variant (M)
- **Statement.** `erdos_891.variants.weisenberg`, which already has a
  `hdickson : type_of% Dickson.dickson_conjecture` hypothesis. Solved, `sorry`.
- **Deduction.** The CRT/lcm argument written out in the docstring. The forms (L/m)x + 1 need
  SchinzelCondition, and each m(L/m·n′+1) needs an ω count. The argument was not re-checked by hand.

### 9. Firoozbakht ⇒ gaps < log² p − log p for n > 4 (M)
- **Statement.** `firoozbakht_conjecture_consequence` (solved label, `sorry`).
- **Source.** Kourbatov 2015 (unverified).
- **Missing.** An explicit lower bound p_n > n log n, which is not in Mathlib, and a small finite check.
- **Chains with #2.** Firoozbakht ⇒ Erdős 382(i).

### 10. Schinzel H / prime k-tuples ⇒ Σ σ_k(n)/n! irrational (M)
- **Statements.** `erdos_252.variants.schinzel` and `.prime_tuples` (both solved, `sorry`).
- **Sources.** Schlage-Puchta 2006; Friedlander–Luca–Stoiciu 2007.
- **Missing.** Factorial-tail irrationality bookkeeping with `tsum`.

### 11. abc ⇒ infinitely many non-Wieferich primes (M)
- **Source.** Silverman 1988.
- fc has no standalone statement; the consequence set appears in the Rotkiewicz and
  `erdos_11.variants.granville_soundararajan` statements.

### 12. `erdos_11.variants.all_odd` ⇒ infinitely many non-Wieferich primes (M; effort unverified)
- **Source.** Granville–Soundararajan 1998, Thm 1.

### 13. Berge–Fulkerson ⇒ Fan–Raspaud (M)
- **Statement.** `BergeFulkersonConjecture.lean`, `variants.fan_raspaud`.
- **Deduction.** Folklore: three of the six matchings in a Berge–Fulkerson double cover share no
  edge. The counting argument was not checked.

### 14. Short-interval π bound ⇒ Erdős 950: f ≪ logloglog n (M; unverified)
- **Statement.** `erdos_950.variants.weaker_pi_implies_f`.

### 15. RH ⇒ `riemannZeta.simple_prop_lt` and `distinct_prop_lt` (Class 1, XL)
- **Statements.** `Paper/RiemannZetaZeros.lean` (open).
- **Source.** Bui–Heath-Brown 2013 (arXiv:1302.5018): under RH, at least 19/27 = 0.7037 of the zeros
  are simple, above 0.6725, and at least 0.84665 are distinct, above 0.8362. They count 0 < γ < T;
  fc counts T < γ ≤ 2T.
- **Missing.** Montgomery's pair-correlation theorem under RH plus BH13's twisted second moments.
  anthropics/zeta-23-lean formalises the unconditional Levinson/Montgomery–Taylor bound, and its
  reuse was not checked.
- **Assessment.** The only genuinely new RH ⇒ open-fc edge found. It is not on any do-not-repeat
  list and not in the 1337 rh-transfer inventory. Multi-month work.

### Further edges (L/XL, recorded in the jsonl)
- Melfi (gaps < √p/10 ⇒ infinitely many primitive weird numbers, #470).
- Grimm-type ⇒ gaps < p^{1/2−c} (#375; 1337 has `research/grimm/`).
- Araujo–Filipe–Miyazaki Ramsey conditional (#627).
- Elliott–Halberstam ⇒ #408(ii) (EGPS90).
- Bombieri–Lang ⇒ #782(ii).
- Petersen colouring ⇒ Berge–Fulkerson / cycle double cover.
- JC₂ / PC₁ ⇒ DC₁.
- Farrell–Jones ⇒ Bass.
- Milićević ⇒ Rado boundedness.
- Real Schanuel ⇒ decidability of ℝ_exp.

## Rejected (recorded with reasons in the jsonl)
- **Done by us:** 985, 233, Mills, idoneal, Cramér RH, density, Li, Robin/Lagarias `_rhs`
  (upstreaming suggested in NEXT_TARGETS).
- **Scoped already:** powerful numbers `error_term_improvement`.
- **Already proved in Lean:**
  - abc ⇒ #393 (`erdos_393.variants.luca`, palomar formal_proof).
  - HL ⇒ #884, made moot because `erdos_884` itself has an unconditional formal_proof.
  - #418 and #913 conditionals, `oppermann_implies_*` and `erdos_287` prime_conjecture_implies,
    which fc proves or links.
- **Policy or premise unavailable:**
  - Knapowski–Turán (NEXT_TARGETS and 1337).
  - Rubinstein–Sarnak (needs LI).
  - Montgomery pair correlation (not implied by RH).
  - Breuillard–Varjú and EllipticCurveRank 31 (non-abelian ERH, BSD).
  - Beurling–Nyman and Weil (XL, already rejected).
  - Bombieri–Vinogradov (a known theorem).
  - Ramachandra variant of #382 (known).
- **Not real edges:**
  - `erdos_1132.parts.ii`: the docstring's "follows from" is about density, not the a.e. statement.
  - OEIS A103151 ⇒ Goldbach: the claim is unverified and probably false.

## Do-not-repeat checks done
- conjectures-lean `README.md` (28 rows), `docs/NEXT_TARGETS.md`, `FURTHER_PROJECTS.md`,
  `ATTEMPTS.md`, and every file in `docs/scoping/`.
- solved-conjectures `CONTENTS.md` on main and `git grep` on `origin/research`, including the
  `research/rh-transfer/README.md` inventory of 24 names.
- Keyword checks (abc, Murty, Wieferich, Rotkiewicz, Butson, Turyn, four exponentials, Cramér,
  Richards, Dickson, Firoozbakht, Bui, hyperperfect, Fan–Raspaud): no hit settles any kept candidate.
  The only hits nearby are Hadamard order 2396 (a different question) and `research/grimm` (#375).

## Not checked
- **GitHub code search:** `gh search code` returned HTTP 403 (rate limit), so "no Lean proof
  elsewhere" rests on fc `formal_proof` attributes and 1337 only.
- **Palomar registry:** not browsed; it may hold conditional proofs, as it does for #393.
- **Primary sources:** none of the papers was opened (Murty–Wong, Rotkiewicz, Turyn,
  Hensley–Richards, Kourbatov, BH13). Attributions come from fc docstrings or memory, marked
  (unverified) where they are not quoted in fc.
- **Effort estimates** were not tested against the Mathlib pin fc4f59e5. Only `primorial_le_4_pow`
  was assumed, and it is not yet confirmed at that pin.
