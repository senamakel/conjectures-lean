# Lane `implications`: Class 2 edges X ⇒ Y between open conjectures

All 98 edges, kept and rejected, are in `implications.edges.jsonl` (same directory). In this file,
"FC" means formal-conjectures at 9097e2f. Paths are relative to `FormalConjectures/`.

## Main finding

FC already states most of the premises, and many of the consequences, word for word. Where both
sides are FC statements, a theorem `B_of_A : type_of% A → type_of% B` involves no modelling
choices. FC itself proves only four edges of this kind: Oppermann ⇒ Legendre, Oppermann ⇒ Brocard,
Beal ⇒ FLT, and strong Goldbach ⇒ Erdős 418. It records one more with a `formal_proof` link
(abc ⇒ Erdős 393, Luca). Several other edges are *stated* in FC but left as `sorry`:
- `Erdos891.erdos_891.variants.weisenberg`, which takes `type_of% Dickson.dickson_conjecture` as a hypothesis;
- `Erdos252.erdos_252.variants.schinzel`;
- `Firoozbakht.firoozbakht_conjecture_consequence`;
- `Erdos470.erdos_470.variants.prime_gap_imp_inf_prim_weird`;
- `Mersenne.rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne`;
- `HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture`.

The edges group into three small Lean projects: **consequences of abc**, **consequences of
Dickson / Schinzel H**, and **prime-gap implications** (Cramér, Firoozbakht, Oppermann, Andrica).
A fourth group (Wieferich, Lander–Parkin–Selfridge, Grimm, Hall) is small enough to fold into any of them.

## Searches

- **FC.** Every `type_of%` hypothesis (69 uses), every `formal_proof` attribute on the relevant
  files, and the premise and consequence files read in full.
- **Erdős pages.** erdosproblems.com commentary, read from the atlas copy `data/raw/erdos.jsonl`
  (1221 problems), grepped for abc, Schinzel, Dickson, Hardy–Littlewood, prime tuples, Cramér,
  Elliott–Halberstam, Goldbach, Bombieri–Lang, and phrases like "assuming", "conditional on",
  "would follow".
- **solved-conjectures.** CONTENTS.md and the file trees of all 225 branches. Only
  `docs/erdos-woods-research.md` (branch `lean-gessel-zhuang-20261124`) is relevant, and it is
  unconditional work, not an abc implication.
- **GitHub code search.** 24 queries pairing a premise with a consequence (`dickson_conjecture
  twin_primes`, `oppermann andrica`, `pillais_conjecture abc`, `IsWieferichPrime abc`,
  `erdos_398 abc`, …). They found no Lean proof of any kept edge. The only hits were FC copies
  and benchmark mirrors (mathdb-lean, proofbee, conjectures-io).
- **Not searched.** Code search does not index everything. The Palomar registry pages render
  with JavaScript, so their contents could not be read.
- **Mathlib.** Not searched mechanically. As far as I know it has no abc, Dickson or prime-gap
  conjecture material (unverified).

## Ranked kept edges, easiest first (the top 20 are sketched)

Effort: S means at most about 2 agent-days.

### Group A: consequences of abc (one project, `abc-consequences`)

Shared toolkit, about 150 lines:
- (i) `abc ⇒ abc.variants.lt_constant_mul` (both FC). The finite set gives a maximum, so take
  K = max c + 1. The converse uses ε/2.
- (ii) `rad m ^ 2 ≤ m` for `Nat.Powerful m`, and `rad m ^ k ≤ m` for k-full m. The product of
  p^k over the prime factors divides m.
- (iii) `ABC.radical (n !) = primorial n ≤ 4 ^ n`, from Mathlib `primorial_le_4_pow`.
- (iv) n! eventually exceeds Cⁿ, for example from `Nat.factorial` lower bounds or Stirling.

FC's abc uses `({a, b, c} : Set ℕ).Pairwise Nat.Coprime`. Coprimality is automatic in every
application below because one of the three numbers is 1.

1. **abc ⇒ `Erdos936.erdos_936.variants.two_pow_add_one`**: `EventuallyNotPowerful (2 ^ · + 1)`.
   Apply abc to (1, 2ⁿ, 2ⁿ+1). If 2ⁿ+1 is powerful, rad ≤ 2√(2ⁿ+1). With ε = 1/2 this gives
   c ≤ K·(2√c)^{3/2}, so c is bounded. About 60 lines. **S.** Source: CrowdMath [Cr20], via erdosproblems.com/936.
2. **abc ⇒ `erdos_936.variants.two_pow_sub_one`**. Same proof with (1, 2ⁿ−1, 2ⁿ); the ℕ
   subtraction is harmless for n ≥ 1. **S.**
3. **abc ⇒ `erdos_936.variants.factorial_add_one`** (Cushing–Pascoe 2016). Apply abc to
   (1, n!, n!+1): rad ≤ 4ⁿ·√(n!+1), and n! beats every exponential. About 100 lines. **S.**
4. **abc ⇒ `erdos_936.variants.factorial_sub_one`**. Same proof. **S.**
5. **abc ⇒ `Erdos977.erdos_977.variants.factorial`**: P(n!+1)/n → ∞, open in FC. abc gives
   rad(n!+1) ≫ (n!)^{1−ε}/4ⁿ. Every prime factor of n!+1 exceeds n, so if P ≤ Cn then
   rad ≤ 4^{Cn}, a contradiction. Murty–Wong's (1+o(1)) n log n is not needed. About 120 lines. **S.**
6. **abc ⇒ finitely many triples of consecutive powerful numbers.** Use (n+1)² = n(n+2) + 1, so
   rad ≤ (n(n+1)(n+2))^{1/2}. **S.** *Catch:* FC `Erdos364.erdos_364` states that **no** triple
   exists, which abc cannot give. A new variant statement is needed:
   `{n | Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2)}.Finite`.
7. **abc ⇒ Brocard's problem has finitely many solutions** (Overholt 1993). **S.** *Catch:* FC
   `Erdos398.erdos_398` states the exact set `{4, 5, 7}`. A new variant statement
   `{n | ∃ m, n ! + 1 = m ^ 2}.Finite` is needed.
8. **abc ⇒ finitely many n with n 2-full and n+1 3-full**, and **finitely many consecutive 3-full
   pairs**. **S** each. *Catch:* FC `erdos_366` and `erdos_366.variants.weaker` are existence
   questions, so new finiteness variants are needed. Source: Turturean, in the erdosproblems
   comments (unverified).
9. **abc ⇒ the quality form `abc.variants.quality`, and the constant form ⇒ abc.** Log
   rewriting; rad(abc) ≥ 2 always holds, so there is no `log 1 = 0` junk. **S.**
10. **abc ⇒ `Catalan.pillais_conjecture`.** Let g = gcd(a xⁿ, b y^m). Then g divides c, so
    normalise by g. With 1/m + 1/n ≤ 5/6 (since (m, n) ≠ (2, 2)), the bound on X = xⁿ
    bounds everything. FC requires c > 0, so the ℕ truncated subtraction is harmless. About 200
    lines of real-exponent algebra. **M.**
11. **abc ⇒ `Hall.weak_hall_conjecture`.** FC quantifies over all x, y : ℤ. Negative x is
    trivial, small |x| is absorbed by choosing C, and the gcd g ≥ 1 only helps. **M.**
12. **abc ⇒ `FermatCatalan.fermat_catalan`.** Needs the finite case split 1/m + 1/n + 1/k < 1 ⇒
    ≤ 41/42. FC counts value triples, so base 1 with unbounded exponents does no harm. **M.**
13. **abc ⇒ infinitely many non-Wieferich primes** (Silverman 1988). The order-lifting lemma (a
    Wieferich p dividing 2ⁿ−1 forces p² | 2ⁿ−1) plus abc shows the "exactly once" part of 2ⁿ−1
    is unbounded. **M.** FC has no standalone statement; use the conclusion of FC's Rotkiewicz theorem.
14. **abc ⇒ `Erdos935.erdos_935.parts.iii`** ([Fe26], unverified). abc on (1, n(n+2), (n+1)²)
    bounds the product Q₂(n)Q₂(n+1)Q₂(n+2). The definition of `Erdos367.B` must be checked. **M.**

Rejected or hard (all in the JSONL):
- Erdős 393 (Luca): already has a `formal_proof` (Palomar).
- Erdős 373 (Luca 2007): **L**. Plain abc gives only P(n(n+1)) ≥ (1−ε) log n, below FC's
  `of_lower_bound` hypothesis of 4 log n.
- Erdős 145 and 208 (Granville): **XL**.
- Erdős 850: needs Baker's explicit abc. **XL**.
- Erdős 938 and `erdos_364.variants.strong`: no deduction found, and the naive argument fails.
- Erdős–Woods (Langevin): **L**, and not in FC.
- Mordell, Roth, Siegel zeros: **XL**.
- Asymptotic FLT: **S**, but the consequence is Wiles' theorem.

### Group B: consequences of Dickson / Schinzel H (one project, `dickson-consequences`)

Shared toolkit, about 150 lines:
- (i) Linear `C·X + D` with gcd(C, D) = 1 and C > 0 satisfies `BunyakovskyCondition`
  (primitive of degree 1, so irreducible over ℤ).
- (ii) Admissibility lemma: for a finite set of linear forms, if for each prime p some n ∈ ℕ
  avoids every root mod p, then `SchinzelCondition` holds. Covered either by a pigeonhole for
  p > |fs| plus a small-p `decide`, or by the witness n = 0 whenever every form takes the value ±1 at 0.
- (iii) Converting `Infinite {n | ∀ f ∈ fs, (f.eval n).natAbs.Prime}` into the target set. Use
  `Nat.prime_iff` where FC writes the root `Prime`.

15. **Schinzel ⇒ Dickson; Schinzel ⇒ Bunyakovsky.** Specialisations. **S.**
16. **Dickson ⇒ `TwinPrimes.twin_primes`, `Dickson.generalized_twin_primes`,
    `infinite_safe_primes`, `infinite_cousin_primes`, `infinite_sexy_primes`.** Five edges with
    both sides in FC, each about 30 lines on top of the toolkit. **S.**
17. **Bunyakovsky (or Schinzel) ⇒ `PrimesAndPerfectSquares.infinite_prime_sq_add_one`**
    (Landau's fourth problem). Needs `Irreducible (X^2+1 : ℤ[X])`; the witness n = 0 works for
    every p. **S.**
18. **Dickson ⇒ `Erdos891.erdos_891.variants.weisenberg`.** Already stated in FC with Dickson as
    a hypothesis, and unproved. Take n = L·n' + 1 with the forms (L/m)X + 1; the witness n' = 0
    gives 1. A primorial lemma gives ω(m) ≤ k−1 for m < p₁⋯p_k. About 150 lines. **S.**
19. **Dickson ⇒ `Erdos647.erdos_647.variants.infinite`.** Erdős noted that this "follows from
    Hypothesis H"; linear forms suffice. Take n = L·t with the forms (L/j)X − 1 for j < k; the
    witness t = 0 gives −1. Then τ(j·p) = 2τ(j) ≤ j + 2, because τ(j) ≤ j/2 + 1. Watch the
    ℕ subtraction in `Set.Ioo (n - k) n`. About 150 lines. **S.**
20. **Dickson ⇒ `PrimeTriplets.prime_triplets`.** Admissibility for {X, X+2, X+6} is the
    pigeonhole for p ≥ 5. **S.**

Further edges, effort M:
- **Dickson ⇒ Jones' exact-length Cunningham chains** (`Arxiv/1104.1579`, first and second
  kind). Force the k-th term composite by restricting to a congruence class.
- **Dickson ⇒ infinitely many composite M_p** (Euler: p ≡ 3 mod 4 with 2p+1 prime). Not in FC.
- **Dickson ⇒ infinitely many 3-factor Carmichael numbers** (Chernick). Not in FC; FC has
  `korselts_criterion` proved.
- **Dickson ⇒ ¬(∀ x, y ≥ 2, π(x+y) ≤ π x + π y).** Uses an explicit admissible 447-tuple of
  width 3159 (Engelsma's numbers, unverified). FC states this only from the First
  Hardy–Littlewood conjecture.
- **First Hardy–Littlewood ⇒ twin primes.** *Catch:* the constant C is a `tprod`. A
  non-multipliable product is the junk value 1, which is harmless, but a multipliable one must
  be shown to be positive.
- **Bateman–Horn ⇒ Schinzel.** **S–M.**

Effort L:
- `erdos_252.variants.schinzel` / `prime_tuples` (Schlage-Puchta; Friedlander–Luca–Stoiciu).
- Erdős 884 via Hardy–Littlewood (already disproved unconditionally).

Rejected:
- Erdős 15 and 855: need quantitative Hardy–Littlewood.
- Erdős 682's Dickson counterexample: already has a `formal_proof`.
- Twin primes ⇒ Erdős 48: the consequence is already solved.

### Group C: prime-gap implications (one project, `prime-gap-implications`)

21. **Andrica ⇒ Legendre** (`Andrica.andrica_conjecture` ⇒ `LegendreConjecture.legendre_conjecture`).
    Let p be the largest prime ≤ n² and q the next. Then √q < √p + 1 ≤ n + 1. About 30 lines. **S.**
22. **Oppermann ⇒ Andrica.** Wikipedia's "Consequences" section states it, with no primary
    citation. Consecutive Oppermann half-intervals have length x, so the gap is at most 2x − 2,
    while 2√p + 1 > 2x. **S.** FC already proves Oppermann ⇒ Legendre and Oppermann ⇒ Brocard (rejected as done).
23. **Cramér (big-O) ⇒ `Erdos680.erdos_680.parts.i`.** Take k = (next prime) − n ≤ C log² n.
    Then k² + 1 < n < q = minFac(n+k). **S.**
24. **Cramér ⇒ `Erdos382.erdos_382.parts.i`** (Cambie's remark). A bad interval contains no
    prime: if q ∈ [u, v] and v < 2u, the largest prime factor occurs to exponent 1. FC already
    proves `lt_two_mul_of_largestPrimeRepeated`. So v − u < gap = O(log² v). **S.**
25. **Cramér ⇒ `erdos_945` and `erdos_945.variants.constant`** (Cambie). Two primes in one
    window have equal τ = 2. **S.**
26. **Cramér ⇒ the eventual forms `legendre_conjecture.ferreira_large_n`,
    `andrica_conjecture.ferreira_large_n`, `oppermann_conjecture.ferreira_large_x` and
    `brocard_conjecture.ferreira_large_n`.** **S** each. Legendre composes with FC
    `bounded_gap_legendre`, which has an AlphaProof `formal_proof`. *Catch:* FC labels these
    consequences "Ferreira proved"; that claim is unverified.
27. **`cramer_conjecture.variants.strict_bound` ⇒ the full Legendre, Andrica and Oppermann
    statements.** **M** each. The work is the real-log numerics (for example 4 log² x < x − 1 for
    x ≥ 75) plus a finite `decide` over primes below about 8100.
28. **Trivial intra-file edges, S.**
    - `strict_bound`, `limsup_eq_one` and Shanks each ⇒ `cramer_conjecture`.
    - Firoozbakht's consequence ⇒ `strict_bound`.
    - `grimm_conjecture` ⇒ `grimm_conjecture_weak`.
    - `lemoine_conjecture_extension` ⇒ `lemoine_conjecture`.
    - `hall_conjecture` ⇒ `weak_hall_conjecture`. *Catch:* the premise is believed false.
29. **Cramér ⇒ `erdos_420.parts.i`.** Each new prime in (n, n+f] doubles τ. **M.**
30. **Firoozbakht ⇒ Andrica and Legendre.** **M**: needs an elementary Chebyshev lower bound
    for π(x). Firoozbakht ⇒ its FC consequence (Kourbatov) is **L**, because it needs
    Dusart-type explicit bounds.
31. **Cramér ⇒ Melfi's hypothesis** (gap < √p/10) is **S**. From there to
    `erdos_470.parts.ii` (Melfi 2015) is **L**.

### Group D: small extras

- **`Mersenne.squarefree_mersenne_of_prime` ⇒ infinitely many non-Wieferich primes, and a proof
  of FC's Rotkiewicz statement itself.** **S–M.** Every prime factor of a squarefree Mₙ is
  non-Wieferich (order lifting). No Zsigmondy is needed: a finite set of primes cannot cover
  unbounded squarefree Mₙ. The location of the `IsWieferichPrime` definition was not checked.
- **Lander–Parkin–Selfridge ⇒ `Erdos324.erdos_324.variants.quintic`, and hence `erdos_324`
  with f = X⁵.** **S.** a < b and c < d force the two pairs to be distinct; a = 0 becomes the
  case n = 1, m = 2. Also LPS ⇒ `five_three` (**S**).
- **Elliott–Halberstam ⇒ Bombieri–Vinogradov.** Trivial (**S**), but the consequence is a theorem.
- **Rejected:** Elliott–Halberstam ⇒ bounded gaps (**XL**, per the brief); Bombieri–Lang ⇒
  Erdős 212, 213, 782 (**XL**); strong Goldbach ⇒ Erdős 418 (done in FC); Collatz ⇒ Erdős 1135
  (same statement).

## Recommended first project

**abc-consequences**: edges 1–9, plus 13 and 10. That is eleven theorems on one toolkit, and
the four Erdős 936 variants and 977-factorial are verbatim open FC statements. Estimated at
about 3–4 agent-days for the S edges. Second choice is **dickson-consequences** (edges 15–20,
about 9 theorems).

Every result would carry the label "conditional on abc" (tier C, with no RH involved). That
needs a tier/literature labelling decision from the user, since CLAUDE.md's labels are written
around RH/GRH.
