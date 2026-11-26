# Lane `w3-progressions-fields`: least primes in progressions, non-residues, abelian fields

Date 2026-11-26 (wave 3). Research only: no Lean written, no other file edited. Numbers were
computed in this session: Python `-I` for thresholds, and C sieves with modular exponentiation
for the checks. The scripts are in the session scratchpad (`w3pf/`) and were not kept. Claims not
checked against a primary source are marked *(unverified)*. Edges are in
`w3-progressions-fields.edges.jsonl`.

## Result

**I found nothing in class A on this ground.** Every open statement I found in the four sub-areas
falls into one of three groups:

- It needs Linnik with exponent 2 or less (`p(a,q) < q²`), so even GRH does not reach it.
- Its GRH deduction is already published, usually in the same paper that states it (class B).
- The finite range it needs is far beyond a Lean check.

The ground is also crowded. Since October 2026, class-number lists up to `h ≤ 3500` have been
posted under GRH, under QRH and under Kimura's bound. One class-B item is cheap and gives a clean,
complete statement: B1 below.

## Class B (the conditional deduction is published; only the unconditional form is fresh)

### B1. Knapp–Köcher–Schmid: `ϱ_p < √p` for every prime `p ∉ {3, 5, 7, 17, 19, 43, 67, 163}` · S

- **Statement.** Here `ϱ_p` is the least odd prime `q ≠ p` with `(q/p) = 1`. Source: W. Knapp,
  M. Köcher, P. Schmid, *Quadratic residues and class numbers*, Funct. Approx. 47 (2012) 173–182,
  abstract: "it is shown that ϱ_p < √p unless p ∈ {3, 5, 7, 17, 19, 43, 67, 163}, possibly with
  one further exceptional (large) prime p = p_u … The exceptional prime does not exist if the
  Extended Riemann Hypothesis is true." The exception would give a real zero of `L(s, χ)` in
  `(71/72, 1)`, which is excluded by GRH and also by the unrefereed QRH half-plane `Re s > 11/12`
  that OpenAI announced in October 2026.
- **Why class B.** KKS publish the ERH deduction themselves. What is fresh is only the
  unconditional statement with no exception, which follows from our Lean GRH.
- **Deduction (Lean premises).** Let `χ` be the Legendre symbol mod `p` (primitive) and
  `w(n) = 1 − n/x`. Suppose `x ≤ p` and no odd prime below `x` is a residue. Then
  `Σ_{n<x} Λ(n)(1+χ(n))w(n)` contains only powers of 2 (at most `2 log x + 2 log 2`) and even
  powers of odd primes (at most `2ψ(√x) ≤ 2.8√x`). `erdos-985` `bach_principal_of_GRH` and
  `weinberger-grh` `bach_primitive_of_GRH` (with `N = p`) bound it below by
  `x/2 − √x/20 − 3 − [(√x+2+3/x)(2/3)(log p + 5/3) + log x + 1.6]`.
  - **Threshold (computed):** with `x = ⌊√p⌋` the inequalities contradict each other for every
    `p ≥ 7.07·10⁵`.
  - **Finite range:** the primes below `7.1·10⁵`, about `5.7·10⁴` of them, each needing a few
    Legendre symbols. In Lean this is a `decide`/`native_decide` chunk.
  - **Check (done):** every prime `p ≤ 10⁸`. The only `p` with `ϱ_p ≥ √p` are exactly KKS's
    eight. For `p > 1000`, the largest `ϱ_p / log² p` is `0.558`, at `p = 5297` (`ϱ = 41`).
- **Lean.** About 50 lines of analysis on top of the two lemmas, plus the check. Effort S.
- **Catch.** Low novelty. The deduction is in KKS, and QRH (if accepted) removes the exception as
  well. Jaswal's Zenodo note 23251443 (Oct 2026) says "several classifications known only up to
  one possible exception become complete". I did not see KKS in its abstract *(unverified
  whether the note covers it)*.

### B2. KKS's effective-`β(c)` conjecture, with `β(1/3) = 74093` explicit · S–M

- **Statement (same paper, last paragraph of the introduction).** "one might conjecture that,
  given any real number c ∈ (1/4, 1/2], there is an effective bound β(c) such that ϱ_p < p^c for
  p > β(c), with at most one exception." KKS have `β(1/2) = 163`.
- **Why class B.** GRH gives `ϱ_p ≤ C log² p` with an explicit `C`. That is Ankeny 1952, made
  explicit by Bach–Sorenson and by LLS Thm 1.4. So the conjecture holds for every `c > 0` under
  GRH, and the deduction is folklore. The fresh item is the explicit, exception-free value:
  - **`c = 1/3`.** `ϱ_p < p^{1/3}` for every prime `p > 74093`.
    - Analytic threshold (B1's inequality with `x = ⌊p^{1/3}⌋`): `4.36·10⁹`.
    - **Exact check, done:** every prime up to `4.4·10⁹`. There are 77 exceptions, the last at
      `p = 74093` (`ϱ = 43`). Above `1.1·10⁹` the largest `ϱ_p` is 127, at `p = 1728061733`.
    - A Lean version would check about `2.1·10⁸` primes with a few `powMod` each, which is
      erdos-985's scale.
  - **`c = 0.3`.** The last exception below `10⁸` is `p = 773767`, but the threshold is
    `9.8·10¹⁰`. Out of reach without a sharper constant.
  - **`c = 1/4`.** The last exception below `10⁸` is `p = 17999503`, and the threshold is
    `6.3·10¹³`. Out of reach.
- **Catch.** It is a soft conjecture, and our explicit `β(1/3)` is a numerical refinement, not
  a new idea. Low value.

### B3. Imaginary quadratic fields with class group of exponent 3 or 5 (Elsenhans–Klüners–Nicolae) · XL

- **Source.** EKN, Acta Arith. 193 (2020), arXiv:1803.02056, Thm 2: "Assuming ERH, our
  computations found all fields for exponent up to 5 and 8." Exponent 3 gives 17 fields, the
  largest `|D| = 4027`. Unconditionally only finiteness is known.
- **Our threshold (computed).** If `Cl(D)` has exponent `E`, every split prime satisfies
  `p ≥ (|D|/4)^{1/E}`. B1's argument applied to `χ_D` (with the ramified primes bounded by
  `ω(D) log x`) closes for `|D| ≥ 4.2·10¹⁰` (`E = 3`) and `|D| ≥ 1.8·10¹⁹` (`E = 5`).
- **Why not in Lean.** Below the threshold we would need class-group computations for every
  fundamental discriminant up to `4·10¹⁰`. That is XL. Class B and not feasible.

### B4. Other published GRH consequences met on the way (no work proposed)

- **MathOverflow 426966 / OEIS A354597.** The least `k` with `−n` a non-residue mod `k` is
  `O(log² n)` under GRH. The MO answer (GH from MO, 2022) gives the GRH proof.
- **Narayanan (MIT PRIMES 2014), Conjecture 5.1.** A witness `< 2 ln² n` exists for every
  composite `n` outside three special forms, "proved without ERH". It is Bach's theorem for all
  composites. With GRH now a Lean theorem (lls-grh), nothing is left.
- **Vinogradov's `r_p ≪ p^ε`.** Already rejected in wave 1 (1337 `research/rh-transfer`). Also
  dr vengy, Zenodo 23607810 (Oct 2026), under QRH.
- **McGown: norm-Euclidean cyclic cubic fields.** Under GRH the 13 known conductors are the only
  ones *(unverified: recalled, not re-read)*. It is class B. The Lean side would need
  Euclidean-minimum computations for the positive direction. L–XL. Not pursued.

## Rejected (also in the edges file)

| Statement | Source | Reason (computed) |
|---|---|---|
| least prime `≡ 1 (mod n)` is `< n²` | OEIS A034694 (Ordowski 2016) | GRH gives `2(n log n)²` (Bach–Sorenson) or `(φ(n) log n)²` (LLS). Both exceed `n²` for every `n` |
| `kn+1` prime for some `k < n`; `k < 1 + n^{0.75}`; `a(n) = O(log n log log n)` | A034693 (Murthy 2001, Pe 2002, Ordowski 2014) | `n²`-strength or stronger. Not reachable |
| the maximum over `b` of the least prime `≡ b (mod n)` is `< n²` | A085420 (Kanold-type) | same |
| Proth-type: `k·2^n + 1` prime with `k < 2^n` | least prime `≡ 1 (mod 2^n)` | GRH gives `k ≪ n²2^n`. Not reachable |
| Weaker forms such as `p(a,q) < q³` (true under GRH for `q > 13`) or `< q^{5/2}` (for `q > 57826`) | none | **no source states them as open**, so they are not candidates. They are trivial corollaries of Bach–Sorenson |
| least prime QNR `≡ 3 (mod 4)` below `√p` for `p > 1091`; `≡ 1 (mod 4)` below `√p` for `p > 6269` | sharpenings of Pollack, JNT 187 (2018), Thms 1–2 (`q < p`) | computed exactly to `10⁸`. Under GRH this is a one-page deduction (four characters mod `4p`). But no source states it: Pollack only remarks that the unconditional `n₃(p) ≤ p^{1/4+o(1)}` is ineffective. Not a candidate under the brief's rules. Recorded in case a later lane finds a statement |
| `h(−d) = n` lists for `n > 100` | — | published under GRH (Garcia–Grenié–Lee–Molteni, `h ≤ 2000`; Holmin–Jones–Kurlberg–McLeman–Petersen arXiv:1510.04387, odd `h < 10⁶`) and under QRH (zeta-lab `h ≤ 1500`; Jaswal, Zenodo 23251443, `h ≤ 3000`; GitHub DrMurphyIsIn/boundaries-of-class, `h ≤ 3500`). In Lean, LLS's `h(−q)` lower bound only holds for `q ≥ 10¹⁰`, so every `d < 10¹⁰` would need a class number. XL |
| exponent-6 and exponent-7 class groups (EKN: complete only to `3.1·10²⁰`; for exponent 7 finiteness is unknown) | EKN 2020; Paderborn list | B3's GRH argument needs `|D| ≥ 8.4·10²³` (`E = 6`) and `≥ 5.8·10²⁸` (`E = 7`), beyond any tabulation. GRH alone does not close it |
| Euler's lucky numbers, `h(−d) = 1` | Heegner–Stark | known unconditionally |
| Bach's conjectured least witness `~ log n log log n / log 2` | Bach 1990 | far below `log² n`. Not reachable |
| Sun's primitive-root / quadratic-residue conjectures of special shape (arXiv:1405.0290 §3–4) | Sun | rejected by `novel-oeis-lists` (Weil-type, Kummer-type, or two moduli). Conj. 3.5(ii) and 4.1 re-read: same verdict |
| A344173 (primes `x³+2y³` that are QNRs) | Sun | not multiplicative. Not GRH |

## Novelty search, line by line (2026-11-26)

| Where | Queries | Found |
|---|---|---|
| OEIS (via Exa fetch; direct access is behind Cloudflare) | A034694, A034693, A085420, A053760, A020649, A000229, A306530, A354597, A344173 | the conjectures in the table above. No comment claims a GRH proof of anything new |
| arXiv / web (Exa ×7) | least strong witness conjecture; least prime QR explicit bound and conjecture; least prime QR, KKS exception, QRH; Pollack mod-4 QNR; Benli–Pollack `k`-th power residues; EKN exponent; class numbers beyond 100 under GRH | KKS 2012 (B1, B2); Pollack 2018; Gica 2006; Benli–Pollack 2018 (no explicit conjecture); CMQR arXiv:2404.08380 (`r_p` asymptotic constant `0.7615`); EKN 2020; Garcia et al.; Holmin et al.; zeta-lab; Jaswal; DrMurphyIsIn; Mosunov–Jacobson |
| Zenodo (via Exa) | QRH/GRH notes on least residues and class numbers | dr vengy 23607810 (`r_p ≪ log⁸ p` under QRH); Jaswal 23251443. Nothing on KKS's `√p` theorem or `β(1/3)` |
| MathOverflow (via Exa) | least prime QR; least non-residue of `−n` | MO 263360, MO 426966 (GRH proofs in the answers) |
| formal-conjectures clone `9097e2f` | `git grep` for least prime quadratic residue, Knapp, Gica, norm-Euclidean, Linnik, least prime in a progression, class-group exponent | only unrelated hits (no Linnik-type or KKS statement) |
| formal-conjectures PRs (`gh pr list --state all --search`) | "least prime quadratic residue", Knapp, norm-Euclidean, Linnik, "least prime arithmetic progression", "quadratic nonresidue" | #8059 (open; adds Wikipedia prime/L-function conjectures, not read in full *(unverified)*), #7425, #8195. Nothing on B1 or B2 |
| 1337isnot1337/solved-conjectures clone | `git grep` for quadratic residue, Knapp, norm-Euclidean, Linnik, least prime | nothing relevant |
| openai/math | not searched separately (its QRH preprint was found via Exa) | QRH paper2 lists least-non-residue corollaries, not KKS |

## Not reached

- Guy's UPINT (F-section on residues) and Ribenboim's lists. I had no searchable text.
- McGown's and Lezowski–McGown's norm-Euclidean papers (degrees 5, 7 and up). I did not re-read
  them for undecided conductors.
- Treviño's `k`-th power non-residue paper (JNT 2015), for any stated open problem.
- A broad OEIS keyword sweep. Cloudflare blocks OEIS search, so only single entries fetched
  through Exa were read.
- The full text of Jaswal's Zenodo note: does it already remove the KKS exception?
