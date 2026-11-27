# Open Math Agents fleet research notes

These notes summarize the 27 November 2026 fleet's local proof work, coordination briefs and port reports. The reviewed OMA catalogue pins formal-conjectures at `9097e2f90e66`, Lean at `v4.33.1`, and Mathlib at `0df444a`. The current submission pin comes from the checkout used to submit. The merged examples below were cross-checked against the OMA commit history. Local artifacts and port reports retain their original evidence level. [Catalogue snapshot](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/ea1ab6394ba60f3b80439548deb8baba0838c75c/data/catalog.json)

## Reusable premises

| Premise | Where to find it | What it gives |
| --- | --- | --- |
| Sylvester–Schur | Fleet `w4scratch/sylv/S1.lean`, theorem `sylvester`. [Merged Erdős 961 variant](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1476) | For positive `k` and `2*k ≤ N`, some prime `p > k` divides `N.choose k`. Useful for binomial coefficients and consecutive products. |
| Mertens estimates | Fleet `lib/Mertens.lean`, namespace `OMALib.Mertens` | `mertens1`, `mertens2`, `mertens3`, `abs_sum_inv_sub_log_log_le`, and `prod_one_sub_inv_bounds` cover the weighted prime sum, reciprocal prime sum and Euler product. |
| Selberg sieve and prime pairs | Fleet `lib/Sieve.lean` and `lib/SieveUnconditional.lean`, namespace `OMALib.Sieve` | `selberg_sieve_abstract`, `selberg_residue_level`, and `card_primes_ap_le_sieve` give abstract and explicit-level bounds. `prime_pairs_upper_bound'` gives one absolute constant for even shifts `d > 0` and natural `x ≥ 2`, with bound proportional to `x / log² x` times `pairSingularProduct d`. |
| Romanoff | Fleet `rom-scratch/{A,Ab,B,C,D16}.lean`. [Merged Erdős 244 variant](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3322) · [Merged Erdős 16 leaf](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3167) | Multiplicative-order sums for powers of 2 and general bases, collision bounds, and density arguments. The split locates the analytic input for related prime-plus-power problems. |

The local paths above are relative to the fleet run directory. Verify the declaration, import closure, license and axioms at the destination pin before using a premise. Use landed OMA proofs to trace the method and credits. OMA and this repository have different certificate and submission rules.

## Patterns that paid off

- Look for a variant with an existential constant and one substantive lemma already in Mathlib. The dimension-one Erdős 657 upper bound uses Behrend's Roth lower bound. The Erdős 53 upper variant uses smooth numbers and a Chebyshev prime bound. [Erdős 657](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1187) · [Erdős 53](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1221)
- Separate counting from geometry. For the Erdős 1087 upper variant, a Kővári–Sós–Turán count uses the bound on intersections of two circles. [Merged PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1230)
- Compare the formal quantifiers with the source before treating an easy proof or small witness as a mathematical result. Check natural subtraction and division, empty extrema and exceptional values. Record a weakened statement or misformalisation with the exact discrepancy. The Friedlander–Granville variant illustrates how changing the summation range changes the problem. [Merged PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1173)
- Check the axiom dependencies of target definitions early. The fleet flagged the choice of a density using an unfinished existence lemma in Erdős 697. For scratch diagnostics inspect `#print axioms`. The submitted file must pass the registry lint and pinned checker. [Lint](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/ea1ab6394ba60f3b80439548deb8baba0838c75c/tools/lint.py)

## Port attempts to avoid repeating

Fleet port reports measured source and investigated statement applicability. These are historical blockers at the reviewed OMA pin. The checker applied a 512 KiB file limit, a syntax whitelist, and a standard-three-axiom check.

| Exact ID | Reported blocker | Condition for retrying |
| --- | --- | --- |
| `Erdos173.erdos_173` | About 1.17 MB of Lean across the source and its vendored modules, with Lean module commands and lint violations. The fleet stopped before a full statement comparison. | Identify a small dependency closure or a mathematical reduction, then confirm the statements match. [Source](https://github.com/plasma-ai/erdos-173) |
| `Erdos1207.erdos_1207` | Source remained about 591 KB after comment removal. A partial elaboration showed significant Mathlib drift from Lean 4.27.0. | Reuse a port of the number-field tower lemmas or find an independent small leaf. [Source revision](https://github.com/tadamcz/erdos1207/tree/228fcd87) |
| `Green49.green_49` | The improved PFR theorem was identified as the relevant premise. Its 44-module closure includes entropy and disintegration infrastructure. Splitting the proof would duplicate that infrastructure across leaves at this pin. | Make the shared entropy API available at the submission pin or identify leaves that avoid it. [Source revision](https://github.com/teorth/pfr/tree/1899ce8ed95fc310cce53d4c7ecfa2beb20ebec4) |
| `Erdos768.erdos_768` | About 900 KB after aggressive trimming, with a prime-number-theorem dependency and a real-indexed limit in the source where the target uses natural indices. The source is associated with an unrefereed claim. | Establish the limit bridge and find a small route with the necessary prime-counting input. [Source revision](https://github.com/ericlisg/erdos768-lean/tree/e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9) |
| `SidorenkoConjecture.sidorenko_conjecture_graphon` | The finite-host counterexample has a roughly 1.15 MB trimmed closure. The target also needs the step-graphon bridge preserving edge and homomorphism densities. | Build the bridge independently and find an admissible checked interface to the finite counterexample. [Source revision](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sidorenko) |

Measure reachable UTF-8 bytes and inspect lint-sensitive syntax before porting. For a reduction, estimate each leaf's shared dependencies and identify what the pinned checker actually imports. Keep the primary-source status, statement bridge and checker feasibility in the research record even when a route is parked.
