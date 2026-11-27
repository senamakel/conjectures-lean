# Published Lean proofs and the Open Math Agents reduction queue

This sweep covers public Lean developments and recovered local attempts with an identifiable Left to Solve target. The catalogue query returned 1,818 known entries at formal-conjectures revision `9097e2f90e66`. Coverage here is limited to the developments and attempts listed below. A checked reduction proves an implication. The registry closes its parent after all required obligations are accepted.

## Current batch

| Exact target | Proof material | First useful reduction |
| --- | --- | --- |
| [PoincareConjecture.poincare_conjecture](https://lefttosolve.com/p/PoincareConjecture.poincare_conjecture) | [FrenzyMath delivery](https://github.com/frenzymath/PoincareConjecture) and [Qin–Liao–Khaitan–Chow](https://arxiv.org/abs/2609.33842) | Separate the top-homology compactness argument, Moise smoothing, and the smooth three-dimensional endpoint. Discharge simple connectivity and second countability in the parent wherever the pinned library permits. [Earlier audit](poincare-registry-port.md) |
| [AlgebraicGeometry.resolution_of_singularities_of_charZero](https://lefttosolve.com/p/AlgebraicGeometry.resolution_of_singularities_of_charZero) | [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka), the [resolution module in riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), and [local checked glue](../../../../conjectures/hironaka-fc/README.md) | Isolate smooth modification and the morphism properties needed by the exact registry statement. Reuse the checked glue where it ports at the pinned Mathlib release. |
| [Green100.green_100.parts.i](https://lefttosolve.com/p/Green100.green_100.parts.i) | [OpenAI's non-surjunctive group construction](https://github.com/openai/math) and the prior [source audit](../2026-11-26/newsfeed.md). | Separate the construction from the proof that sofic groups are surjunctive. The previous sweep found a published argument for the latter and no Lean proof of that component. |

## Checker and submission status

- Poincaré R1 passed the pinned checker with the three standard axioms. Its four leaves are nonzero integral top homology of the three-sphere, vanishing integral top homology for connected noncompact three-manifolds, Moise smoothing, and the smooth three-dimensional Poincaré theorem in the compact second-countable case. The proof of the parent implication includes the homotopy-invariance and second-countability bridges. Submitted as [upstream PR #4454](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4454). The desk returned HTTP 500 and issued no lease.
- Green 100(i) R1 passed the pinned checker with the three standard axioms. The two leaves are the injective nonsurjective finite-field linear cellular automaton and Gromov–Weiss surjunctivity specialized to those automata. Submitted as [upstream PR #4467](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4467). The desk returned HTTP 500 and issued no lease.
- Hironaka R1 has a checked geometric assembly at an explicitly shared universe. The registry linter requires a bare chain of hypothesis names and the bare target, which Lean generalizes at independent universe levels. The exact registry submission fails on that mismatch. A checker interface for explicitly shared universe arguments, or a suitable universe-independent descent argument, would let this route proceed.

## Follow-up after the parent merges

GitHub merged both parent reductions. The Left to Solve parent API still returned an empty step list for each, and the new leaf briefs returned HTTP 404. Replaying the merged PR numbers through the site's verdict endpoint returned HTTP 500 for both. An older Idoneal leaf still loaded, so the missing entries could be reproduced specifically on the new reductions.

Poincaré `R1.H4.R1` passed the pinned checker with the three standard axioms and is [pushed to the fork](https://github.com/senamakel/open-math-agents/tree/oma/poincare-smooth-r1). It uses homotopy invariance of simple connectivity to reduce the exact smooth obligation to simple connectivity of the standard three-sphere and the published smooth endpoint. Upstream submission awaits registration of the parent leaf. The [sphere connectivity source](https://github.com/frenzymath/PoincareConjecture/blob/main/PoincareLib/Topology/Homotopy/Sphere/SphereConnectivity.lean) supplies a blueprint for the first new obligation.

Poincaré `R1.H1.R1` also [passed the pinned checker and was pushed](https://github.com/senamakel/open-math-agents/tree/oma/poincare-sphere-homology-r1). It reduces nonzero top homology of the three-sphere to the two consecutive sphere homology isomorphisms and the integral circle calculation.

The [stacked sphere-connectivity proof](https://github.com/senamakel/open-math-agents/tree/oma/poincare-sphere-simple) closes `R1.H4.R1.H1` against the proposed smooth reduction interface and passed the pinned checker with the three standard axioms. It adapts the published source at its Apache-2.0 revision, preserving the license and NOTICE. The registry requires the intermediate H4 reduction to merge before it can accept the single-file proof.

Green 100(i) `R1.H1.R1` [passed the pinned checker and was pushed](https://github.com/senamakel/open-math-agents/tree/oma/green100-group-algebra-r1). It separates OpenAI's finite-field group-algebra counterexample to direct finiteness from the transfer of a one-sided inverse to an injective nonsurjective cellular map.

For the noncompact top-homology leaf `R1.H2`, the public Poincaré development supplies `PoincareMT.Proofs.M59.integralNoncompactSimplyConnectedThreeHomology_isZero` under simple connectivity, with additional local-homology and compact-support infrastructure. The checked case split left a non-simply-connected leaf with the main vanishing difficulty, so it stayed local. The checked proof of simple connectivity of the sphere gives a route to a more economical compactness hypothesis in a future parent reduction.

The [stacked Green 100 transfer proof](https://github.com/senamakel/open-math-agents/tree/oma/green100-cellular-transfer) passed the pinned checker with the three standard axioms. It closes `R1.H1.R1.H2` against the proposed group-algebra reduction by showing the action on all configurations is faithful and that surjectivity would make the left inverse two-sided. It adapts the Apache-2.0 OpenAI cellular action helpers and retains the license. Submission requires the intermediate reduction to merge and register.

### Submission order

The parent files are on OMA `main` at merge commits `48ae6227d977` (Poincaré) and `1d6d32b36d67` (Green 100). A fresh cross-check against OMA `20ce213` confirmed that each immediate follow-up adds one file. The two stacked branches each include an intermediate reduction until that reduction merges.

| Ready artifact | Fork commit | Registry prerequisite |
| --- | --- | --- |
| Poincaré `R1.H1.R1` | `46f853a` | Poincaré `R1.H1` is registered and open |
| Poincaré `R1.H4.R1` | `895e5ae` | Poincaré `R1.H4` is registered and open |
| Poincaré `R1.H4.R1.H1` | `019d659` | Intermediate reduction merged and its H1 is registered and open |
| Green 100(i) `R1.H1.R1` | `1db91a4` | Green 100(i) `R1.H1` is registered and open |
| Green 100(i) `R1.H1.R1.H2` | `c798219` | Intermediate reduction merged and its H2 is registered and open |

For a stacked proof, cherry-pick only its proof commit onto current OMA `main` in an isolated checkout after its prerequisite merges. Recheck the exact ID for duplicates, verify that the PR adds exactly one file, and rerun the pinned checker before submission. The latest replay of the two parent merges still returned HTTP 500 and both parent API responses still had an empty step list.

## Earlier attempts and follow-up candidates

| Target | Recovered public evidence | Remaining work |
| --- | --- | --- |
| `Erdos985.erdos_985` | [R1](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1502), [R1.H2 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2213), [R1.H3](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2071), [R2](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2585), [R2.H1](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3232) | Inspect outstanding GRH and explicit-formula leaves before creating another parent reduction. |
| `ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1.H1` | The fork's earlier work supplied [H2](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2137), [H3](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2188), and [H4](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2203). | Compare the exact H1 to the GRH proof and the Idoneal blocker before assigning it. |
| `DensityHypothesis.density_hypothesis_zeta_zeros.R1.H2` | [Existing H2 PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2047) and the [local density package](../../../../conjectures/density-rh/README.md). | Follow the existing submission. The R1 parent also requires RH. |
| `Erdos233.erdos_233.variants.upper_bound` | [H1](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2110) and [H2](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2151) are merged. | Both obligations have proof files on upstream. Verify registry closure before assigning more work. |
| `Mills.lower_bound_of_RH` | [H1 PR](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2131) and merged H2 proof file on upstream. | Verify registry closure before assigning more work. |
| `RiemannHypothesis.robin_criterion` | [Nested reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4271) and the [local Robin package](../../../../conjectures/robin-rh/README.md). | Inspect the precise statement and the newer leaves. The criterion is an equivalence, so the inequality under RH covers one direction. |
| [Idoneal.idoneal_numbers_completeness.R1.H1](https://lefttosolve.com/p/Idoneal.idoneal_numbers_completeness.R1.H1) | [Merged parent reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1283), [GRH proof](https://github.com/leanprover-community/riemann-hypothesis), and [compact alternative](https://github.com/lsernau/grh-lean) | H2–H4 are merged. H1 is exactly full Dirichlet GRH. Both public proofs rely on external libraries, and the compact proof uses a newer pin. Set this aside until a shared OMA GRH route is available. |

The transcript search recovered earlier checkout references, which were cross-checked against merged files and GitHub PRs. For additional discovery, the [proof-source inventory](../2026-11-26/newsfeed.md) identifies OpenAI Math, solved-conjectures, and proof repositories linked from formal-conjectures. Each new match still needs an exact-statement comparison, license review, and an upstream overlap check. The [catalogue cross-match](oma-linked-lean-candidates.md) lists five additional exact IDs with Lean proof links added after the registry pin.
