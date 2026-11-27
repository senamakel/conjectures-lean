# OMA open-result fleet

27 November 2026. Ten Luna workers screened distinct mathematical families at
the OMA pin (Formal Conjectures `9097e2f90e66`, Lean `v4.33.1`). The target is
100 newly merged proofs, disproofs or substantive proof steps for open results.
None of this wave's candidates reached that state. Two reductions from the
previous wave merged and are tracked separately. The Lindelöf statement
submission remains distinct from a proof. [Erdős 770 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4219) · [Robin reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4271) · [Lindelöf statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4230)

| Lane | Triage evidence |
| --- | --- |
| Erdős 250–349 and Agoh–Giuga | Erdős 307's coprimality variant already has live proof PRs. Erdős 287's prime variant remains genuinely open. The Agoh–Giuga target already has a reduction, with unresolved substantive hypotheses. [Erdős 307 PR #4257](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4257) · [Agoh–Giuga reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/919) |
| Erdős 500–899 | The Erdős 506 small-`n` target has an upstream missing answer definition. The apparent finite lead at Erdős 723 would require a projective plane of order 12. Erdős 473's new prime-circle reduction leaves universal existence in two residue classes mod 4. Bounded witness generation found circles for every even order 18–32, leaving the general step unresolved. [Prime-circle reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4309) · [Unquantified large-order result](https://arxiv.org/abs/2609.19114) |
| Erdős 1–249 and 900+ | Erdős 102's implication from Erdős 101 is already referenced in the problem source. The live brief for Erdős 133 flags a prior disproof. Erdős 1053 and 1055 had no concrete bridge. Erdős 1186 had public Lean proof reports and existing OMA bounds work. Erdős 1160 already has a pending reduction step. [Erdős 102](https://www.erdosproblems.com/102) · [Erdős 1186 related OMA work](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3344) · [Erdős 1160 PR #4376](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4376) |
| Algebra, geometry and Green | The low-dimensional Dixmier and Poisson targets have no short bridge in the pinned imports. Green 40's all-`n` version remains an open asymptotic problem. The Maxwell H2 desk brief returned 404, and Kintali's preprint already treats the collinear three-charge bound with the critical-circle argument. [Green 40](https://lefttosolve.com/p/Green40.green_40.variants.all_n) · [Maxwell reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4126) |
| ABC and Cramér | The proposed ABC route is the published equivalence of formulations. The Cramér route requires the open Firoozbakht input. The ABC lease attempt returned HTTP 500. [ABC equivalence](https://arxiv.org/abs/1409.2974) · [Firoozbakht reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3997) |
| OEIS and reused proofs | A069004 and A105751 had overlapping PRs. A103662's newly merged reduction leaves the decimal-zero property for all `2^(40k)` and mixed even bases coprime to 5. A157237's uniform three-term representation exceeds what the existing Romanoff density lemmas supply. [A103662 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4284) · [A157237](https://oeis.org/A157237) |
| Other reduction steps | A069191's rank-one Hermitian interlacing obligation appears in the merged Lean file. Its exact API endpoint returned `not_found` and the lease request returned HTTP 500. Mathlib had ordered Hermitian eigenvalues but the search located no rank-one interlacing theorem at the pin. [Reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4154) · [Desk incident](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues/3627) |

## Crystal component collision search

The crystal target asks whether `n = ab` determines the unordered pair
`{a,b}` among pairs of odd factors greater than 1 for which the biharmonic
mean is integral. Prior search covered minimum half-component through
1,500,000. The recurrence in Theorem 4 gives a cheap way to test an additional
product interval where different recurrence parameters could lead to the same
product. [Open target](https://lefttosolve.com/p/Arxiv.1601.03081.crystals_components_unique) · [Source and recurrence](https://arxiv.org/abs/1601.03081) · [Earlier range](easy-open-sweep.md)

Using the paper's parameter `w`, start at `(s,t) = (w,(w−1)^2)` and advance to
`(t,(w−2)t+2−s)`. For `w ≥ 4` the half-components increase. The first product
`(2w−1)(2(w−1)^2−1)` increases with `w` and gives a bound on the parameter
for any product limit. Parameters below 4 give only the small case 35 or a
factor 1. Enumerate `4 ≤ w ≤ 3,000,000` up to product
107,999,910,000,017,999,999, retaining only products strictly above
13,499,977,500,008,999,999, then sort by product and compare adjacent rows.
This checks a new product interval beyond the old minimum-component cutoff.
Stop at the first distinct-pair collision or after enumerating and sorting the
interval, with a 30-second wall limit. The C++ search used unsigned 128-bit
products. It found no collision among 1,532,047 pairs in 0.16 seconds with
approximately 67 MiB peak memory. This finite search has no Lean certificate.
