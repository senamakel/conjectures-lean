# A245211 R1 squarefree Omega 6 discovery (2026-11-27)

## Exact live reduction

`python3 scripts/attack.py steps OeisA245211.conjecture` at the local OMA upstream snapshot reported parent R1 PR #733 merged (upstream commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`) and two open leaves:

- `OeisA245211.conjecture.R1.H1`: every fixed point has two distinct prime factors of multiplicity one.
- `OeisA245211.conjecture.R1.H2`: a finite divisor exclusion for complementary factors at a nontrivial cofactor.

`gh pr view 733 --repo GuillaumeBAUD-coder/open-math-agents` confirms merged 2026-11-26; it adds only `reductions/OeisA245211.conjecture.R1.lean`. The direct brief endpoint returned 404. `gh search prs` found only #733; a code search finds this reduction file. Current local registry snapshot reported both leaves `solved: false`.

## Prior-art stop

Exa search on 2026-11-27 for A245211 and squarefree Omega 6 surfaced a public post by Ava (@ehh_ssu), timestamp 2026-11-22, stating a Lean 4 proof that 21 is the only fixed point with `Omega(n) <= 6`, across all exponent partitions; it links Zenodo record 24437886 (version 1.1.0) and names `OmegaSix.lean`. That theorem directly contains the proposed squarefree Omega 6 case. Do not pursue or claim this finite closure as a novel result.

Primary starting references:
- https://zenodo.org/records/24437886
- https://aixiv.online/problems/krizeks-fixed-point-question-for-oeis-a245211
- https://oeis.org/A245211
- OMA reduction PR: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/733

Earlier aiXiv paper 2611.02431 (public 2026-11-22) establishes exclusions through Omega 5 and bounds the squarefree Omega 5 smallest prime by 17, but the later Omega<=6 claim supersedes this as a novelty avenue.

## Search record and limits

- Exa queried exact A245211/Omega 6, squarefree Omega 6, and the proposed 65/64 Euler-product route.
- LemmaGraph `origin=oma/` search found the exact OMA reduction definition and open leaf statements, but no Omega 6 proof (its corpus includes OMA merged artifacts, not arbitrary Zenodo uploads).
- `gh search prs` and `gh search code` against `GuillaumeBAUD-coder/open-math-agents` found PR #733 and the merged R1 reduction.
- Local transcript command `python3 scripts/attack.py history 'OeisA245211'` was started; output had not completed at note time.
- LivingBrain was unavailable: no LivingBrain tools were loaded in this session, so no memory search was performed.

No Lean proof was started and no OMA lease or submission was made.

## Artifact-level verification

Downloaded the public v1.1.0 Zenodo archive into this ignored scratch directory and inspected `lean/oeis-a245211/OeisA245211/OmegaSix.lean` directly. It closes exactly the proposed squarefree `Omega=6` case:

- `omegaSix_must_be_squarefree_ge_37`: any fixed point with `omegaBig n = 6` is squarefree `p*q*r*s*t*u` with `37 ≤ p < q < r < s < t < u`.
- `six_prime_growth_bound`: for `p ≥ 181`, the product `(2p+1)…(2u+1) < 65*p*q*r*s*t*u`, contradicting the fixed-point identity.
- `six_prime_moment_ne`: for the remaining `30` possible smallest primes `37 ≤ p < 181`, Cunningham forced closure rules out the equality.
- `not_isFixedPoint_of_omegaBig_eq_six` and `fixedPoint_eq_21_of_omegaBig_le_six` close the full six-multiplicity case and all cases `Omega ≤ 6` respectively.

The exact local idea is already covered. No proof experiment is warranted. `python3 scripts/attack.py history 'OeisA245211' --limit 30` completed and returned no matching local transcripts.
