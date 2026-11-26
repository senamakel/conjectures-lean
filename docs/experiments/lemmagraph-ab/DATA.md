Harness-measured per arm (duration from the Agent tool; agents' own timestamps were unreliable). All 12 final files re-elaborated by the orchestrator: no errors, no sorry.

| round | task | arm | wall s | tokens | tool uses | lean runs | lemmagraph calls (useful) | greps | wrong-name errors |
|---|---|---|---|---|---|---|---|---|---|
| 1 | frattini (Frattini criterion + CRT torsion, new proofs) | A | 43 | 79,488 | 7 | 3 | 0 (0) | 0 | 1 |
| 1 | frattini | B | 43 | 77,327 | 9 | 4 | 0 | 3 | 1 |
| 1 | places (grh port drift fix, Places.lean) | A | 174 | 109,280 | 22 | 9 | 0 (0) | 8 | 0 |
| 1 | places | B | 81 | 95,551 | 13 | 7 | 0 | 5 | 0 |
| 2 | torsion (bach-sharp-gap step 2, three new lemmas) | A | 114 | 112,409 | 12 | 4 | 5 (5) | 0 | 0 |
| 2 | torsion | B | 88 | 93,933 | 11 | 4 | 0 | 3 | 0 |
| 2 | discreteunits (grh port, fun_prop continuity) | A | 124 | 98,053 | 12 | 5 | 1 (1) | 1 | 0 |
| 2 | discreteunits | B | 130 | 84,657 | 8 | 5 | 0 | 0 | 0 |
| 2 | mellin (grh port, MellinTheta.lean) | A | 190 | 102,024 | 12 | 5 | 3 (1) | 0 | 0 |
| 2 | mellin | B | 267 | 82,678 | 8 | 4 | 0 | 2 | 0 |
| 2 | measplace (grh port, Measure/Place.lean; ~160 s per elaboration) | A | 887 | 136,526 | 18 | 4 | 5 (3) | 1 | 0 |
| 2 | measplace | B | 875 | 88,220 | 14 | 5 | 0 | 4 | 0 |

Totals: A 1,532 s, 637,780 tokens, 30 lean runs; B 1,484 s, 522,366 tokens, 29 lean runs.
Round 1: arm A was told "first resort" and made zero calls. Round 2: arm A had a mandatory procedure (premises on every goal before grep, call ledger calls.jsonl).

Qualitative (from the agents' notes and ledgers):
- torsion A: the key lemma ZMod.isCyclic_units_two_pow_quotient_neg_one came from text_search at rank 2; agent says it would not have recalled it. Arm B found the same lemma by grepping UnitsCyclic.lean. premises on the goal returned only generic group lemmas (orderOf_dvd_card rank 7, orderOf_dvd_of_pow_eq_one rank 1), not the specific cyclic-units lemmas; search/text_search did.
- discreteunits A: premises ranked Continuous.comp 1 and continuous_of_discreteTopology 19; agent would have recalled both; B recalled from memory. Time went to elaboration order, not lemma finding.
- mellin A: get_declaration gave the exact signature of mellin_differentiableAt_of_isBigO_rpow_exp (useful); both premises calls returned mostly instance noise (Real.borelSpace, IsScalarTower.*). All fixes were local syntactic drift.
- measplace A: premises surfaced Real.eNorm_eq_ofReal (rank 29) and ENNReal.ofReal_pow (rank 39); "probably would have found them anyway". get_declaration confirmed Set.Mem.intro is gone; text_search for a repo-local lemma returned junk (repo not indexed). Wall time dominated by 160 s elaborations.
- Same fixes found by both arms in every pair.

Tasks were all WIP items: PR #31 (grh-compact port) files Places, MellinTheta, DiscreteUnits, Measure/Place; PR #29 (bach-sharp-gap) Frattini criterion and torsion bounds. All 12 results are correct; one version of each is being landed on those PRs.
Untested: discovery (finding conjectures/connectable lemmas) and tasks far from the model's recall.
