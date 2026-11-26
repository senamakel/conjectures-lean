# lemmagraph A/B experiment, rounds 1-2 (2026-11-26)

## Question

Does the lemmagraph MCP speed up solving and discovery on our Lean work?

## Design

Paired arms, same model (Sonnet), same task, run by OpenHuman agents.

- **Arm A (lemmagraph).** Round 1: the tools were offered as the "first resort", optional.
  Round 2: a mandatory premises-first procedure (call `premises` on every goal before grepping,
  `get_declaration`/`text_search` for unknown names after the Mathlib bump, `search` for idea-level
  questions) with a call ledger, one line per call, in `calls-A.jsonl`.
- **Arm B (control).** No lemmagraph; grep over Mathlib, `#check`, `exact?`.
- **Tasks.** Six work-in-progress items: PR #31 (grh-compact port: Places, MellinTheta,
  DiscreteUnits, Measure/Place) and PR #29 (bach-sharp-gap: Frattini criterion, torsion bounds).
- **Measured.** Wall time and tokens and tool uses as reported by the harness (the agents' own
  timestamps were unreliable); Lean runs, lemmagraph calls and useful hits, greps and
  wrong-name errors, self-reported in each `log-*.json`. All 12 final files were re-elaborated
  by the orchestrator: no errors, no `sorry`.
- **Index.** Mathlib `fc4f59e5` in full (Lean core and Batteries included), served read-only and
  unchanged during the run. No repo corpus (our repo and riemann-hypothesis are not indexed).

Protocols: [round 1](lemmagraph-ab/round1/PROTOCOL.md), [round 2](lemmagraph-ab/round2/PROTOCOL.md),
[round 2 tasks](lemmagraph-ab/round2/TASKS.md). Ledgers and logs are under
[`lemmagraph-ab/`](lemmagraph-ab/); the raw table is [`DATA.md`](lemmagraph-ab/DATA.md).
The Lean files are not kept.

## Results

| round | task | arm | wall s | tokens | tool uses | Lean runs | lemmagraph calls (useful) | greps | wrong-name errors |
|---|---|---|---|---|---|---|---|---|---|
| 1 | frattini | A | 43 | 79,488 | 7 | 3 | 0 (0) | 0 | 1 |
| 1 | frattini | B | 43 | 77,327 | 9 | 4 | 0 | 3 | 1 |
| 1 | places | A | 174 | 109,280 | 22 | 9 | 0 (0) | 8 | 0 |
| 1 | places | B | 81 | 95,551 | 13 | 7 | 0 | 5 | 0 |
| 2 | torsion | A | 114 | 112,409 | 12 | 4 | 5 (5) | 0 | 0 |
| 2 | torsion | B | 88 | 93,933 | 11 | 4 | 0 | 3 | 0 |
| 2 | discreteunits | A | 124 | 98,053 | 12 | 5 | 1 (1) | 1 | 0 |
| 2 | discreteunits | B | 130 | 84,657 | 8 | 5 | 0 | 0 | 0 |
| 2 | mellin | A | 190 | 102,024 | 12 | 5 | 3 (1) | 0 | 0 |
| 2 | mellin | B | 267 | 82,678 | 8 | 4 | 0 | 2 | 0 |
| 2 | measplace (about 160 s per elaboration) | A | 887 | 136,526 | 18 | 4 | 5 (3) | 1 | 0 |
| 2 | measplace | B | 875 | 88,220 | 14 | 5 | 0 | 4 | 0 |

| | wall s | tokens | Lean runs |
|---|---|---|---|
| A total | 1,532 | 637,780 | 30 |
| B total | 1,484 | 522,366 | 29 |

## Findings

(a) No measurable speed-up on these six tasks. Total wall time was 1,532 s (A) against
1,484 s (B), with 30 against 29 Lean runs, and every pair found the same fix.
(b) Arm A used about 22% more tokens (637,780 against 522,366).
(c) Unprompted, the agents never called it: in round 1 arm A made zero calls despite "first resort".
(d) The useful calls were exact-name tools. In torsion, `text_search` returned
`ZMod.isCyclic_units_two_pow_quotient_neg_one` at rank 2, which the agent says it would not have
recalled; arm B found the same lemma by grepping `UnitsCyclic.lean`. In mellin, `get_declaration`
gave the exact signature of `mellin_differentiableAt_of_isBigO_rpow_exp`. In measplace,
`get_declaration` confirmed that `Set.Mem.intro` is gone.
(e) `premises` returned generic or instance-noise lemmas on these goals. On the torsion goal it
gave general group lemmas (`orderOf_dvd_card` rank 7, `orderOf_dvd_of_pow_eq_one` rank 1), not the
cyclic-units lemmas. In mellin both calls returned mostly instances (`Real.borelSpace`,
`IsScalarTower.*`). The lemmas actually used sat at ranks 1 and 19 (discreteunits:
`Continuous.comp`, `continuous_of_discreteTopology`, both of which the agent would have recalled)
and 29 and 39 (measplace: `Real.eNorm_eq_ofReal`, `ENNReal.ofReal_pow`, "probably would have
found them anyway"). A `text_search` for a repo-local lemma returned junk, since the repo is not
indexed.
(f) The bottleneck was elaboration (Measure/Place, about 160 s per run) and elaboration-order
fixes, not lemma lookup. The remaining fixes were local syntactic drift.

## Limits

- n = 6 pairs, one model, one run per arm, so variance between runs is unknown. Differences of
  tens of seconds (for example mellin, 190 s against 267 s) are within what we would expect from
  noise on a shared box.
- The tasks were within the model's recall, which is where retrieval helps least.
- Lemmagraph calls, useful hits, greps and error counts are self-reported by the agents.
- No discovery task was run (two arm directories were created and left empty).
- Round 1 arm A made no calls, so only the four round 2 pairs test the tool.

## Next

- Goals outside the model's recall (lemmas it cannot name from memory).
- A discovery A/B: finding connectable lemmas for an open statement.
- Larger n with repeated runs per arm, to get a variance estimate.
- Feedback for lemmagraph: filter instance and typeclass declarations out of `premises` results;
  index this repo and riemann-hypothesis so repo-local lemmas resolve.
