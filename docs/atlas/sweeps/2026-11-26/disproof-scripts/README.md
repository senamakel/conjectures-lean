# Search and verification scripts, refutation lane, 2026-11-26

Copies of the scripts the sweep agents wrote, kept so the searches recorded in the
`disproof-*.md` reports beside this folder can be rerun. They are working scripts, not a
library: unreviewed, uncommented in places, and written for one run each. A report's claim is
only as good as the check it describes; nothing here is a Lean proof.

| Folder | Report | Content |
| :--- | :--- | :--- |
| `hunt/` | `disproof-hunt.md` | spectral-corpus annealing, tree domination polynomials to `n = 28`; `runs/hits.jsonl` holds the six witness graphs |
| `hints-epoch/` | `disproof-oeis-neighbours.md` | Sun's sparse-sum representation scans (`sun3.c`), the exact checks of `235644514` and `9974943843` |
| `nb-comb/` | `disproof-1337-neighbours.md` | Gawron–Miska–Ulas congruences, distance-graph independence ratios |
| `verify-hits/` | `disproof-1337-neighbours.md` | the independent re-check of those two hits |
| `hunt-ineq/` | `disproof-inequalities.md` | the inequality searches (all negative) |
| `polya/`, `sieve/` | `conjectures/polya-liouville` | recomputation of `L(906150257)` and `M(7725038629)`; the auditor's segmented sieve |
| `hajos-audit/`, `granville-audit/` | PRs #17, #16 | the auditors' independent checks |
