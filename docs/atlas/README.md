# Implication atlas

Edges between results: "from `X`, `Y` follows". The atlas is how targets are found. An open `Y`
whose `X` is proved in Lean is a theorem waiting to be written; an open `Y` whose `X` is itself
open gives `theorem Y_of_X`, which becomes unconditional the day `X` is proved.

It complements the [Conjecture Atlas](https://github.com/senamakel/tiny-cortexdb-mathagent),
which scores problems one at a time. This one records the links between them, with the source of
each deduction and, for edges we rejected, the reason.

## Files

| File | Content |
| :--- | :--- |
| `edges.jsonl` | one JSON object per implication edge, kept or rejected |
| `sweeps/2026-11-26/toolkit-reuse.md` | opens with the premise inventory: our theorems with their constants and thresholds |
| `sweeps/` | the report of each discovery sweep, by date and lane |

## Edge schema

| Key | Meaning |
| :--- | :--- |
| `premise` | the result `X` |
| `premise_status` | `lean-proved`, `theorem` (published, not in Lean), `claimed`, `open` |
| `premise_lean_source` | repository, path and declaration when `X` is in Lean |
| `consequence` | the result `Y` |
| `consequence_ref` | formal-conjectures path and declaration, Erdős number, Atlas id, or a citation |
| `consequence_status` | `open`, `partially`, `solved` |
| `implication_source` | where the deduction is published |
| `effort` | `S`, `M`, `L`, `XL` |
| `lean_exists` | where a Lean proof of `Y` or of `X ⇒ Y` already exists; empty if none was found |
| `in_1337` | whether 1337isnot1337/solved-conjectures lists `Y` as settled |
| `class` | `1`: `X` is proved in Lean, so `Y` can be unconditional. `2`: `X` is open |
| `notes` | the catch, the finite range, the reason for a rejection |
| `sweep`, `lane` | the sweep date and the lane that found the edge; the same edge can appear from two lanes |

## Sweeps

| Date | Lanes | Status |
| :--- | :--- | :--- |
| 2026-11-26 | [formal-conjectures conditional scan](sweeps/2026-11-26/fc-scan.md); [solved-conjectures newsfeed](sweeps/2026-11-26/newsfeed.md) (with an [inventory of 1337isnot1337/solved-conjectures](sweeps/2026-11-26/newsfeed-1337-inventory.md)); [Conjecture Atlas](sweeps/2026-11-26/atlas.md); [reuse of our theorems](sweeps/2026-11-26/toolkit-reuse.md); [implications between open conjectures](sweeps/2026-11-26/implications.md); [Erdős status feed](sweeps/2026-11-26/erdos-feed.md); [lemma mining of big proofs](sweeps/2026-11-26/lemma-mining.md) (inventories: [external](sweeps/2026-11-26/lemma-mining-external-inventory.md), [local](sweeps/2026-11-26/lemma-mining-local-inventory.md)) | 268 edges |

The sweep reports are research notes: nothing in them was built, and claims marked
*(unverified)* were not checked against a primary source. An edge is confirmed only when its
Lean proof is merged.

## Edges proved so far

Merged into [`conjectures/implications`](../../conjectures/implications/), each rebuilt and its
axioms read before the merge (standard three only).

| Edge | Kind | PR |
| :--- | :--- | :--- |
| infinitely many squarefree `2^n − 1` ⇒ infinitely many non-Wieferich primes (Rotkiewicz), with `sq_dvd_mersenne_iff_isWieferichPrime` | theorem; both were `sorry` in formal-conjectures | #1 |
| Cramér, its strict form, Firoozbakht, or any `p^ε` gap bound ⇒ Erdős 382 (i); Firoozbakht ⇒ Cramér | premise open | #2 |
| Butson `H(4, 2m)` ⇒ Hadamard conjecture | premise open | #3 |
| four exponentials ⇒ `2^t` or `3^t` transcendental for irrational `t` | premise open | #3 |
| abc ⇒ Erdős 936 (four variants) and Erdős 977 (factorial variant) | premise open | #4 |
| quantitative density bound for `k`-term progressions ⇒ Erdős 142 (lower variant) and all-`k` Erdős 140 | premise proved in Lean by openai/math, taken here as a hypothesis | #5 |
