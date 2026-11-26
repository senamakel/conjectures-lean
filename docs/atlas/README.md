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
| 2026-11-26 | [formal-conjectures conditional scan](sweeps/2026-11-26/fc-scan.md); [solved-conjectures newsfeed](sweeps/2026-11-26/newsfeed.md) (with an [inventory of 1337isnot1337/solved-conjectures](sweeps/2026-11-26/newsfeed-1337-inventory.md)); [Conjecture Atlas](sweeps/2026-11-26/atlas.md); [reuse of our theorems](sweeps/2026-11-26/toolkit-reuse.md); [implications between open conjectures](sweeps/2026-11-26/implications.md); [Erdős status feed](sweeps/2026-11-26/erdos-feed.md) | 246 edges; the lemma-mining lane is still running |

The sweep reports are research notes: nothing in them was built, and claims marked
*(unverified)* were not checked against a primary source. An edge is confirmed only when its
Lean proof is merged.
