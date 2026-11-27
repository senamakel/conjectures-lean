# Find the Lean-open targets closest to a proof

Use this pass when you have an open OMA family or a collection of Lean goals and want to find what existing declarations could prove. Rank by the smallest remaining argument you can actually test. Keep mathematical novelty separate from tractability. A known proof that has not been formalized can supply a technique for a neighbouring open target. [Scope and prior-art requirements](../AGENTS.md#priority-results-not-yet-in-the-public-literature)

## Retrieve and shortlist

The scanner uses the live OMA catalogue for exact Lean targets and the local LemmaGraph MCP endpoint at `http://127.0.0.1:7340/mcp`. It queries 32 premises per goal to retain the recall of LemmaGraph's R@32 workflow. It separately searches for neighbouring OMA declarations and checked proofs. It runs Exa only for the top candidates, with the original source and exact statement in each query.

```sh
python3 scripts/attack_scan.py --q 'clique' --limit 12 --exa-top 3 > scan.json
python3 scripts/attack_tools.py shortlist scan.json --take 3
python3 scripts/attack_tools.py links scan.json
```

The ranking prefers an identical printed proposition, then more qualified symbols in common. This is a lightweight retrieval heuristic. Elaborated signatures can differ in binder names, universe annotations, and notation. Generic shared symbols can rank a result too high. Each entry retains the original 32-result premise ranking, nearby OMA declarations, links, and up to five proposed bridge lemmas. Use the suggested `#check` lines at the OMA pin and read the actual signatures. A neighbour in `oma/proofs` can suggest a construction even if it cannot be imported.

The JSON report includes per-target service errors. The scanner exits nonzero when a lookup failed and retains successes for inspection or retry. Use `--exa-top 0` for a retrieval-only pass. Set `--lemmagraph-url` or `--exa-url` to point at another compatible MCP endpoint. Adjust `--limit`, `--offset`, and `--workers` to bound work. Filter by `--source` or `--field` when the first page mixes unrelated topics.

## Break down an exact target

Start with the registry's checked reductions. Their open leaves provide a decomposition with an existing Lean proof that connects them to the parent.

```sh
parent=Erdos151.erdos_151
python3 scripts/attack_scan.py --parent "$parent" --exa-top 1 > leaves.json
python3 scripts/attack_tools.py packet leaves.json "$parent.R1.H1"
```

For an unreduced problem, inspect the top bridge signatures and try `apply` or `exact` in the pinned checkout. Record the actual remaining goal state after the candidate lemma. Save named propositions in a JSON object and rerun the scanner on those bridge goals. Include required hypotheses and binders so semantic search sees the right goal. The scanner retrieves candidate lemmas for each obligation, while the pinned Lean checkout determines whether they apply.

```sh
printf '%s\n' '{"small-clique":"∀ n : ℕ, n < 4 → n ≤ 3"}' > goals.json
python3 scripts/attack_scan.py --goals goals.json --exa-top 0 > goals-scan.json
```

Compare the original and residual goals. Promote a target when an exact lemma closes a checked obligation or the remaining gap has a short, concrete proof route. A lexical match alone is a lead. For a new reduction, show in Lean how its hypotheses imply the original target before treating them as a decomposition. [OMA proof and reduction verification](ATTACK.md#5-verify-and-hand-off)

## Link work and hand off

Take one GitHub snapshot per batch, then use the exact-ID helper to find changed Lean paths for the target, its ancestors, and descendants. Refresh the snapshot and check the live registry before assigning a proof.

```sh
repo=GuillaumeBAUD-coder/open-math-agents
gh pr list -R "$repo" --state open --limit 1000 --json number,title,url,files > open-prs.json
python3 scripts/attack_tools.py overlap "$parent" --prs open-prs.json
python3 scripts/attack_tools.py shortlist leaves.json --prs open-prs.json
python3 scripts/attack_tools.py packet leaves.json "$parent.R1.H1" --prs open-prs.json
```

Review any shared bridge that `links` finds across distinct targets. Confirm which declarations and pins can be shared before spending time on separate proofs. The packet carries the statement, candidate lemmas, prior-art hits, and questions about the exact gap, proof applicability, open siblings, and what would disprove the route. Check original sources and unresolved PRs before treating a suggested target as available. When the GitHub snapshot reaches its limit, follow the additional checks in the [batch runbook](OMA_AT_SCALE.md#run-a-discovery-batch).
