# lemmagraph A/B experiment, round 2 (2026-11-26)

You are one arm of a paired experiment measuring whether the lemmagraph MCP speeds up Lean work on
our WIP conjectures. Another agent does the SAME task in the other arm. Round 1 was inconclusive
because the lemmagraph arm never called the tool, so arm A now has mandatory steps.

lemmagraph = an index of all Mathlib/core/Batteries declarations at exactly our pin
(Lean v4.36.0, Mathlib fc4f59e5) plus their proof-dependency graph. Names and signatures in results are exact.
It retrieves, it does not prove: check that a lemma applies.

## ARM A (lemmagraph): mandatory procedure
0. Load the tools first:
   ToolSearch "select:mcp__lemmagraph__premises,mcp__lemmagraph__search,mcp__lemmagraph__text_search,mcp__lemmagraph__get_declaration,mcp__lemmagraph__dependencies"
1. For EVERY goal you have to prove (each `sorry`, each failing `have`/tactic step whose goal you can read
   from the error or `trace_state`), BEFORE grepping or guessing names, call
   `mcp__lemmagraph__premises` with the goal as a Lean statement, e.g.
   `∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → IsCyclic (ZMod (p ^ e))ˣ`, or the pretty-printed goal
   `⊢ Continuous (Prod.map (fun x ↦ ⇑u ∘ x) id)` with its hypotheses. This is the strong tool:
   it ranks lemmas from similarity plus the proofs of similar Mathlib theorems
   (benchmark: 59% of a real proof's premises in the top 32, 82% in the top 128). Ask for a generous
   limit (32-64) if the tool takes one. Read the whole ranked list before choosing.
2. When a name is unknown or ambiguous after the Mathlib bump (unknown identifier/constant, ambiguous
   overload, signature mismatch), call `mcp__lemmagraph__get_declaration` on the name (short names work;
   it reports ambiguity) and/or `mcp__lemmagraph__text_search` with keywords, and
   `mcp__lemmagraph__dependencies` on a sibling lemma to see what Mathlib now uses in its place.
3. Use `mcp__lemmagraph__search` for idea-level questions ("cyclic group has at most n solutions of x^n = 1").
4. Only after steps 1-3, fall back to grep over Mathlib sources if needed (count those greps).
5. Keep a call ledger in `<armdir>/calls.jsonl`, one line per lemmagraph call:
   {"tool":..., "query": "<short>", "useful": true|false, "used_lemma": "<name or null>", "rank": <rank of the used lemma in the result list or null>}

## ARM B (control)
Do NOT use any mcp__lemmagraph__* tool, the `lg` CLI, or anything under ~/work/personal/lemmagraph.
Use grep/rg over Mathlib sources (~/work/personal/conjectures-lean/.lake/packages/mathlib/Mathlib),
`#check`, `exact?`, `apply?`, `rw?`, `simp?`, etc.

## Rules for both arms
- `export PATH=$HOME/.elan/bin:$PATH`. Never `lake update`, `lake exe cache get`, or `lake build`.
  Single-file elaboration only (command given in your task). `nice -n 10`.
- Edit ONLY files inside your arm directory. Don't edit repo worktrees; you only read them and run
  `lake env lean` inside them. Don't commit or push.
- Statements are fixed. Change proofs only. (Port files: if a statement truly cannot typecheck for a
  representational reason, re-spell it with the same meaning and flag STATEMENT RE-SPELLED.)
- Hard budget: 60 minutes wall time. Stop when done or out of time; a partial result is fine; report it honestly.
- At the end write `<armdir>/log.json`:
  {"task":..., "arm":"A"|"B", "start_utc":..., "end_utc":..., "status":"done"|"partial"|"failed",
   "compiles":true|false, "sorries_left":N, "errors_left":N, "lean_runs":N,
   "unknown_identifier_errors":N, "lemmagraph_calls":N, "lemmagraph_useful_hits":N,
   "grep_searches":N, "notes":"3-6 sentences: what was hard; for arm A, concrete cases where lemmagraph found
   something you would not have recalled, and where it failed"}
  Take `date -u +%FT%TZ` as your first action and again at the end.
- Final reply: log.json contents, the calls.jsonl line count (arm A), and the final file path.
