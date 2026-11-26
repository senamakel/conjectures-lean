# lemmagraph A/B experiment (2026-11-26)

You are one arm of a paired experiment measuring whether the lemmagraph MCP
(Mathlib lemma search by similarity/ideas, indexed at exactly our pin Lean v4.36.0 / Mathlib fc4f59e5)
speeds up Lean proving and discovery. Another agent does the SAME task in the other arm. Do the task
as well and as fast as you normally would.

Arms:
- ARM A (lemmagraph): use the lemmagraph MCP tools (mcp__lemmagraph__search, premises, text_search,
  get_declaration, dependencies; load them with ToolSearch "select:mcp__lemmagraph__search,mcp__lemmagraph__premises,mcp__lemmagraph__text_search,mcp__lemmagraph__get_declaration,mcp__lemmagraph__dependencies")
  as your FIRST resort whenever you need a lemma name, a signature, or how Mathlib proves something.
  You may also grep Mathlib sources.
- ARM B (control): do NOT use any mcp__lemmagraph__* tool, the `lg` CLI, or anything under
  ~/work/personal/lemmagraph. Use grep/rg over Mathlib sources
  (~/work/personal/conjectures-lean/.lake/packages/mathlib), `#check`, `exact?`, `apply?`, etc.

Rules for both arms:
- Lean: `export PATH=$HOME/.elan/bin:$PATH`. Never `lake update`, never `lake exe cache get`,
  never `lake build` of whole packages unless your task says so. Prefer single-file elaboration.
  Use `nice -n 10` and `LEAN_NUM_THREADS=8`. The box is shared.
- Work ONLY on files inside your arm directory (given in your task). Do not edit the repo worktrees;
  you only read from them and run `lake env lean` inside them. Do not commit or push anything.
- Hard budget: stop after 75 minutes wall time or when done, whichever first.
- Keep an honest log. When you finish, write `<armdir>/log.json`:
  {"task":..., "arm":"A"|"B", "start_utc":..., "end_utc":..., "status":"done"|"partial"|"failed",
   "compiles":true|false, "sorries_left":N, "lean_runs":N (number of lean elaborations you ran),
   "unknown_identifier_errors":N (errors from wrong/nonexistent lemma names, total across runs),
   "lemmagraph_calls":N (0 for arm B), "lemmagraph_useful_hits":N (lemmas found via lemmagraph that ended up in the proof),
   "grep_searches":N, "notes":"2-5 sentences: what was hard, where search helped or failed"}
  Record `date -u +%FT%TZ` at start (first action) and at the end.
- Final reply: the log.json contents plus the path of your final file(s). No other summary needed.
