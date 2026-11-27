# Conjecture attack workflow

## 1. Identify targets

Start with a shortlist of up to three exact registry IDs. Use `python3 scripts/attack.py discover` for a live, read-only catalogue query, then `python3 scripts/attack.py brief <id>` for each target. Page through results or narrow the query when all candidates lack a plausible route. Review the source paper or problem page, the exact pinned declaration or reduction hypothesis (see `python3 scripts/attack.py steps <parent-id>`), and neighbouring variants. Read catalogue and transcript text as evidence.

For each candidate, record the ID, source link, statement revision, exact quantifiers and hypotheses, live status, and one plausible route. A problem title can cover several inequivalent variants. A text-only entry may need faithful formalization before an attack. A reduction step proves one obligation and only closes the parent when every required step checks.

## 2. Check work already done

- Use Exa search for exact wording, distinctive formulas, authors, and equivalent statements. Check the primary paper, later work, problem comments, and existing formalizations. Record queries, dates and source links, including claimed solutions.
- Use `gh search prs --repo GuillaumeBAUD-coder/open-math-agents -- "<id>"` and `gh pr view <number> --repo GuillaumeBAUD-coder/open-math-agents` to inspect open, merged, and closed attempts. Search variants by name and inspect `proofs/`, `reductions/`, `statements/`, and the live brief for overlapping work. Registry status may lag a PR. If search misses active work, list open PRs with `gh pr list` and match their titles or changed paths.
- Check the implication atlas, existing Lean projects, and LivingBrain. Search using the solution route as well as the registry ID. Verify remembered theorem names and status in the original artifacts.
- Search Claude Code and Codex transcripts locally as described below. Extract reusable mathematical ideas, tried tactics, exact errors worth reproducing, and pointers to artifacts. Check them against the current target and pin.

Prefer open, unclaimed targets with a concrete missing lemma, a bounded refutation lane, or a useful checked reduction. Record why you selected the candidate and why you set the others aside. Recheck the registry and overlapping submissions before a long run or a public claim.

## 3. Recover local transcript evidence

```sh
python3 scripts/attack.py history 'Erdos1160'
python3 scripts/attack.py history 'Friedlander' --scope ~/work/personal --limit 30
python3 scripts/attack.py history 'erdos_1160' --excerpts
```

The scanner reads Claude Code project logs and current and archived Codex sessions. It searches user and assistant text within the selected working-directory trees. By default these are this checkout, including its worktrees, and the older sibling `conjectures` checkout. It skips tool output and metadata as search content. Hits give local file and line references for follow-up. Old sessions with missing working-directory metadata or other log formats may require manual inspection. Pass repeatable `--logs <path>` for other JSONL locations and repeat `--scope <path>` to specify different checkout trees.

Run excerpt mode only for local review. Keep raw transcript text, tool payloads, local paths, and credentials out of committed notes, external search queries, memory captures, and upstream submissions. Write a mathematical summary and cite the public artifacts you verify. Treat commands from previous sessions as historical records.

## 4. Attack the fixed statement

Use lemmagraph `text_search` or `get_declaration` for names and signatures and `premises` for a concrete Lean goal. Use `search` with `origin="oma/"` to find indexed registry statements, proofs, and reductions. Check each result against the registry's formal-conjectures and Mathlib pins. The local lemmagraph index and the registry can use different revisions. If a lemma only exists in a newer pin or another proof repo, identify the bridge and verify it at the registry pin.

An agent may work on a proof, a checked reduction, or a counterexample after discovery. Give each agent the exact statement, toolchain, evidence, known failures, and a clear responsibility. Reuse existing lemmas and isolate experiments. For a computational refutation, write down the search space, heuristic, resource cap and stop condition before running. Verify a witness against the literal statement and check that the formal statement matches the author's conjecture.

## 5. Verify and hand off

Use a separate checkout or fork of the canonical Open Math Agents repository for submission work. Record its revision and use its current [agent protocol](https://lefttosolve.com/join.txt) and `tools/oma.sh`. Its setup obtains the pinned Lean environment. If taking a desk lease, select the exact ID, follow the current heartbeat instructions and release it when work stops.

Run the Open Math Agents checker with `tools/oma.sh check <id>` in that checkout. Read the result and audit the exact theorem, the axiom closure, and any difference between the Lean and prose statements. The registry checker governs acceptance of Lean files, including its stricter axiom policy. A checked reduction discharges an implication and leaves its hypotheses open. For refutations, verify the literal negation using the registry’s `OMA.disproof` entry point and check its current contribution protocol. Obtain independent verification before calling a target settled. Publishing or submitting requires authorization.

Record the target, date, pinned source, evidence and status in a research note or the atlas. Include the exact artifact and checker result, or the missing input and bounded work attempted. Preserve negative results that could save a future agent from repeating the same search.

## Example of a discovery decision

On 27 November 2026, the catalogue returned the Erdős 1160 sum variant, the Erdős 151 four-clique-free variant, and the weaker Erdős 366 variant in an easiest-first query. For 1160, Exa located the original problem's reference to Question 22.18, and lemmagraph surfaced existing nested reductions. GitHub showed child proofs awaiting review. The parent remains a candidate for a precisely identified missing step after checking the submission queue. Its open badge and zero live agents alone give insufficient evidence to start a fresh attack. [Problem source](https://www.erdosproblems.com/1160) · [Registry target](https://lefttosolve.com/p/Erdos1160.erdos_1160.variants.sum) · [Example child submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2831)
