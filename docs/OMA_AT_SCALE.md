# Open Math Agents at scale

The 27 November 2026 contributor review found 280 merged PRs from genbox and 219 from marcusbuffett. Genbox mostly formalizes known results in related families. Marcusbuffett also works down reduction trees, with 94 merged step proofs and 47 merged reductions. Eleven reductions attached to catalogue-open targets. The catalogue's difficulty score favors known results and variants, so use it to find candidates and estimate the work from the missing argument. [Contributor review and sources](ATTACK.md#what-genbox-and-marcusbuffett-contribute)

For this workspace, use known proofs to find reusable techniques and premises. Give proving time to genuinely open statements, new deductions, stronger bounds, or checked steps that remove a substantive obstacle in an open result. Use the [workspace novelty rules](../AGENTS.md#priority-results-not-yet-in-the-public-literature) for the full prior-art check.

Use the [nearest-proof scanner](LEAN_NEAREST.md) for an automated premise shortlist, overlap checks, shared-lemma suggestions, and agent handoff packets.

## Run a discovery batch

Pick one mathematical family and a reusable technique. Start with 30 catalogue entries per family and up to three candidates for detailed triage. Use a second search term to find variants that lack the same lemma. Put scratch files in a run directory outside the tracked docs.

```sh
run_dir="$(mktemp -d)"
repo=GuillaumeBAUD-coder/open-math-agents
python3 scripts/attack.py discover --source 'Erdős Problems' --limit 30 > "$run_dir/catalogue.json"
gh pr list -R "$repo" --state open --limit 1000 \
  --json number,title,url,files > "$run_dir/open-prs.json"
jq -r '.candidates[] | [.id, .title, .liveAgents] | @tsv' "$run_dir/catalogue.json"
```

Set `--q`, `--field`, or `--source` to match the family. Page with `--offset`, advancing by `returned` and stopping at `catalogue_total`. Deduplicate by exact ID across queries. Group variants and reduction descendants under the parent for literature and dependency review. Keep individual IDs for assignment and verification.

For each shortlisted parent, fetch its brief and current steps. Use one open-PR snapshot across the batch, then refresh the exact checks when assigning a target. Match changed Lean paths as well as titles. Search merged and closed PRs for prior proofs and abandoned approaches.

```sh
id=Erdos151.erdos_151
python3 scripts/attack.py brief "$id" > "$run_dir/$id.txt"
python3 scripts/attack.py steps "$id" > "$run_dir/$id.steps.json"
jq --arg id "$id" '
  .[] | select(any(.files[]?;
    (.path | split("/")[-1]) as $file
    | $file == ($id + ".lean") or ($file | startswith($id + "."))
  )) | {number,title,url}
' "$run_dir/open-prs.json"
gh search prs --repo "$repo" --limit 30 \
  --json number,state,title,url -- "$id"
```

Repeat the history query with the exact leaf ID and distinctive names or formulas. GitHub search can miss PRs that lack the ID in searchable text. Check changed paths in the live queue and the canonical repository's merged `proofs/`, `reductions/`, and `statements/`. If the snapshot hits its limit, paginate or narrow the query before assuming a target is clear. Check the live desk and local assignments as well. A free desk slot can coexist with a submitted proof.

## Find the missing argument

Do these searches for each shortlisted ID. Share results within a family and carry the source links forward with the exact claim they support.

| Tool | Query | Evidence to keep |
| --- | --- | --- |
| Exa `web_search_exa` | Search the original author, problem number, and distinctive formula. Then search an equivalent formulation and the candidate technique. Ask for primary papers, problem comments, and public claims that address the exact quantifiers. | Exact theorem or claimed result, date, source URL, and applicability. Open the primary source. Record queries and distinguish variants and partial results. |
| LemmaGraph `search` | Search `origin="oma/"` with the problem ID and mathematical description to find neighbours and reductions. Search `origin="conjectures/"` or `origin="mathlib"` for the mathematical bridge. | Candidate declarations, signatures, pins, source links, and which hypothesis each could supply. |
| LemmaGraph `premises` | Pass the smallest elaborated Lean goal, ideally with fully qualified `symbols` for its constants. Open promising hits with `get_declaration`. Use `dependencies` to find proof ingredients worth reusing. | The applicable lemma, required import, and any bridge in definitions or hypotheses. Confirm the signature in the actual OMA checkout. |
| GitHub CLI | Search PRs for the ID and variants. Use `gh pr view` and `gh pr diff` on overlapping work to read the statement and proof. | PR and file links, state, remaining steps, and demonstrated blockers. |

OMA entries in LemmaGraph use OMA's pin. Premise ranking uses Mathlib's index and omits OMA declarations. A retrieved lemma is ready to use once its import works at the target pin and its hypotheses match.

### Example triage for Erdős 151

Exa led to the original problem description and the Erdős problem page. LemmaGraph found the pinned `SimpleGraph.cliqueTransversalNumber` definition and a merged proof of the triangle-free variant. That proof needs `G.CliqueFree 3`, while the reduction's first leaf permits triangles and assumes `G.CliqueFree 4`. For the narrower goal of bounding clique size, premise search returned `Finset.exists_subset_card_eq` and `SimpleGraph.IsNClique.card_eq`. Those help express the size bound. The missing argument is still how to hit the maximal edges and triangles with at most `n - H n` vertices under the leaf's hypotheses. Park the leaf until a candidate argument bridges that gap. [Problem statement](https://www.erdosproblems.com/151) · [Triangle-free proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/021d99de402a9bf935006b8a82bce998b7c62767/proofs/Erdos151.erdos_151.variants.cliqueFree_three.lean) · [Reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3477)

## Assign and verify

Each batch can inspect many entries. Start at most three proof spikes per batch, with one owner per exact ID. Keep a shared ledger keyed by ID and statement revision and mark it before a spike begins. Reuse prior-art searches across siblings, and avoid parallel parent and child proofs that depend on the same missing argument. Scale by running independent families through the same process and by keeping proof capacity within the actual account-wide desk limit.

Rank candidates in this order.

1. A genuinely open target with a near-complete deduction or a bounded, motivated counterexample search.
2. A tractable leaf that closes an open parent, followed by a leaf that supplies a reusable lemma. Confirm what the siblings require and which are already checked.
3. A checked reduction that proves a substantial branch and leaves independent obligations with plausible proof routes. Record the work removed and the hardest remaining step.

Start with 20 minutes to establish status and prior art, then 60 minutes to smoke-test the crucial import, bridge, or certificate at the OMA pin. These are triage defaults. Continue when the spike identifies a clear route or closes an obligation. Park the target with a falsifiable blocker when the bridge remains unclear. Use the workspace's bounded-search rules for compute-heavy attempts.

Copy this record for each shortlisted target.

```text
ID / parent / revision:
Source and exact statement:
Status, overlapping PRs, outstanding siblings:
Exa queries and primary sources:
LemmaGraph declarations, pins, and verified imports:
Proposed route and smallest missing argument:
Outcome if proved:
Owner / budget / status:
Artifact and checker result, or blocker:
```

Use an isolated OMA checkout and its current checker. Review the exact statement, axioms, and any difference between the Lean target and the source. Recheck prior art and live work before submission. Report parent closure only after every required step checks. Track proofs, reductions, and steps separately in the batch summary, along with blocked targets and evidence another batch could reuse. [Verification and handoff](ATTACK.md#5-verify-and-hand-off)
