# Conjecture attacker

Find open conjectures in Open Math Agents, recover earlier attempts from Claude Code and Codex, and pursue the best route to a Lean-checked proof, reduction, or counterexample. The Lean projects and implication atlas supply reusable mathematics. [Open Math Agents registry](https://github.com/GuillaumeBAUD-coder/open-math-agents) · [Live catalogue](https://lefttosolve.com)

## Start with discovery

```sh
git submodule update --init --recursive
python3 scripts/attack.py discover --limit 10
python3 scripts/attack.py brief Erdos1160.erdos_1160.variants.sum
python3 scripts/attack.py history 'erdos_1160'
```

Use `--q`, `--field`, `--source`, and `--offset` to change the shortlist. Use `steps <id>` for open obligations from existing reductions and `discover --kind formalize` for targets awaiting a Lean statement. Discovery and briefs require `curl`. The example ID demonstrates the interface. Recheck its status before starting work.

Give Claude Code or Codex this prompt from the repo root.

> Follow the conjecture attacker workflow in AGENTS.md. First identify three exact open targets from Open Math Agents. Check their source statements, live status, GitHub submissions and local prior attempts. Use Exa for prior art and lemmagraph for reusable Lean premises. Pick the best-supported route and pursue it through local verification. Record the outcome and the remaining gap.

See the [research workflow](docs/ATTACK.md) for candidate selection, transcript search, and verification. The companion [Codex skill](.agents/skills/conjecture-attacker/SKILL.md) points to the same workflow. Claude Code loads it through `CLAUDE.md`.

## Repository map

| Path | Purpose |
| --- | --- |
| [Research workflow](docs/ATTACK.md) | Discovery, prior art, proof, refutation, and handoff |
| [Agent instructions and status tracker](AGENTS.md) | Entry point and rules for the existing Lean projects |
| [Open Math Agents submodule](open-math-agents/) | Pinned registry tooling and checker |
| [Lean results](RESULTS.md) | Results and historical project inventory |
| [Conjectures](conjectures/) | Independent Lean packages |
| [Implication atlas](docs/atlas/) | Existing implications, searches, and refutation attempts |
