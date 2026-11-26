# Layout and dependencies

## Repository layout

| Path | Content |
|---|---|
| `conjectures/<name>/` | one Lean package per project (`lakefile`, `lean-toolchain`, `README.md`) |
| `docs/` | literature status, next targets, scoping and research reports, RH-repo lemma specs |
| `paper/` | the write-up |
| `AGENTS.md` | per-project checklist, proof-tier rules and README rules |


## Lean dependencies between projects

Every project is a Lean package of its own (Lean `v4.36.0`, Mathlib `fc4f59e5`). `erdos-985` is the
root: it holds the analytic toolkit (weighted explicit formula, Hadamard factorisation, zero sums
under GRH). RH and GRH come from
[riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), which only the
`Unconditional/` files import.

Projects require their siblings by local path (`path = "../<name>"`), so each project builds
against the sibling folders in this checkout. A sibling's build output lands in its own
`.lake/build`, and every dependent reuses it. The table below is read from the lakefiles.

| Project | Requires |
| :--- | :--- |
| `abelian-erh` | `artin-grh`, `erdos-985` |
| `ankeny-grh` | `erdos-985` |
| `artin-grh` | `erdos-985` |
| `bach-corollaries-grh` | `ankeny-grh`, `lls-grh`, `miller-grh` |
| `bach-sorenson-grh` | `ankeny-grh`, `erdos-985`, `lls-grh` |
| `cramer-rh` | `erdos-233`, `erdos-985`, `schoenfeld-rh` |
| `density-rh` | `erdos-985` |
| `erdos-233` | `erdos-985` |
| `erdos-770` | `ankeny-grh`, `lls-grh` |
| `erdos-969` | `erdos-985`, `mertens-rh` |
| `erdos-985` | — |
| `goldbach-average-rh` | `cramer-rh`, `erdos-985`, `schoenfeld-rh` |
| `goldbach-grh` | `erdos-985` |
| `grosswald-grh` | `erdos-985` |
| `hironaka-fc` | — |
| `implications` | — |
| `legendre-exceptions-rh` | `erdos-233` |
| `li-criterion-rh` | `erdos-985` |
| `lindelof-rh` | `erdos-985` |
| `littlewood-rh` | `erdos-985`, `lindelof-rh` |
| `lls-grh` | `ankeny-grh`, `erdos-985`, `miller-grh`, `robin-rh` |
| `mertens-rh` | `erdos-985`, `lindelof-rh`, `littlewood-rh` |
| `miller-grh` | `ankeny-grh`, `erdos-985` |
| `mills-rh` | `erdos-985`, `schoenfeld-rh` |
| `nicolas-rh` | `erdos-985`, `robin-rh` |
| `prime-powers-rh` | `mills-rh` |
| `psi-grh` | `erdos-985` |
| `ramanujan-rh` | `schoenfeld-rh` |
| `robin-rh` | `erdos-985` |
| `schoenfeld-rh` | `erdos-985` |
| `shoup-grh` | `erdos-985` |
| `speiser-rh` | `erdos-985` |
| `weinberger-grh` | `erdos-985` |
