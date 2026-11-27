# Local Search and Verification Solvers

## Cubic Acute Sets (`OEIS A089676`)

Use the local C++ solver and Python verification helper in `solver/` to search for candidate acute subsets in `{0, 1}^n` for `n >= 11` and print formatted Lean 4 record definitions for insertion into `lean/cubic-acute-sets/CubicAcuteSets/Records.lean` or `RecordsII.lean`.

### Files

- `search.cpp` runs a multi-phase, multi-threaded heuristic search seeded by default from `Witnesses.lean`, `Records.lean`, and `RecordsII.lean` (`--witnesses` overrides the list and `--seed-file` appends to it). For dimensions `11` through `15`, Phase 1 runs randomized destroy-and-extend large neighborhood search (`lns_extend`). For dimensions `16` through `--max-n`, Phase 2 maintains an 8-entry candidate pool per dimension (`SharedState`), seeds from Bevan's `+2` construction (`n - 2 -> n`), runs up to 6 passes alternating bipartite 2-coloring lifts (`BipartiteState` with parity union-find `try_add`, parallelogram XOR recombinations, and `conflict_guided_repair` using `accumulate_odd_cycle_hits` and `peel_odd_cycles`) with coordinate projection (`drop_coord` and `insert_coord`) and refill, and finishes with `lns_extend` when time remains.
- `export_lean.py` checks vertex uniqueness, `0 <= x < 2^n` range bounds, and triple-wise acuteness by rejecting any triple where `((x ^ y) & (z ^ y)) == 0`, compares sizes against `BASELINE_KAMENETSKY_2026` (`0 <= n <= 26`), and prints Lean 4 record definitions using `--prefix` (default `record`, or `recordII` for `RecordsII.lean`) to stdout or `--out` for kernel verification via `checkAcuteMatrix_sound`.

### Usage

Compile and run the binary in `/tmp` so build outputs remain outside the git working tree:

```bash
g++ -O3 -std=c++17 -pthread solver/search.cpp -o /tmp/solver_search
/tmp/solver_search --seconds 60 --max-n 26 --threads 4 --out /tmp/solver_records.json
python3 solver/export_lean.py --prefix recordII /tmp/solver_records.json
```

Remove temporary files from `/tmp` once exported definitions have been added to Lean.

## Proper-Divisor $\tau$-Moments (`OEIS A245211`)

Use `solver/a245211_search.py` to compute the proper-divisor moment `a(n) = sum_{d|n, d<n} d * tau(d)` by divisor-multiple sieve tables, verify the 66 OEIS header terms (`A245211(1..66)`) and optional `b245211.txt` data (`1..10000`), check the uniqueness of the fixed point `n = 21` and the milestones `min(A245213) = 72` and `min(A245214) = 144` up to `--limit`, audit the Diophantine fixed-point equation across `Omega(n) <= 4`, verify the prime-power parity congruence and non-squarefree `Omega(n) = 5` exclusions, run the exhaustive branch-and-bound hyperbolic search for squarefree `Omega(n) = 5` (`43,849` triples, `0` solutions), and execute the Cunningham prime-factor forced-closure accelerator for `Omega(n) = k` (`k in 3..10`, reducing `Omega(n) = 5` to `14` primes and `Omega(n) = 6` to `30` primes with `0` surviving roots) together with the non-squarefree `Omega(n) = 6` exclusions (`(6)`, `(5,1)`, `(4,2)`, `(2,2,2)`, `(4,1,1)`, and parity-obstructed shapes).

```bash
python3 solver/a245211_search.py --limit 200000
```

