# Erdős 932 census through 150 million

The census found **11,197 qualifying gaps** among the 8,444,396 consecutive-prime gaps with left endpoint at most 150,000,000. It reproduced all 10,000 indices in the OEIS b-file and added 1,197 rows in [the extension table](erdos932-census-150m-extension.tsv). OEIS uses one-based prime indices and its table ends at index 6,386,830, corresponding to the prime 111,551,057. The conjecture asks whether infinitely many gaps qualify and remains open. [OEIS indices](https://oeis.org/A387864) · [OEIS left primes](https://oeis.org/A387863) · [Erdős problem](https://www.erdosproblems.com/932)

## Search and validation

The search protocol recorded on 27 November 2026 capped one thread at 120 CPU seconds. The published table's observed hit rate made a 34% extension of its prime range a reasonable place to look. An Eratosthenes sieve generates consecutive primes through 150,100,000 to include the successor of every left endpoint in range. For each gap of length (g), the program divides each interior integer by every prime strictly smaller than (g), with multiplicity. An integer qualifies precisely when its residual is 1. The program records the first two qualifying integers in each gap in the extension.

An independent trial-division validator checked both listed primes in every row, checked that no prime lies between them, and confirmed that both listed integers meet the strict factor bound. A fresh run of the exhaustive scan reproduced the table byte for byte in about six seconds. The table's SHA-256 is `c39b641a824e998b6a9fcdd84b159438a307d5837a02ce8d3b0fc12400c18fc0`.

The final qualifying gap is between 149,973,611 and 149,973,667, and the witnesses are 149,973,616 and 149,973,660. Lean proves these endpoints occur consecutively in the zero-based prime sequence and both witnesses have largest prime factor below 56. The theorem does not compute the index. The verified axiom list is `[propext, Classical.choice, Quot.sound]`. [Lean certificate](../../../../conjectures/implications/Implications/SmoothGapWitness150m.lean)

The 27 November Exa and GitHub checks found the 10,000-entry OEIS table and the merged one-hit density result, with no larger public census found. [OEIS table](https://oeis.org/A387864/b387864.txt) · [One-hit density proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1815) · [SciNet census criterion](https://api.scinet.pub/p/c9854261-4d4f-4be1-aa98-65270fe45e66)

## Reproduce

Run from the repository root.

```sh
mkdir -p .lake/erdos932-census
curl -fsSL https://oeis.org/A387864/b387864.txt -o .lake/erdos932-census/b387864.txt
printf '%s  %s\n' '01c68a6cb27e5a0f7b7d9734fbe3076945c1a512c6281c7fd32431985c3b8969' \
  .lake/erdos932-census/b387864.txt | sha256sum --check
g++ -O3 -std=c++20 scripts/erdos932_census_150m.cpp -o .lake/erdos932-census/scan
(ulimit -t 120; .lake/erdos932-census/scan .lake/erdos932-census/b387864.txt \
  .lake/erdos932-census/extension.tsv)
cmp .lake/erdos932-census/extension.tsv docs/atlas/sweeps/2026-11-27/erdos932-census-150m-extension.tsv
python3 scripts/validate_erdos932_census_150m.py .lake/erdos932-census/extension.tsv
cd conjectures/implications
lake build Implications.SmoothGapWitness150m
```
