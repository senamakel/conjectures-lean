# Erdős 932: bounded census to 150 million

## Pre-registered search

Date: 2026-11-27. The target is Erdős Problem 932: for infinitely many indices (r), the open gap ((p_r,p_{r+1})) contains at least two integers whose largest prime factor is strictly less than the gap length (g=p_{r+1}-p_r).

OEIS A387864's b-file contains 10,000 indices and ends at (r=6{,}386{,}830). A387863 gives the corresponding prime endpoint (p_r=111{,}551{,}057). The proposed extension checks every prime left endpoint (p_rle150{,}000{,}000), approximately 34.5% farther in (p). The local density over the known range is about (10{,}000/6{,}386{,}830); this gives a weak reason to expect some additional hits, while Erdős's density-zero result warns that the hit rate can decline. The purpose is the finite-census advance listed by the SciNet problem entry, not an infinitude inference.

The search is deterministic and exhaustive over that range. A byte sieve generates primes through (150{,}100{,}000), which supplies the next prime for every left endpoint at most (150{,}000{,}000). For each gap (g), each interior (m) is tested by exact trial division by every prime (ell<g). It qualifies iff the residual is 1, exactly the condition that its largest prime factor is strictly less than (g). The script first checks all 10,000 OEIS indices in order and the corresponding endpoint prime.

Stop condition: finish the complete range or stop at 120 CPU seconds. The program is single-threaded and receives an OS CPU-time limit. The expected work is one sieve to (150.1) million and one exact test for every integer lying strictly inside a scanned prime gap. The earlier scouting pass completed in 97.829 CPU seconds but did not save the full extension table; this rerun was authorized to capture that table.

## Sources checked before the run

- [OEIS A387863](https://oeis.org/A387863) and its b-file: prime endpoints of gaps with at least two qualifying integers.
- [OEIS A387864](https://oeis.org/A387864) and its b-file: gap indices. Its comment attributes the 1976 infinitude conjecture and still says it is open; its linked Chai Wah Wu table is for (n=1,ldots,10000).
- [Erdős Problems #932](https://www.erdosproblems.com/932) and its discussion page: still listed open; the thread says finite computation cannot resolve the infinitude question.
- [SciNet #932](https://api.scinet.pub/p/c9854261-4d4f-4be1-aa98-65270fe45e66), posted 2026-07-21: identifies extending the A387864 census as an accepted finite advance; it reports zero logged investigations.

No larger public census endpoint was found in those records. Exa and GitHub searches for A387863, A387864, Erdős 932, and the endpoint are recorded in the handoff.

## Result

Pending the registered run and independent validation.
