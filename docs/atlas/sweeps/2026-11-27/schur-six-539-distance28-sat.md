# Fixed-support Schur (S(6)\ge539) SAT screen

**Protocol recorded:** 27 November 2026, before SAT generation. **Status:**
fixed support and resource caps below; SAT result to be appended after the run.

## Prior art

The October 2026 paper of Chen, Zhu and Long gives 131 inequivalent
538-modulus sum-free partitions of `[1,537]`
([arXiv:2610.31362](https://arxiv.org/abs/2610.31362)); it says those examples
are a retained search sample, not an exhaustive classification. Adam McKenna's
November 4 preprint gives an explicit partition of `[1,538]`, directly checked
and formalized in Lean 4 ([Zenodo DOI 10.5281/zenodo.23937655](https://doi.org/10.5281/zenodo.23937655),
[certificate repository](https://github.com/mysticflounder/schur-538)).

The November follow-up search in
[`jeffchen006/Schur-Number-6/evolve538/README.md`](https://github.com/jeffchen006/Schur-Number-6/tree/main/evolve538)
reports no 539 coloring after 47 generations of blank-start evolved programs,
fixed-prefix growth experiments and partial residue-class searches. It reports
1,021 evolved 538 words (995 up to color renaming), but no SAT test of the
specific distance-28 support frozen below. A separate October preprint lists a
search in progress for six-colorings at lengths 537–620, without a 539 result
or this fixed-support test
([HAL-05836388](https://hal.science/hal-05836388)). Exact Exa searches on
27 November surfaced no public `S(6) ≥ 539` certificate or distance-28 SAT
result. The formal-conjectures bridge remains `Erdos483.HasTriple` at pin
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`; OMA's live search for “Schur”
returned no exact catalogue candidate.

## Fixed input and support

The word is McKenna's published `schur6-538.word`, not either an evolved word
or his alternate `schur6-538-b.word`. The pinned source is
[`mysticflounder/schur-538`](https://github.com/mysticflounder/schur-538) at
commit `47c01b341b74ef5620c5e3f858c527cd266e212b`; the source word's SHA-256 is
`9e149c007b778655afd199685ebcc76260604a44f4c322d8aa9a1d96afb71d20`. The
normalized 538-symbol word has SHA-256
`9be24a8e408a0d531aaa77596c7123c44a68d2c6725627f284dd2bc96df12c41`.

An input inventory canonicalized the 1,021 evolved records to 995 words up to
color renaming, then added both distinct McKenna words (neither occurs in that
corpus). Across these 997 normalized words and all six possible appended
colors, there is a unique minimum: 28 old complementary pairs already have the
append color at both endpoints. In the first-occurrence canonical coloring,
the append color is 4; it is color `3` in McKenna's published word. Pair
positions below are 1-indexed and each pair sums to 539:

```text
(6,533)   (24,515)  (28,511)  (37,502)  (39,500)  (42,497)  (55,484)
(57,482)  (59,480)  (68,471)  (72,467)  (73,466)  (77,462)  (86,453)
(88,451)  (91,448)  (103,436) (106,433) (108,431) (117,422) (121,418)
(126,413) (137,402) (138,401) (151,388) (170,369) (200,339) (249,290)
```

The SAT search has exactly this fixed support. For each of the 28 disjoint
pairs, exactly one endpoint changes to one of the five colors other than the
append color. Every position outside those 28 changed endpoints stays as in the
published word; the appended position 539 has the fixed append color. There
are 10 choices per pair, (10^{28}) raw assignments. Changing one endpoint in
each pair removes all 28 immediate `x + y = 539` conflicts; other complementary
pairs were checked not to conflict in the append color.

## SAT encoding and limits (set before the run)

The script
[`schur-six-539-distance28-sat.py`](schur-six-539-distance28-sat.py) uses 280
one-hot variables (10 alternatives for each of 28 pairs). Exactly-one clauses
contribute 1,288 clauses. It then checks every old Schur triple
`1 ≤ x ≤ y`, `x + y ≤ 538`. For a triple touching (k) support pairs, it
enumerates the (10^k) choices for those groups and adds a clause forbidding
each assignment that makes the triple monochromatic. The append position is
handled by the fixed-support condition above. Any SAT model is reconstructed
and checked directly against all Schur triples on `[1,539]`.

The hard limits are:

* preflight at most 20,000,000 local choice-tuples across all old triples;
* at most 10,000,000 generated conflict clauses and at most 1 GiB for DIMACS;
* CaDiCaL time limit 300 seconds, 8 GiB address-space cap and 2 GiB proof-file
  cap; DRAT-trim verification has its own 300-second and 8 GiB caps.

The caps bound support-induced formula growth, solver memory/time and proof
storage. If preflight exceeds its tuple cap, formula generation does not start.
If any cap is reached, the outcome is recorded as incomplete; no cap is raised
automatically. A SAT result is accepted only after the direct finite checker.
An UNSAT result is accepted only if the generated DRAT proof passes DRAT-trim.
Otherwise the run is inconclusive. The solver and checker are pinned to
CaDiCaL commit `e4d9bd93af444c6575a908a24da2c4130cb2a1c7` and DRAT-trim commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, respectively; their source/build
outputs stay under the worktree's ignored `target/solvers/` directory.

## Result

Pending the bounded SAT run and independent witness/proof check.
