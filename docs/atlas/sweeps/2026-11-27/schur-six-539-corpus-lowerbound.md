# Witness-packing lower bound for pinned Schur 538 words

**Protocol recorded:** 27 November 2026, before the witness-packing run.

## Question and prior evidence

Can a stored six-color Schur word on `[1,538]` be extended to `[1,539]` using
at most 29 recolorings of old positions? Adam McKenna's explicit 538 coloring
and the 1,021 records in the pinned `evolve538` corpus are the finite input
families. The existing screen canonicalizes those records to 995 words up to
color renaming and adds McKenna's two distinct published words, for 997
normalized words total. A prior exact minimum-support search found the unique
minimum of 28 append-color complementary pairs on McKenna's main word. The
fixed 28-pair family is already excluded by a verified DRAT proof; an
independent direct witness check excludes every 28-change extension across
these 997 words. This run asks for a broader elementary lower bound across all
low-conflict word/color pairs, including distance 29.

Sources and pins are recorded in
[`schur-six-539-distance28-sat.md`](schur-six-539-distance28-sat.md):
`jeffchen006/Schur-Number-6` commit
`5148494527df1e61e199bad21018e9a0bebbf0e0` and
`mysticflounder/schur-538` commit
`47c01b341b74ef5620c5e3f858c527cd266e212b`. The published evolve538 report
describes evolutionary, fixed-prefix and partial residue searches, but does
not claim this witness-packing bound. The direct distance-28 SAT screen only
covers one exact support; the present run is a different combinatorial lower
bound. No public 539 coloring surfaced in the prior-art screen documented in
the linked note.

## Bound

Fix a stored word `w` and append color `c` at 539. Let `m` count old pairs
`(a,539-a)` whose two entries both have color `c`. Any valid extension must
change at least one old endpoint in each of these disjoint pairs, so it needs
at least `m` recolorings. Let `P` be the set of all endpoints of these `m`
pairs.

For a pair `i`, consider its ten possible single-endpoint repairs: choose one
of its two endpoints and recolor it to one of the five colors other than `c`.
A repair option is *witnessed* if some old Schur triple made monochromatic by
that recoloring has all its other positions outside `P`. Such other positions
are fixed by the mandatory endpoint repairs unless an additional recoloring
changes one of them. For each pair for which all ten options have a witness,
form the union `U_i` of the other positions in the ten selected witness
triples. If `q` such unions are pairwise disjoint, each corresponding pair
requires at least one extra recoloring beyond the mandatory one: either its
second endpoint changes, or a position in `U_i` changes to break the witness.
Disjointness of the `U_i`, and their being outside `P`, makes these `q` extra
recolorings distinct. Thus every extension has distance at least `m+q`.

The script selects the lexicographically first witness triple per option,
then greedily packs eligible pair-unions in increasing `(union size, pair
index)` order. This produces a certified lower bound; it is not claimed to be
an optimal packing. If `m >= 30`, the elementary complementary-pair bound
already excludes distance at most 29.

## Bounded protocol

The script checks all `997 * 6 = 5,982` normalized word/append-color pairs.
It computes witness data only for cases with `m <= 29`. Before building
witness lists it counts the exact number of triple-incidence visits implied by
their support endpoints and aborts if this exceeds 50,000,000. The pinned
corpus must still contain exactly 1,021 raw evolved words, 995 canonical
evolved words, and the two distinct McKenna words. Every input is checked for
sum-freeness, and all old triples have `1 <= x <= y`, `x+y <= 538`.

The run stops after this complete finite inventory, or before witness
enumeration if the incidence cap is exceeded. It does not expand the corpus,
search other 538 words, or increase a cap automatically. A reported `m+q`
bound applies only to the pinned stored families and does not rule out an
extension from a word outside them.

## Result

The complete inventory found 5,982 word/append-color cases, of which 36 have
`m <= 29`. Their exact witness-incidence count was 4,203,290, below the
predeclared 50,000,000 cap. Greedy packing found `q=2` in all 36 cases: the
unique `m=28` case (McKenna main, canonical append color 4) has lower bound
`m+q=30`; each of the other 35 cases has `m=29`, hence bound 31. The other
5,946 cases have `m >= 30` and already meet the target lower bound. The script
reports all 36 word IDs and colors; no low-`m` case has bound below 30.

For the minimum case, the packed conflict pairs are `(28,511)` and `(37,502)`;
their selected witness-position unions have sizes 14 and 15 and are disjoint
(the script checks disjointness directly). Thus every one of the 997 pinned
words, for every appended color, requires at least 30 old-position changes to
extend to 539. This is a corpus-bounded result, not a proof that no other
538-word has a 539 extension. It is stronger for the pinned corpus than the
prior distance-28-only exclusion and uses no SAT solver.

Reproduction command: `python3 docs/atlas/sweeps/2026-11-27/schur-six-539-corpus-lowerbound.py`.
The script checks input hashes, corpus cardinalities, every input's sum-freeness,
the triple count, the incidence cap, and the stated packing rule. Python
`py_compile` and a second complete run passed.
