# Q7 layer census feasibility protocol for the open Q8 snakepit bound

Date: 2026-11-27

## Question and rationale

The target is the open upper bound `Λ(8) ≤ 104`. The published paper proves
`Λ(7)=52` by splitting a hypothetical 53-edge Q7 snakepit along a coordinate,
enumerating eligible Q6 heavy layers, then testing each layer's possible
completion with CP-SAT. It reports 4,576,964 labeled heavy-layer sets and 5,041
representatives under Q6 automorphisms. The official data repository at
`Math-AI-Caltech/Snake-in-the-Box` commit
`46c765399353a588ea50444a5d6610f53102b1c2` contains witnesses and tables but no
search implementation, so this is an independent reproduction attempt.

The first measurement targets the promising, reusable stage only: enumerate
Q6 induced linear-forest vertex sets with edge count 23–26, at least 27
vertices, and a fixed degree-two pattern (origin plus two canonical neighbors).
The paper's split argument says a hypothetical 53-edge Q7 pit has a least-used
coordinate with at most 7 crossing edges; its heavier Q6 layer has 23–26 edges,
at least `ceil(c/2)` components, and at least 27 vertices. If the labeled-set
count cannot be reproduced, the Q8 layer-pair route needs more algorithmic
details before its cost can be estimated. Symmetry-orbit reduction is a second
phase and is not mixed into this first timing measurement.

## Search-space and checks

The labeled search space is subsets of the 64 vertices of Q6 that include the
fixed pattern. Incremental constraints reject induced degree above two; final
candidates are checked directly for acyclicity and the edge/vertex/component
conditions. The source text gives 4,576,964 as the expected eligible labeled
count before the 5,041 orbit count. A mismatch is a correctness/debugging stop,
not evidence against the published result. No Q8 candidate is searched here.

## Resource and stop conditions

- At most 120 seconds wall time.
- At most 2 CPU cores and 2 GiB resident memory.
- Stop after 10,000,000 recursive search nodes if the census is incomplete.
- Record elapsed time, node count, eligible labeled count, peak RSS, and the
  first failed invariant. Do not continue into orbit reduction if the labeled
  census does not finish within these caps.
- No external PR, issue, or submission is part of this experiment.

## First bounded run

The initial exclude-before-include DFS reached the 10,000,000-node cap in
0.235 seconds, counted no complete assignments, and used 7,132 KiB maximum RSS.
This is a traversal-order diagnostic: it spent the node budget in sparse
prefix branches before reaching depth 64. It does not estimate the full census
cost. A second bounded diagnostic changes only the branch order to include
before exclude, keeping the same node, wall, CPU, and memory limits; its goal is
to measure whether eligible leaves are reached promptly. No symmetry reduction
or Q8 search is included.

The include-first diagnostic reached a full assignment in 65 nodes and exposed
a classification bug: the first such assignment had maximum degree two but
contained cycles. The search had incorrectly treated every leaf as an expected
forest and stopped on `edges != vertices - components`. This is a legitimate
candidate rejection, not an invariant failure. The next run corrects this by
counting and rejecting cyclic leaves while retaining the degree-sum invariant;
all resource caps remain unchanged.

The corrected include-first run hit 10,000,000 nodes in 0.414 seconds, found
55,895 cyclic full assignments and no eligible forest leaves, using 7,072 KiB
maximum RSS. Because this arbitrary node cap again prevented a useful timing
sample, the final feasibility phase uses dynamic branching: choose an undecided
vertex with the most already-selected neighbors, breaking ties by smallest
vertex label; include first, then exclude. The only search-size cap is 2.5
billion nodes, with the existing 110-second internal wall cap and 2 GiB address
space cap. This phase measures whether constraint-aware ordering reaches the
reported forest census at a useful rate. It still stops before orbit reduction.

## Exact-edge partition protocol

The dynamic run reached 2.5 billion nodes in 77.37 seconds (67.44 CPU seconds),
emitting 847,152 eligible masks and rejecting 990,634 cyclic leaves at 7,912
KiB maximum RSS. The reported total is 4,576,964, so the one-run node cap is
insufficient. Continue as four disjoint deterministic slices, exact edge count
`E=23,24,25,26`; their union is the original labeled census. Save each slice's
normalized 64-bit vertex masks only under ignored `.lake/snakepit8/` artifacts
for possible later orbit checking. Each slice has a 180-second internal wall
cap, 200-second external timeout, 2 GiB address-space cap, single-threaded
execution, and 6-billion-node cap. Four runs therefore consume at most 12 CPU
minutes; stop the sequence earlier if aggregate measured CPU reaches 14
minutes, any invariant fails, or a slice hits its cap. The expected sum is
4,576,964 masks; a mismatch requires debugging, not a result claim. Orbit
reduction and Q8 compatibility are explicitly out of this phase.

### Revised continuation after the first slice cap

The first exact-edge slice `E=26` stopped at its 6-billion-node cap after
118.50 CPU seconds, with 5,860 forest masks and 59,632 cyclic leaves. Its mask
file is only a partial slice and must never be treated as complete. To continue
under the requested aggregate budget, measure the remaining targets `E=25,24,23`
in that order, each with a 170-second internal cap, a 190-second external
timeout, and the same 6-billion-node / 2 GiB limits. These three runs consume
at most 510 CPU seconds. Combined with prior measurements (185.94 CPU seconds),
this leaves at least 204 seconds under the 15-minute total for one targeted
prefix-splitting or optimization attempt. Stop all compute at 840 aggregate
CPU seconds, any failed invariant, or a 2 GiB limit event. Record incomplete
slices as such. The aggregate census is complete only if every exact-edge mask
file is complete and the four counts sum to 4,576,964.

### Q6 profile upper-vertex pruning

Before the next run, use the published exact Q6 profile as an additional
sound pruning bound. The table gives `L(6,k)=26` only for `k=1,2`, `L(6,k)≤25`
for `k=3`, and `L(6,k)≤24` for `k=4,...,8`; Huang's bound
`L(6,k)+k≤32` excludes larger component counts at the relevant edge targets.
Therefore an eligible Q6 forest with 26 edges has at most 2 components and at
most 28 vertices; one with 25 edges has at most 3 components and at most 28
vertices; targets 23 and 24 have at most 32 vertices. Prune as soon as the
selected count exceeds the corresponding ceiling. This is a logically exact
consequence of the paper's Q6 table and Huang bound, and attacks the large
isolated-vertex tail directly.

Retry the incomplete `E=26` slice once with this pruning, capped at 170 seconds
and 6 billion nodes. This is not an exhausted range; the prior run stopped
incompletely. Then run the remaining exact targets `E=25,24,23` in that order,
each capped at 170 seconds and 6 billion nodes. Total additional compute is at
most 690 CPU seconds; including prior measurements (about 186 CPU seconds),
this remains below the 15-minute aggregate budget. Do not rerun any target that
completes. If any target hits both its cap and its vertex bound without
completing, preserve it as partial and stop that target; the remaining targets
still proceed under the aggregate limit.

The pruned `E=26` retry again hit 6 billion nodes, after 125.43 CPU seconds,
emitting 5,860 eligible masks and rejecting 32,214 cyclic leaves at 7,092 KiB
maximum RSS. Compared with the prior unpruned run, it reached the same forest
count and reduced cyclic leaves but did not reduce nodes. Treat this exact-edge
slice as incomplete; do not retry it again within this budget. Proceed with one
run each for `E=25,24,23`, using the already-recorded caps.

The single `E=25` run hit the 6-billion-node cap after 124.16 CPU seconds,
emitting 81,326 eligible masks and rejecting 186,240 cyclic leaves at 7,100
KiB maximum RSS. This is also incomplete; no retry is planned. Proceed to `E=24`
then `E=23` once each.

The single `E=24` run hit the 6-billion-node cap after 122.89 CPU seconds,
emitting 592,878 eligible masks and rejecting 732,873 cyclic leaves at 7,140
KiB maximum RSS. It is incomplete; no retry is planned. Run `E=23` once under
the same caps, provided the aggregate CPU budget remains available.

The single `E=23` run hit 6 billion nodes after 137.47 CPU seconds, emitting
1,444,364 eligible masks and rejecting 1,240,642 cyclic leaves at 7,100 KiB
maximum RSS. It is incomplete. The four exact-edge partial outputs currently
sum to 2,124,428 masks, far below the reported 4,576,964. The measured budget
remaining is about 144 CPU seconds under the 840-second aggregate stop.

Use this final budget for one diagnostic run on `E=23` tracking the remaining
degree capacity of selected vertices. If `r` vertices remain and their maximum
degree is 2, at most `floor((capacity + 2*r)/2)` additional edges can be added.
However, the tracked capacity is exactly `2*(vertices - edges)`, so this upper
bound simplifies to `vertices + r`. The existing minimum-size filter already
requires `vertices + r ≥ 27`, making the proposed edge bound redundant for
target 23. In replacing the previous `edges + 2*r` bound, it actually removes a
valid pruning in some branches. Run from the root into a separate `.lake`
artifact, with a 140-second internal wall cap, 145-second timeout,
6-billion-node cap and 2 GiB limit. This intentionally repeats the incomplete
E23 prefix to measure the changed bounded traversal; do not merge its masks
with the earlier prefix. Stop all compute after this one run, regardless of
completion.

The capacity-bound retry hit 6 billion nodes after 122.95 CPU seconds, emitting
1,422,003 masks and rejecting 1,223,129 cyclic leaves at 7,100 KiB maximum RSS.
It is partial. The two E23 files are alternate bounded traversals and must not
be merged. The mask file for each run contains exactly eight bytes per emitted
mask. Hashes and outcomes:

| Slice / run | CPU seconds | Nodes | Forest masks | Cyclic leaves | Max RSS | Outcome | Mask SHA-256 |
| --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| E26, initial | 118.50 | 6,000,000,000 | 5,860 | 59,632 | 7,180 KiB | partial | `562cf9b0d6b932862cd3a3ca88d273d407debf57d0ad5818b02382382ea58195` |
| E26, vertex bound | 125.43 | 6,000,000,000 | 5,860 | 32,214 | 7,092 KiB | partial, identical mask file | `562cf9b0d6b932862cd3a3ca88d273d407debf57d0ad5818b02382382ea58195` |
| E25 | 124.16 | 6,000,000,000 | 81,326 | 186,240 | 7,100 KiB | partial | `4ff1eb97d65f56ca9dc4aa0ed9aa3ababae120c71a02a036f3b2a6e9251dcbc5` |
| E24 | 122.89 | 6,000,000,000 | 592,878 | 732,873 | 7,140 KiB | partial | `7e29fc650bea39900e9d9d71f63341e3b7cf3c600af74a8c41ff0d2ffd004895` |
| E23, basic bound | 137.47 | 6,000,000,000 | 1,444,364 | 1,240,642 | 7,100 KiB | partial | `0bbe748d774b84682b0739502884ca2f09feccb72b505f8a5a8a1575491bfb3b` |
| E23, degree-capacity bound | 122.95 | 6,000,000,000 | 1,422,003 | 1,223,129 | 7,100 KiB | partial, alternate traversal | `641b37136e5247e759378b2a9aba675b1413a676443c0a7a54b2cddbe69b4dbc` |

Aggregate measured CPU was about 819.5 seconds (13.7 minutes), under the
840-second stop. No slice completed. The four target-specific partial files
using the latest run for each target contain 2,102,067 masks, not a complete
census. The E23 count differs between bounded traversals because the second
traversal replaced `edges + 2*r` with the weaker, redundant `vertices + r`
prune, so its node cap covered a different part of the search tree. This says
nothing about the complete counts, which should agree. The capacity expression
was not an optimization. The complete labeled census was not reproduced. Raw
Q6 layer generation consumed nearly the full budget and does not support
starting the much larger Q8 compatible-pair search without a more efficient
generator or the authors' implementation.

## Interpretation

Finishing the count reproduces only the Q7 enumeration stage; it does not prove
the Q7 completion exclusions, certify any CP-SAT result, or establish
`Λ(8)≤104`. The Q8 route still needs a complete compatible-pair search for Q7
layers with total internal edge count at least 92 and cross count at most 13,
plus a checkable certificate for every rejected pair.
