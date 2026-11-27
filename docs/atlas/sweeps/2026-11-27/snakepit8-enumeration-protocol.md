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

## Independent validation

A separate pass over the latest four mask files rebuilt the induced
hypercube graph for each mask and checked the required vertex count,
edge count, fixed pattern, maximum degree two, and acyclicity by
union-find. It also checked that each file contains distinct masks and
no incomplete record. All 2,102,067 masks passed. These checks verify
the emitted records, while the node caps leave the enumeration partial.

## Interpretation

Finishing the count reproduces only the Q7 enumeration stage; it does not prove
the Q7 completion exclusions, certify any CP-SAT result, or establish
`Λ(8)≤104`. The Q8 route still needs a complete compatible-pair search for Q7
layers with total internal edge count at least 92 and cross count at most 13,
plus a checkable certificate for every rejected pair.

## Optimized E23 benchmark (pre-recorded)

This benchmark tests two search-order optimizations on the exact `E=23` Q6
slice. It uses the prior useful upper bound `edges + 2*remaining_count`; the
redundant degree-capacity expression remains available as `--capacity-bound`
for reproducing that earlier variant. The default branch and previous commits
retain the earlier implementation and measurements.

### Eligible-set preservation

The normalized target family is all vertex masks in Q6 that contain `0,1,2`,
have at least 27 vertices, induce exactly 23 edges, have maximum induced degree
at most two, and are acyclic. The optimized traversal must emit this same set
when it finishes; traversal order and bounded prefixes may differ.

**Forced degree-two exclusions.** The `blocked` mask is the union of the
neighborhoods of selected vertices whose current induced degree is two. If a
blocked undecided vertex `u` were later selected, its selected neighbor `v`
would gain a third induced edge. Since selected vertices are never removed,
every completion containing `u` would violate the degree bound. Removing
`blocked` bits from `remaining` therefore discards no eligible completion. On
an include branch, the code adds `N(v)` to `blocked` when an existing selected
neighbor transitions from degree one to two, and adds `N(x)` when the new
vertex `x` has degree two. Exclude branches preserve the previous blocked mask.

**Early cycle rejection.** The fixed initial set `{0,1,2}` induces the path
`1—0—2`. Maintain its selected-graph components with rollback union-find.
Adding a vertex with zero or one selected neighbor cannot create a cycle. If a
new vertex `x` has two selected neighbors `y,z` in the same current component,
then the existing path from `y` to `z` together with `y—x—z` is a cycle, so no
acyclic completion can contain `x`. If they are in distinct components, adding
`x` only joins those components. The recursion rollback restores the prior
component partition. Every prefix of an eligible final forest is itself
acyclic, so early cycle rejection removes no eligible final set. The terminal
acyclicity check remains as an invariant check; with early rejection enabled,
`cyclic_leaves` should remain zero.

Together, these rules preserve exactly the normalized target set on a complete
traversal. The independent validator checks every emitted record's uniqueness,
fixed pattern, vertex count, induced edge count, degree bound and acyclicity;
the proofs above address omitted-set soundness.

### Bounded benchmark

Create a new mask file under ignored `.lake/snakepit8/` storage and run only
`E=23` with both flags enabled. The prior unchanged baseline was 6 billion
nodes, 1,444,364 masks and 137.47 CPU seconds; do not rerun it. Use one thread,
a 2 GiB virtual-address-space cap, a 140-second internal wall cap, a 150-second
external timeout, and the existing 6-billion-node cap. Record CPU/wall time,
maximum RSS, node count, emitted mask count, forced-exclusion count, early-cycle
prune count, cycle leaves, completion status, byte length and SHA-256. Run the
independent validator on the resulting file. A cap or invariant failure means
the file is partial; do not merge it with any earlier partial traversal. If
complete, it gives the exact normalized `E=23` slice only. No other edge slice,
Q8 pair search, push, or external post is part of this benchmark.

### Benchmark result

Command: `enumerate_q6_heavy_layers 23 .lake/snakepit8/q6-e23-forced-cycle.bin
--force-saturated --early-cycle`, under `ulimit -v 2097152` and
`/usr/bin/time -v timeout -k 2s 150s`. It stopped at the 6-billion-node cap,
after 126.40 CPU seconds and 126.43 wall seconds, at 7,176 KiB maximum RSS.
It emitted 3,094,237 masks, recorded 1,648,287,490 forced exclusions,
87,187,141 early-cycle prunes, and zero cyclic terminal leaves. The file is
24,753,896 bytes with SHA-256
`b344573ab83fc21c79582639c2f363ccf0ccf423023060fd4aa8ec07e2280cf3`.

The independent Python validator checked all 3,094,237 records for uniqueness,
normalized vertices, at least 27 vertices, exactly 23 induced edges, maximum
degree two, and acyclicity. It passed in 49.95 wall seconds (49.72 CPU seconds,
404,652 KiB maximum RSS). At the same 6-billion-node cap, the prior baseline
emitted 1,444,364 masks in 137.47 CPU seconds; this combined variant emitted
about 2.14 times as many masks and had zero cyclic terminal leaves. These are
bounded-prefix throughput figures, not complete slice counts or a comparison
of equal mask prefixes. The output is partial, so the masks were not merged
with prior artifacts. The two soundness arguments above establish that a
completed traversal retains exactly the same eligible normalized set; the
independent validator confirms every emitted record is a member of that set.

## Deterministic checkpoint/resume implementation and synthetic validation

The enumerator accepts `--checkpoint FILE`, `--resume`, and `--node-cap N`.
The checkpoint records the search parameters, output byte offset, cumulative
counters, and a frontier of branch-decision prefixes. At a node cap, the
current unvisited subtree and each not-yet-entered sibling are stored as an
antichain: no frontier prefix is an ancestor of another. Decisions are pairs
`(vertex, include/exclude)` under the deterministic dynamic variable order.
Resume replays each prefix from the normalized root, recomputes forced
exclusions and degrees, and rejects a prefix if its next recorded vertex no
longer matches the search configuration. It truncates the output to the
checkpoint's flushed byte offset before appending. This makes interrupted
search continuation disjoint from completed subtrees, assuming the checkpoint
and mask file belong to the same run and are not modified externally.

The bounded validation fixture is deliberately separate from all Q6 artifacts:
dimension Q4, seed `{0,1,2}`, target 3 edges, minimum 3 vertices, both sound
pruning flags enabled, and at most 13 newly processed search nodes per process
invocation. A test repeatedly resumes until the frontier empties, with a hard
limit of 1,000 invocations. It checks frontier prefix-freeness after every
checkpoint, output record alignment and uniqueness after every resume, then
compares the final set against both an uninterrupted Q4 traversal and an
independent exhaustive scan of all 2^13 masks containing the seed. This is a
correctness test of checkpoint semantics, not a Q6 performance measurement.
No E23, E24, E25 or E26 search is authorized by this fixture.

The previous E23 optimized output has no checkpoint/frontier record. Its last
emitted mask only locates a tentative point in the deterministic DFS: the
bit-5 include subtree appears complete and the bit-5 exclude subtree is partial.
The unreported no-output tail after that last mask cannot be recovered from
the mask file or aggregate counters. Resuming from a reconstructed path could
therefore redo an unknown amount of work; that artifact is not an exact
continuation checkpoint. Keep it partial and do not append to it. A genuine
Q6 continuation requires either a new checkpointed run from the root or a
separately logged prefix partition whose completed subtrees are known.

The synthetic check passed with 46 normalized Q4 masks after 17 capped
invocations. The resumed set equaled both uninterrupted DFS and the independent
2^13-mask exhaustive scan. Every intermediate frontier passed the prefix-free
check; every resumed output was record-aligned and duplicate-free. The test
also confirmed empty-frontier repeated resume is idempotent and that truncated
output, malformed checkpoint data, misaligned offsets, an offset/count
mismatch, and a checkpoint path equal to the output path are rejected. The
enumerator compiled with `-std=c++20 -O3 -Wall -Wextra -Werror`. This provides
small-instance evidence for checkpoint correctness only. No Q6 run was made,
so there is no Q6 continuation timing result and no evidence yet that the
checkpointed traversal improves Q7 census feasibility or makes Q8 pair
compatibility practical.
