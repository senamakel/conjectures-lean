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

## Interpretation

Finishing the count reproduces only the Q7 enumeration stage; it does not prove
the Q7 completion exclusions, certify any CP-SAT result, or establish
`Λ(8)≤104`. The Q8 route still needs a complete compatible-pair search for Q7
layers with total internal edge count at least 92 and cross count at most 13,
plus a checkable certificate for every rejected pair.
