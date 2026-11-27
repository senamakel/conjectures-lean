# Medium-difficulty Open Math Agents sweep

On 2026-11-27 the live catalogue rated each target 47/100 and showed zero active agents. The exact statements below use formal-conjectures revision `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, Lean `v4.33.1`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The local Open Math Agents catalogue was at `72791e06468b6b2f5143ffbf67ae52c9aa08acf5`. The live steps queries returned no registered reductions for these parents.

Discovery used the live catalogue and briefs, GitHub PR title and ID searches, the local registry proof and reduction directories, the repository atlas, LivingBrain, and the Claude Code and Codex transcript scanner. Lemmagraph's registry index provided overlapping Maxwell declarations at the registry pin. Its Mathlib index suggested affine-space and natural-division lemmas at a newer pin. The Lean checks below used the registry pin.

## Maxwell for three charges

**Registry ID** `Arxiv.2607.27197.maxwell_conjecture.variants.three_charges`. For any three distinct sites in Euclidean three-space and any three nonzero real charges, if every equilibrium off the sites has a nondegenerate Hessian, the equilibrium set has extended cardinality at most four. The exact declaration is [at the pinned source](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Arxiv/2607.27197/MaxwellConjecture.lean#L244). [Live registry](https://lefttosolve.com/p/Arxiv.2607.27197.maxwell_conjecture.variants.three_charges)

Exa searches for arbitrary unequal signed charges and for the Gabrielov–Novikov–Shapiro distance-ratio reduction located a published bound of twelve and the equal-magnitude special case. The 2026 five-charge counterexample concerns a different number of charges. GitHub surfaced the merged two-charge proof, whose single-term differentiation argument is reused with credit to @harshshah1618. The three-charge title search returned no matching PR. [Published bound and planar reduction](https://arxiv.org/abs/math-ph/0409009) · [Equal-magnitude case](https://doi.org/10.1016/j.physd.2015.07.007) · [Five-charge counterexample](https://arxiv.org/abs/2607.27197) · [Two-charge Lean proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/289)

[MaxwellAffineSpan.lean](MaxwellAffineSpan.lean) proves that the equilibria of three affinely independent sites lie in their plane, including for mixed signs. With weights `-qᵢ / ‖x - aᵢ‖³`, zero force and zero total weight would give a nontrivial affine dependence. Normalizing the weights then gives an affine combination. Lemmagraph's `affineIndependent_iff_of_fintype` supplies the key exclusion.

For a sharper count, Gabrielov–Novikov–Shapiro's coordinates give a concrete real algebraic problem. Normalize the first two sites to `(0,0)` and `(1,0)`, the third to `(a,b)` with `b ≠ 0`, and scale charges to `(q₁,q₂,1)`. Put `u = r₁/r₂`, `v = r₁/r₃` with both positive. The common denominator is `D = q₁ + q₂ u³ + v³`. Set `X = a v³ + q₂ u³` and `Y = b v³`. The two necessary equations are

```text
u² ((X − D)² + Y²) = X² + Y²
v² ((X − aD)² + (Y − bD)²) = X² + Y²
```

On this branch, retain only `D ≠ 0` and points `(X/D,Y/D)` away from the sites. The noncollinear counting obligation is to show at most four such equilibria under the Hessian hypothesis. For collinear sites, the Hessian hypothesis excludes off-axis equilibria by rotational symmetry, leaving a separate one-variable count. The Lean artifact checks the plane restriction. The algebraic count and collinear branch remain open here.

## Antihydra

**Registry ID** `BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.variants.set`. For every natural sequence with `a 0 = 8` and `a (n+1) = (3*a n)/2`, every prefix `[0,n)` has at most twice as many odd entries as even entries. The source connects this to the machine found by mxdys and Rachel Hunter. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Other/BeaverMathOlympiad.lean#L114) · [Live registry](https://lefttosolve.com/p/BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.variants.set) · [Problem source](https://bbchallenge.org/antihydra)

Exa searches for the floor recurrence and parity-prefix bound found the machine reformulation and computational work. The live brief recorded a prior release marked too hard. GitHub's Antihydra title search returned no matching PR. No prefix simulation was repeated. [Machine and recurrence](https://wiki.bbchallenge.org/wiki/Antihydra)

[AntihydraParity.lean](AntihydraParity.lean) reformulates the exact target as a lower bound of `n/3` even terms along the canonical orbit from 8. Its shift formula shows that the first `n` parity bits depend only on the seed modulo `2^n`. Lemmagraph identified `Nat.add_mul_div_left` for the induction step. Seeds `1 + 2^n*k` have all-odd prefixes of length `n` for arbitrarily large `k`. Consequently a uniform even-count bound based solely on seed size cannot close the argument. The missing input is a prefix estimate specific to the orbit from 8.

## Bugeaud's logarithmic ratio floor

**Registry ID** `Bugeaud06.problem_10_6_variant_1`. The target asks for a strictly increasing natural sequence whose consecutive ratios are eventually at least `1 + c/log n` for some `c > 0`, with every irrational dilate dense modulo one. Exa searches on that ratio floor, Katz and Boshernitzan identified the weaker growth reading and published density results. The exact variant already has an open submission using odd multiples of powers of two, Dirichlet approximation and dyadic rescaling. Its GitHub check passed and human review was pending. Further work on this candidate would duplicate PR #520. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean#L250) · [Katz](https://arxiv.org/abs/1607.00670) · [Submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/520)

## Verification

The two research artifacts use `lake env lean` in the pinned formal-conjectures checkout. Their axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`, or a subset. No submission or desk lease was created.

## Follow-up after submission

The Maxwell reduction passed upstream CI in [PR #4126](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4126). A follow-up Exa search found [Kintali's August 1 preprint](https://shivakintali.github.io/papers/Maxwell3.pdf), which claims at most four critical points when the critical set is finite and at most two for collinear sites. Remark 1.1 explains how nondegeneracy gives finiteness via semialgebraicity. The PR now cites this claim. Further work on the same count was stopped on prior-art grounds. The preprint's noncollinear proof has not been independently verified here.

A parallel Luna attack checked the shift from Antihydra's rounded-down orbit starting at 8 to the rounded-up Hydra orbit starting at 7. The terms differ by one, so parity is complemented. The remaining prefix bound stays open. [AntihydraParity.lean](AntihydraParity.lean) · [bbchallenge background](https://wiki.bbchallenge.org/wiki/Antihydra)

The live registry rated `Erdos473.erdos_473.variants.finite` 47/100. Its pinned target is a permutation of `1,…,n` for each `n ≥ 2` with prime sums at adjacent positions, without a closing-edge condition. GitHub and the live reduction list showed no overlapping submission. Exa found She’s prime-circle theorem for sufficiently large even orders, with no explicit threshold in the statement, and the solved infinite variant reported by Erdős and Graham. Neither covers the exact all-orders finite target. The checked reduction rotates an even prime circle to put the largest value last, deletes it to obtain an odd path, or cuts the closing edge for an even path. Backtracking generated witnesses for sizes 2 through 16, checked with Lean's kernel `decide`. The remaining conditions ask for circles from order 18 onward in the two even residue classes modulo four. [Problem source](https://www.erdosproblems.com/473) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/473.lean) · [She’s preprint](https://arxiv.org/abs/2609.19114)

The official checker accepted the Erdős 473 reduction with only standard axioms. It was submitted upstream in [PR #4309](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4309).
