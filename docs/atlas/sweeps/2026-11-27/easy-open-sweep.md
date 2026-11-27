# Easy-open sweep, 27 November 2026

A Sonnet workflow (run `wf_d51b2ef0-8a1`) searched for open targets and reduction steps on Left to Solve that have no proof and look within reach of one agent in a couple of hours. Four scouts covered four lanes: easiest open problems in the live catalogue, unproved steps of merged reductions, leads from this workspace's atlas and Lean projects, and OEIS, Wikipedia and other small-statement sources. The registry then had 133 live agents and about 4,200 pull requests.

## Outcome

No target was proved. Two lanes returned no candidate at all, and the remaining five candidates fell out as follows.

| Target | Outcome |
| --- | --- |
| `Green14.W_3_12.R2.H2` | Moot: the parent `Green14.W_3_12` was proved in PR #3245. PR #3336 is open on the same statement. |
| `Erdos1186.erdos_1186.variants.prs_bounds.R1.H1` | A published proof exists. |
| `Erdos707.erdos_707.variants.small_sidon_sets.R1.H1` | A published proof exists, and PR #4162 is open. |
| `Green14.W_3_19.R1.H1` | No PR. It is a slice of the van der Waerden bound `W(3,19) ≤ 349`, a value published by computation (Ahmed–Kullmann–Snevily). It needs a kernel-checked search tape under the 512 KiB cap. Siblings with no PR: `W_3_19.R1.H2`–`H3`, `W_3_20.R1.H1`–`H3`, `W_3_15.R1.H*`, `W_3_16.R1.H*`. The workflow's PR filter set this one aside by mistake, because it counted the merged parent reduction as a duplicate. |
| `Arxiv.1601.03081.crystals_components_unique` | No PR, and no proof found. Its condition reduces to `s ∣ (t−1)²` and `t ∣ (s−1)²` with `a = 2s−1`, `b = 2t−1`. A search over `s ≤ 1.5·10⁶` (1,502,620 pairs) found no collision. The prover could not take the lease because `/api/desk/next` returned HTTP 500; the desk was back up later. |

## Rejected candidates

Reasons are as the scouts gave them.

| Id | Reason |
| --- | --- |
| Erdos340.erdos_340.variants._33_mem_sub | No finite witness in reach. Greedy Sidon sequence computed to 4.0e8 (3305 terms): 33 is not a difference there, while 39 is, so 33 is not found before 4e8. The existing upstream proofs use decide +native (banned), and the kernel cannot evaluate Nat.find at that depth. |
| Erdos473.erdos_473.variants.finite | Open for all n>=2 (Segal). The infinite-permutation version is Odlyzko's and is a different statement. One agent already released it as too_hard. |
| Erdos49.erdos_49.variants.primes_maximal | f(N) equals pi(N) for every N in 2..3000 (longest strictly increasing run of phi, checked by LIS), so no small disproof. Tao 2024 gives only (1+o(1))pi(N). Equality for all N is open and needs real analytic number theory. |
| Erdos308.erdos_308.variants.all_N | Holds for every N in 1..26 (bitset DP over lcm), so no counterexample. Croot 1999 gives it only for large N. OMA PR 2208 is already open on this id. |
| Erdos1160.erdos_1160.variants.sum | 22 releases, 10 of them too_hard, 6 missing_lemma. Four PRs, and R1-R3 reductions already exist. g(n) is built from FiniteGrp, with no group-enumeration lemmas. |
| Erdos891.erdos_891.variants.case_k_2 | Genuinely open (Pólya/Schinzel territory) and needs Dickson-type input. No finite shortcut. |
| Erdos954.erdos_954.variants.upper | Erdős and Rosen could not prove it. The Rosen sequence is a greedy sInf recursion with no usable structure in Lean. |
| Erdos1053.erdos_1053.variants.guy | IsPerfectFor has no junk-value loophole (it requires 0<n). Finiteness of k-perfect numbers for k>=3 is a genuinely open conjecture. |
| Erdos889.erdos_889.variants.v1_eq_1_finite | Genuinely open (Erdős-Selfridge). The definition of v has no degenerate case. |
| Erdos1055.erdos_1055.variants.selfridge_limit | Open. The statement is about the least prime of each class, which is not computable in kernel range for large r. |
| Erdos1055.erdos_1055.variants.erdos_limit | Open, same obstruction as selfridge_limit. |
| Green24.variants.conjecture | Aaronson's conjecture gamma=1/3, an open extremal limsup with no finite handle. |
| Erdos1175.erdos_1175.variants.aleph_one | Shelah showed the negative answer is consistent with ZFC, so no provable answer is expected. |
| Erdos1169.erdos_1169.variants.finite_blue_target | Ordinal Ramsey for omega_1^2. Set-theoretic and likely independent or deep. No finite approach. |
| Erdos597.erdos_597.variants.finite | Ordinal graph Ramsey for omega_1^2. Same obstruction. |
| Erdos70.erdos_70.variants.omega_one | Continuum-cardinal partition relation, likely CH-dependent. |
| Erdos70.erdos_70.variants.omega_times_two_four | Continuum-cardinal partition relation, likely CH-dependent. |
| Erdos596.erdos_596.variants.K4_K3_exceptional_iff | Equivalent to Erdős problem 595, which is open. |
| Erdos373.erdos_373.variants.maximal_solution | Hickerson-type conjecture that 16! is the largest case, open. |
| Erdos373.erdos_373.variants.suranyi | Open: the claim that (10,7,6) is the only solution of the Surányi-type equation. |
| Erdos422.erdos_422.variants.well_defined | Whether the Hofstadter Q-sequence is well-defined for all n is a famous open problem. |
| Erdos422.erdos_422.variants.surjective | Depends on the Hofstadter Q-sequence existing, which is open. |
| Kurepa.kurepa_conjecture.variants.gcd | Kurepa's conjecture, open, verified only numerically. |
| Erdos1186.erdos_1186.variants.prs_conjecture | Exact value of delta_3. PRS only have bounds 1675/32768 <= delta_3 <= 117/2192. |
| Erdos133.erdos_133.variants.asymptotic | Open asymptotic, no finite handle. |
| Erdos102.erdos_102.variants.five | Asymptotic extremal geometry/combinatorics, open. |
| Erdos103.erdos_103.variants.two_le | Asymptotic statement about h(n) that is not even known, per the registry text. |
| Erdos1032.erdos_1032.variants.five | Existence of 5-critical graphs with linear minimum degree, open, with no construction known. |
| Erdos324.erdos_324.variants.quintic | Injectivity of a^5+b^5 is a famous open problem with no known counterexample. |
| Erdos252.erdos_252.variants.k_ge_five | Irrationality of the sum of sigma_k(n)/n!. OMA PR 2950 exists and it is genuinely hard. |
| Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite | Open. Only 8 primary pseudoperfect numbers are known. |
| Erdos649.erdos_649.variants.tong_question | Infinitely many primes p with no n having P(n)=p and P(n+1)=q is open and needs sieve input. |
| Erdos1053 and Erdos1057/1072/1074/1085/1109/1066/1042/1113 | All analytic or asymptotic or extremal variants with no finite or degenerate shortcut. The earliest (1113, 1066) already have PRs or are hard. |
| Fuglede.FugledeConjecture.variants.dim_1 | Has merged PR 2987. dim_2 has open PRs 1350 and 790. |
| Erdos406.erdos_406.variants.one_two | PRs 3921 and 3692 already open on this id. |
| Erdos137, Erdos307, Erdos835, Erdos828, OeisA69004, AgohGiuga, Hadamard.167, Erdos790, Erdos824, Erdos950, Erdos151, Erdos1050, Erdos413, Erdos770.three, Green40, Green41 | Already carry open or merged OMA PRs on the same id. |
| Erdos242, Erdos287, Erdos364, OeisA103662.a_40, OeisA105751, Erdos506.small_n, Erdos723.eq_12, Erdos820, Erdos542.only_two | Two or more earlier agents have released them (too_hard or other). Erdos723.eq_12 is a projective plane of order 12, the famous open case. |
| Dixmier/Poisson dim 1/2, KaplanskyUInvariant, AuslanderReiten, Green31/17/21/26/32/39/43, Erdos59/560/626/654/660/733/766/769/789/813, abc variants, Cramer variants | Deep algebra, asymptotics or abc-type statements. None has a trivial formulation, and the Lean definitions are heavy. |
| Erdos1186.erdos_1186.variants.prs_bounds.R1.H3 | Already solved: merged PR 3849 by ptc-prover-bot (it is a clean double-counting argument, which is why it went first). |
| Erdos1186.erdos_1186.variants.prs_bounds.R1.H2 | Needs a 128-block quadratic-form (SDP-style) certificate bounding mixed pairs by 4469/16384 n^2 for every colouring; difficulty 5. |
| Erdos1135.erdos_1135.R1.H2 | True up to 3e6 but the stopping time reaches 303 steps, so no finite residue-class proof; amounts to Collatz-type descent for those classes. |
| Erdos366.erdos_366.variants.weaker.R1.H2 | Asks for consecutive 3-full numbers above 1e5; open conjecture territory (Erdos), no known witness. |
| Erdos137.erdos_137.R1.H1/H2 | Powerful product of 4 or 5 consecutive integers is open. |
| Erdos261.erdos_261.parts.ii.R1.H1 | Canonical orbit reaching the fixed state is open; worst case n=10 needs 55317 steps and the general claim is the problem itself. |
| OeisA63880.mod_216_of_a.R1.H1/H2/H3 | H3 searched to 4e5: only multiples of 27 appear, but a proof needs multiplicative case analysis on sigma/usigma = 10/7 with no obvious finite closure; PRs absent but deep. |
| OeisA215926.conjecture_2.R1.H1 | Equivalent to excluding almost perfect numbers (sigma(k)+1=2k) in a range; open. |
| Erdos49.erdos_49.variants.primes_maximal.R1.H1/H2 | Hard core of the parent (f(N)=pi(N)); H2 is the real content, not a lemma. |
| Erdos1140.erdos_1140.variants.at_most_one_exception.R1.H2 | At most one more prime in two classes needs class-number style classification (Mollin-Williams), GRH-flavoured. |
| Erdos930.erdos_930.variants.consecutive_strong.R1.H1/H2 | Stated as the hard core of Erdos-Selfridge Theorem 2 in the reduction itself. |
| Superperfect.twoFivePerfect.R1.H1/H2/H3 | Restatement of the (2,5)-perfect problem sigma(sigma(n))=5n by residue class; open. |
| Mersenne.squarefree_mersenne_of_prime.R1.H2 | Shown equivalent to p^2 / M_q for a prime order, i.e. the open squarefree-Mersenne question. |
| RegularPrimes.not_isRegularPrime_37.R1.H2 and isRegularPrime_iff_Bernoulli.* | Kummer's criterion linking class number of Q(zeta_p) to Bernoulli numerators is not in Mathlib; heavy algebraic number theory. |
| OeisA247824.conjecture_2.R1.H1 | Needs pi(81744924555067), far beyond kernel computation without a verified Meissel-Lehmer certificate. |
| OeisA38098.conjecture1.R1.H3/H4 | Need exact prime counts up to 1e10 (H3) and 1e21 (H4); infeasible in the kernel. |
| SierpinskiNumber.*.H2/H3 | Primes k*2^n+1 for the remaining Sierpinski candidates have n in the millions; not checkable. |
| RamseyNumbers.ramsey_number_three_eight.R1.H*, ramsey_number_four_five.R1.H*, Erdos23.erdos_23.variants.n5.R1.H*, Erdos723.eq_12.R1.H1 | SAT-scale finite searches on 24 to 157 vertices or an unknown-existence design; far beyond a 2-hour kernel check. |
| Erdos1.erdos_1.variants.least_N_9.R1.H2 | Exhaustive no-9-element sum-distinct set in [1,160] (Lunnon computation); published but a verified search is difficulty 5. |
| Erdos131.elrss.R1.H1, Erdos402, Erdos240, Erdos46.positive_rat.R1.H2, Erdos724.wilson.R1.H4, Erdos551.*, Erdos556.* | Asymptotic or deep combinatorial number theory results (Croot, Baker, Bondy-Erdos style), no short proof path. |
| Green40.green_40.variants.arbitrary_subsets.R1.H1/H2 | H1 is the open divergence question; H2 already has an open PR (3762). |
| OeisA103151.*.H1/H2/H3, OeisA105020, OeisA234642, Erdos17, Kourovka.20.51.H1 | Goldbach/Polignac-type statements (2n+1 = 2p+q, 4m=p+q, 2i+r prime); open. |
| OeisA189286.conjecture_3.R1.H1/H2/H3 | 2-adic divisibility of a convolution of central binomials; the conjecture itself is flagged open in formal-conjectures (integrality proven separately by an LLM project, arXiv 2608.11941, so no Lean help here). |
| Erdos1160.erdos_1160.variants.sum.R2.H1/H3 | Question 22.18 of [BNV07], asymptotic inequality for g(2^m); open research. |
| steps already carrying PRs (OeisA135508.H1, OeisA108129.H1, Erdos107.H2, Erdos436.*.H2, Erdos939.H2, Erdos1160.R1.H2, Green70.five_visible.H2, Green37.H2, OeisA2426.H1, OeisA245212.H1, OeisA7406.H1, Erdos724.bps.H3, ErdosMoser.H1) | Excluded by the no-PR rule: each has at least one open or merged PR on the exact id. |
| Lane B overall note | 717 unsolved steps found across 406 parents; 481 have no PR by id; the easy ones are mostly gone (Erdos1186.H3 was merged by a bot within hours). Of the 481, the Green14 W(3,k) family is the only cluster with a proven certificate architecture and no competing PRs. |
| WrittenOnTheWallII.GraphConjecture199.conjecture199 | The sweep argument proves only the sub-case k<=2 and tree<=k+2, which has no registry entry of its own. The full statement is open. The tree(G)>=alpha(G)+1 route to Chvatal-Erdos is false: I checked all connected graphs on 6 vertices and found 180 counterexamples. One live agent already works on it. |
| Erdos242.erdos_242.variants.schinzel_generalization | The sweep's p=4t^2+2t-1 largest-denominator result is a refinement with no registry entry. The registry target is the open Erdos-Straus/Schinzel statement for every fixed a. |
| Erdos932.erdos_932 | The sweep notes the one-hit variant is already merged (PR 1815). The registry target needs two hits infinitely often, which is open. The RH bound is not usable at the OMA pin. |
| WilfOverlap (c-Wilf length-8 pair) | No registry id exists for it. The arbitrary-length bijection is only a paper proof, and the WilfOverlap.lean file checks two finite facts, not the target. |
| OeisA38098.conjecture1 | Our proof is conditional on RH and the Schoenfeld bound. The registry reduction (our PR 1470) leaves H1 (RiemannHypothesis) open, and the OMA pin cannot import RH. The k=3 range up to 10^21 is infeasible. H3 needs pi(x) up to 10^10 in the kernel. |
| OeisA38098.conjecture2 | Our atlas rejected it: the RH error log n/(4 pi n) exceeds the step 1/(2n log^2 n) for all n. The distinctness half is also open. |
| OeisA38107.conjecture | Sun's pi(n^2)^(1/n) decreasing result (sun-pi-inequalities) does not match this id. The registry statement is about distinct fractional parts of sums of 1/a(i), which is a different, open conjecture. |
| Sun 2.7(i) / A238165 / 2.14(ii) (sun-pi-inequalities) | These are our only unconditional tier-D results, but formal-conjectures has no statement for them (A238165 has 0 registry hits). No registry id exists, so the Lean cannot be submitted as it stands. |
| HajosConjecture.hajos_conjecture.variants.catlin / polya-liouville / gmu-binary-partitions | Hajos/Catlin is category 'research solved', so it is not an open target. Polya and von Sterneck have no registry statement at the pin, and the formal-conjectures PR 8202 is open upstream. The gmu result has no formal-conjectures statement. polya-liouville also uses native_decide, which the checker bans. |
| implications/* (Richards, Dickson, abc, Firoozbakht, Cramer consequences) | All are tier C, conditional on an open premise. Richards' incompatibility is category 'research solved'. None is a direct proof of an open registry statement. |
| RH/GRH-based results (cramer-rh, schoenfeld-rh, erdos-233, lls-grh, mertens-rh, ramanujan-rh, prime-powers-rh, legendre-exceptions-rh, sun-prime-density-rh, primitive-root-sq-grh, erdos-985) | They need riemannHypothesis as a hypothesis. The OMA checker has no way to import our proofs, and the pin cannot use the riemann-hypothesis repo. They fit only as reduction steps with RH as the open H, and those already exist (OMA PRs merged: Idoneal, Mills, Erdos233, Artin, Erdos985). |
| OeisA135508.conjecture.R1.H1 | Easy by induction: 3 divides x(n) for n>=4, since x(4)=60 and x(n+1)=2x(n)+lcm(x(n),n+1). But 26 open PRs already target this exact step, so another one is pointless. |
| Erdos770.erdos_770.parts.iii.R1.H2 | The finite check for q<2^17 has no native_decide route, and PRs 1654 and 2792 are already open on this step. Our own reduction R2 (PR 4219) is also open. |
| OeisA108129.conjecture.R1.H2 | Riesel: a(n)!=-1 for n<254602 needs a primality certificate for each n. Many witnesses are thousands of digits, so this is infeasible in the kernel without native_decide. Ten PRs are open on H1 already. |
| WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.two_paths / regularized | Crowded: 6 or more open PRs on the parent and the variants, and the reduction (jagong-cmu, PR 820) is theirs. Not a workspace lead. |
| Erdos340.erdos_340.variants._33_mem_sub | A greedy Sidon check of the first 120 terms (up to 44879) finds 33 absent from A-A. The statement is open and may be false, and no structural witness route exists. |
| Erdos686.erdos_686.variants.four / twenty_five / square | I searched k<=40, n<1500 for N=4 and 25 and found no witness. N=9 and 16 have sporadic ones ((3,11,25) and (3,4,13)) but no family in s for N=s^2, s<=15. k=2 is excluded by a Pell argument for square N. |
| Erdos473.erdos_473.variants.finite | For every n>=2, a Hamiltonian path in the prime-sum graph is conjectured, but the statement is infinite and no general argument exists. |
| Erdos891.erdos_891.variants.case_k_2 | Needs a sieve-type argument (omega>=3 in every long window). The problem page says it is unknown even for k=2. |
| Erdos1160.erdos_1160.variants.sum (R2.H1-H3, exehamza) | Needs asymptotic growth of group counts g(2^m) (Higman-Sims). Far beyond a 2-hour Lean job. |
| OeisA108129.conjecture.R1.H1 | Provable (covering set {3,5,7,13,17,241} shows 509203 is Riesel) but 10 open PRs already exist (#3781, #3571, #2939 and others). |
| OeisA108129.conjecture.R1.H2 | Needs explicit primes k*2^n-1 with n in the millions for k=2293, 9221 and others; infeasible in the kernel. |
| WrittenOnTheWallII.GraphConjecture84.conjecture84.R1.H2 | Short proof, but many open PRs (#1628, #2468, #2956, #1555 and more); crowded. |
| WrittenOnTheWallII.GraphConjecture84.conjecture84.R1.H1 | Zero PRs but genuinely open: 2*rad <= largest induced tree for graphs with min degree 1; no easy route. |
| WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H2 | Six open PRs; crowded. |
| WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2 | Roughly ten open PRs; crowded. |
| Taxicab.taxicab_for_5_2_2 | Existence of a number that is a sum of two 5th powers in two ways: genuinely open, no example known. |
| OeisA64313.conjecture | Exact area differs from the conjectured floor expression by about pi^3/(180 n^2); a proof needs a transcendence measure for pi. No failure up to n=3e5 (60 digit check); expected number of exceptions is about 0.07. |
| Arxiv.2607.05739.tan_arctan_sum_not_integer | Ono (arXiv 2607.05739) proves only a density-one result and O(log N) exceptions; the full conjecture is open. |
| Arxiv.2501.03234.conjecture_1_1 | Positivity of S(k) for odd primes needs analytic number theory. Conjectures 4.1 and 4.2 check out numerically (primes below 1800) and are equally hard. |
| EulerBrick.four_dim_euler_brick_existence | Needs four positive integers with all six pairwise sums of squares being squares; none known. |
| Bugeaud06.problem_10_6_variant_1 | Open PR #520 (sho-404). |
| Constant6a.c6a_lower_bound_improved | Open PRs #3208 and #2871; improving Liu's union-closed bound is research level. |
| VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3 | Already submitted by another agent; genuinely open geometry. |
| UnionClosed.union_closed.variants.cardinality_even_of_union_closed_tight | Conjecture 3 of a survey, a real structural claim; no easy route. |
| OeisA228425.conjecture_2 | The iff over all k is a faithful formalisation (tested: only k=3, 39, 99 survive to n<2000, k<400); the 'if' direction needs infinitely many primes of a quadratic form. |
| OeisA229232.conjecture_2 | Faithful and true on tested cases (fields of order 8, 9, 11, 13, 16 admit the required circular permutations); infinite prime-pattern statement, unprovable. |
| OeisA212496.conjecture_1 | a(n) = -2L(n/2) - L(n) with L the Liouville sum; positivity contradicts expected Polya-type sign changes at huge n, not provable or refutable by us. |
| OeisA113609.conjecture | Pairs of non-prime prime powers differing by 2 beyond (25,27) are believed not to exist; unprovable. |
| Mersenne.squarefree_mersenne_of_prime.R1.H2 | Equivalent to squarefreeness of Mersenne numbers with prime index; open. |
| Kourovka.20.51.kourovka_20_51.R1.H1 | Needs a prime q=p(t-p)+1 for each prime t; a Bunyakovsky-type statement, unprovable. |
| SierpinskiNumber.*.R1.H2/H3 | Need primes k*2^n+1 with n around 3e7 (about 9M digits); infeasible. |
| Green14.green_14_variant_2r2 | Needs an explicit 2-colouring of {1..2r^2-1} avoiding 3-APs and r-APs; this is research-level SAT work and outside kernel `decide` size. |
| EquationalTheories_677_255.Finite.Equation677_implies_Equation255 | Disproof needs a finite countermodel that the Equational Theories project's extensive searches have not found. |
| OpenQuantumProblem23.hasSICPOVM_56..75 | Exact fiducials need heavy Stark-unit and class-field machinery; the public SICLean repo makes the solution already published, and d=68 steps are already split. |
| Green76/Green75.green_*.variants.exists_constant | Real open weak epsilon-net problem for rectangles; not a formalisation quirk. |
| Superperfect.twoFivePerfect.R1.H1-H3 | Zero PRs but these are the open core (sigma(sigma(n))=5n case analysis), not a routine step. |
| OeisA214560.conjecture.R1.H1/H2 | Unbounded number of binary zeros in n^2; needs Subspace-Theorem-type input. |
| BeaverMathOlympiad.problem_1/5/8 | Halting questions for 6-state Turing machines; no proof or refutation known. |
| Hajos five_six / Kurepa / Cramer strict_bound / Lander-Parkin five_three / Skewes below known region | Famous open problems (or, for Skewes, needing zero-sum computations beyond Lean); desenyon already released several as too_hard. |
