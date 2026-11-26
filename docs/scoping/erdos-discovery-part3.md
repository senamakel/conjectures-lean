# Discovery, slice 3 of the open Erdős problems (#830–#1221)

Date 2026-11-24. Research only: no repo was edited and nothing was built. Live pages and comment
threads were read through Exa (`erdosproblems.com/<n>` and `erdosproblems.com/forum/thread/<n>`).
Small sanity computations ran under `nice -n 19`; their scripts are in the session scratchpad
(`p3/`), and none took more than a few CPU-minutes.

**Result: no candidate is kept.** I found nothing in this slice where we could realistically prove
something that is both open and not already claimed, at any of grades (A), (B) or (C). The
near-misses below show why. Most of them have been attacked in public during 2026, often with
AI assistance and Lean, and the rest need input that neither RH/GRH nor a finite computation
supplies.

## 1. Coverage

- Input: `atlas/erdos_open_part3.json`, 214 problems (213 `open`, 1 `partially_resolved`: #848).
  I read every statement and every commentary in full, as a dump paged through in order.
- Rough split by tag: number theory without a primes tag 88, number theory with one 17,
  graphs/hypergraphs/combinatorics/groups 41, analysis/probability 23, geometry 16, additive
  combinatorics 15, set theory 14. One problem has a formal-conjectures statement in the harvest
  (#1112). Seven are flagged `finite_witness` (#835, 848, 982, 993, 1020, 1041, 1082).
- 16 problems were shortlisted and checked against the live page and comment thread:
  #835, 848, 933, 939, 963, 1041, 1056, 1059, 1110, 1112, 1209, 1210, 1212, plus 913, 979 and
  1065 from the commentary alone. I ran sanity computations for #1212 and #1110.
- I skipped #969 and #985 (already scoped), and #971 and #1141 (in the earlier discards).

## 2. Ranked candidates kept

None.

## 3. Near-misses (live state checked unless noted)

- **#1212** (an infinite path of coprime lattice points avoiding prime–prime pairs). This looked
  like it might fall to a periodic construction, and I tested two. Vertical strips of composite
  columns are blocked: by CRT, every strip of bounded width has a row y sharing a factor with
  each column, and BFS confirms this (strips of width 3–33 die below y≈500). Diagonal bands
  y = x + d, |d| ≤ D, are blocked for every D (residue-graph search, D ≤ 12, no surviving
  states). This agrees with Duncan's Lean-checked "drift obstruction" in the thread (no
  qualifying path stays within bounded distance of the diagonal). There is also a
  formal-conjectures PR #4218 (June 2026) and a determinant-method post (Aug 2026). The problem
  needs control at every scale, a Jacobsthal-type issue. Not a quick win.
- **#933** (limsup 2^k3^l/(n log n) = ∞). Thread, Feb 2026: GPT-5.2 and Tao give a
  *heuristic* proof via 3-adic digits of log₃(−1/(2a))/log₃4. Tao says the needed digit
  hypothesis is "comparable to … normality … well out of reach". One Zenodo "negative answer"
  was refuted in the thread. I reached the same reduction independently (we need 4^e·m ≡ −1
  mod 3^b with e·m ≤ 3^b/ω). Character sums to prime-power moduli might give something, but
  that would be research, not a plan.
- **#1110** (density of numbers representable as sums of p^a q^b with no summand dividing
  another). The open pairs are density for (4,3), (5,3), (5,2), (7,2), (9,2) and infinitely many
  coprime non-representable numbers for {2,5}, {2,9}, {3,5}. The obvious route, counting
  antichains, fails. I computed the growth exponent of the number of antichains in
  {p^a q^b ≤ N} exactly by DP (L = log N up to 800): 1.11 (4,3), 1.02 (5,3), 1.25 (5,2),
  1.12 (7,2), 1.04 (9,2), all above 1. For (7,3) it is 0.92 and for (11,2) 0.98, which matches
  the Yu–Chen thresholds, so their method is exactly this count. The sum ≤ N constraint does not
  lower the exponent. A proof would have to exploit collisions among the sums.
- **#835** (χ(J(2k,k)) = k+1?). Ma–Tang settle every k with k+1 not prime. k = 10 and k = 12
  are excluded through Steiner-system non-existence (athvedt, May 2026). The first open case,
  k = 16, would need a large set of S(15,16,32); a Sept 2026 Kramer–Mesner/SAT attack
  (veljjanoski) left the symmetric cases undecided. Too hard.
- **#1056** (k adjacent intervals with products ≡ 1 mod p, for every k). Witnesses exist for
  k ≤ 14 (OEIS A060427). Infinitely many primes work for k = 4 (Lean, June 2026, via a
  Wilson-theorem trick, Hardy–Subbarao). Arbitrary k is open, and finding witnesses does not
  close it.
- **#848** (max set with ab+1 never squarefree). Sawhney proved it for large N. AI-assisted
  explicit thresholds have brought N₀ down to 2.64·10¹⁷ (Mar 2026). Closing N < N₀ is a
  max-clique problem, so N₀ would have to drop by about 13 orders of magnitude. Crowded and
  infeasible.
- **#963** (dissociated subset of size ⌊log₂ n⌋). A thread claim gives (1−o(1))log₂ n, and
  small-n counterexamples to "{1..n} is extremal" were found (Sept 2026). The exact floor
  statement is out of reach.
- **#1210** (pairwise coprime A ⊂ [1,n), Σ1/(n−a) ≤ Σ1/p + O(1)). The sieve gives
  ≤ (2+o(1)) loglog n. Getting constant 1 implies a form of the second Hardy–Littlewood
  conjecture (thread, Apr 2026: Bloom, Sothanaphan). The bound loses at the parity barrier.
- **#1059** (infinitely many primes p with every p − k! composite). The sieve route fails: k!
  is divisible by every small prime, which inflates the singular series, so the expected number
  of prime p − k! is ≍ 1. Upper-bound sieves lose a constant ≥ 4, and GRH level x^{1/2} does
  not fix that.
- **#939** (r = 4: coprime 4-powerful a+b=c). Cambie searched exhaustively with no solution
  for max(a,b) ≤ 10¹⁴, and abc predicts none. Extending a search proves nothing.
- **#1209**, remaining sub-questions (always or infinitely often squarefree or prime values of
  n + 2^{2^k}). These amount to Fermat-number squarefreeness or Fermat primes (ebarschkis,
  Apr 2026).
- **#1041, #1112: claimed solved after the harvest.** For #1041, ani's degree-7 counterexample
  (Sept 2026) has an independent Lean check (williamwkcook). For #1112, a claimed full
  dichotomy (r_k exists iff d₂ ≥ k+1) is posted with a sorry-free Lean proof.
- **#913, #979, #1065** (commentary only): these need prime values of polynomials
  (8p²−1 prime; prime-parametrised k-th power sums) or prime-pair-type statements. RH/GRH
  gives none of them.

## 4. Bulk discard summary (214 problems)

| Reason | Count (approx.) | Examples |
|---|---|---|
| Set theory / partition calculus (consistency or GCH questions) | 14 | 918, 919, 1167–1177, 1218, 1220 |
| Extremal / Ramsey / chromatic graph and hypergraph asymptotics, no finite closing case | ~38 | 836, 857, 901, 902, 911, 917, 944, 1011, 1013, 1020, 1029, 1030, 1032, 1035, 1104, 1155–1158, 1178, 1182, 1183 |
| Discrete geometry (distances, convexity, unit-distance graphs) | 16 | 831, 838, 953, 956, 959, 982, 1066, 1070, 1082–1088, 1207, 1208 |
| Complex/real analysis, polynomials, lacunary series | ~22 | 906, 973, 995, 996, 1002, 1038–1040, 1045, 1117, 1120, 1131–1133, 1150–1152, 1154, 1221 |
| Prime-distribution questions beyond RH (short-interval/Cramér, prime tuples, Hardy–Littlewood 2) | ~20 | 852, 853, 855, 860, 932, 950, 961, 962, 968, 970, 972, 1137, 1139, 1142, 1184, 1201, 1203, 1204 |
| Arithmetic functions / divisors / factorials: asymptotics or "infinitely many" needing new ideas | ~45 | 830, 849, 850, 856, 859, 878, 879, 885–893, 912, 928–931, 945, 955, 975, 976, 1003, 1004, 1052–1055, 1060–1063, 1072–1074, 1093–1095, 1100, 1101, 1106, 1122, 1143 |
| Powerful / abc-type Diophantine | ~10 | 935, 936, 938, 940, 942, 943, 978, 1107, 1108, 1113 |
| Additive combinatorics, Sidon sets, bases: asymptotic constants | ~20 | 839, 840, 864, 866, 870, 873, 875, 876, 881, 954, 1097, 1103, 1109, 1145, 1146, 1186, 1191, 1192, 1194, 1199, 1200, 1206 |
| Famous/hopeless (Collatz, Singmaster, amicable, Carmichael x^{1−o(1)}, Gaussian moat, Chowla irrationality) | ~8 | 830, 849, 952, 1049, 1057, 1135, 1160, 1162, 1163 |
| Already resolved or claimed after the harvest (main question) | ~6 | 1041, 1112, 1207 (main question answered by LPZ26), 1209 (main parts), 939 (parts 1 and 3), 872 (final question) |
| Scoped elsewhere | 4 | 969, 985, 971, 1141 |

Counts overlap a little and are approximate. Every problem not named in section 3 falls into
one of these rows on its statement and commentary alone.

## 5. What this slice says about the method

- The RH/GRH toolkit (ankeny, bach-sorenson, cramer, schoenfeld, mertens) found **no** use in
  this slice. The prime-flavoured problems here need Cramér-scale gaps, prime tuples, or the
  parity barrier broken, and RH gives none of these.
- The finite-computation angle (C) fails for a common structural reason. Where an explicit
  threshold exists (#848: 2.6·10¹⁷), the finite range is a combinatorial optimisation, not a
  simple check. Where the question is "for every k" (#835, #1056), witnesses for small k do not
  close it.
- Anything elementary and visible in this slice has a 2026 thread with AI-assisted attempts,
  often including Lean (#1041, #1112, #1056, #1209, #1212, #939). That matches the crowding seen
  in the earlier discovery report.
