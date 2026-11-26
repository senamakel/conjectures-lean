# Erdős discovery, slice 2 (problems 415–829): where could we prove something genuine?

Date 2026-11-24. Research only: no repo was edited, nothing was built, no lake or lean was run.
Input: `atlas/erdos_open_part2.json` (session scratchpad; erdosproblems.com harvest of 2026-09).
Live state was checked through Exa on erdosproblems.com forum threads, erdosproblemaday.com,
erdosproblems.ai, aiXiv, ProofXiv, Zenodo and arXiv. Claims I could not confirm from a primary
source are marked *(unverified)*.

## 1. Slice covered

- **214 problems** (207 `open`, 7 `partially_resolved`). By first tag: 86 number theory, 71 graph
  theory, 22 geometry, 10 additive combinatorics, 10 combinatorics, 9 analysis, 5 set theory,
  1 Diophantine approximation.
- I read every statement and commentary in full, dumped to text with `python3 -I`, not filtered by
  keyword. The `lean` field is `False` for all 214, so it is useless; formal-conjectures was only
  checked where a candidate survived the first pass.
- Each problem was sorted into one of three groups: (A) a finite computation, construction or short
  argument; (B) an unwritten RH/GRH-conditional result; (C) closing a finite range. I fetched the
  live pages and searched for 2025–2026 work on the 12 problems that survived that sort: 436, 458,
  479, 488, 617, 647, 686, 700, 726, 779, 820, 828.
- Excluded as instructed: 770 (in progress); 462, 684 and 769 (assessed in
  `discovery-unwritten-rh-consequences.md`). I did not re-propose anything from that report's
  discard list (456, 663, 680, 681, 820, 445, 436-type, 470, 420, 478 …) because I had no new idea
  for any of them.

## 2. Candidates kept

**None.** I don't think any problem in this slice offers a result that is both reachable and not
already claimed. The three that came closest were taken between July and November 2026, two of them
with Lean proofs. The rest need mathematics far beyond a few pages, or input that RH/GRH does not
give.

The three most attractive targets, with what I found about each:

| # | What we could have done | What is already there (live, checked 2026-11-24) |
|---|---|---|
| **617**, Erdős–Gyárfás balanced colouring, case r = 5 | SAT / UNSAT certificate, Lean-checked via LRAT | **Done, repeatedly.** Xia–Szeider, arXiv:2610.24484 (17 Oct 2026): a Lean 4 reduction plus 12,296 drat-trim-checked SAT-modulo-symmetries subproblems. Sneiderman, aiXiv 2609.02999 (21 Jul 2026), a non-computational proof. Kara, aiXiv 2609.03121, a Lean verification with only the 3 standard axioms (89 LRAT certificates replayed in the kernel). N. Winter, `github.com/nwinter/erdos-617-r5`, a Lean proof of `erdos_617_r5_unconditional`. Howell, Zenodo 10.5281/zenodo.23485982, an independent SAT route. At least five AI-assisted proofs. The all-r conjecture is open and out of reach. |
| **436**, is Λ(5,3) finite? (three consecutive quintic residues) | Lehmer-style reduction to a finite labelling CSP over primes ≤ B, then an UNSAT certificate | The reduction is public (erdosproblemaday.com report 436, 28 Jul 2026, which also gives Λ(5,3) ≥ 37,329,226). ProofXiv paper, 16 Nov 2026: a Lean certificate for Λ(5,3) ≥ 99,999,999 and Λ(7,3) ≥ 9,999,999, and computationally ≥ 313,714,024. Plasma AI 2026 claims "yes for every odd k" assuming a case of the logarithmic Elliott conjecture *(pending, unverified)*. Finiteness would need an UNSAT certificate at an unknown B > 3·10⁸ over roughly 1.7·10⁷ prime variables. The report itself says no defensible cost estimate exists. Another lower-bound bump is worthless. **Drop.** |
| **647**, is there n > 24 with max_{m<n}(m + τ(m)) ≤ n + 2? | Push a kernel-checked exclusion further | Kernel-checked to 10⁸ (Mian, "decanus") and then to 10¹³ (eerot, `fjordmindlabs/math/erdos647-sparse`, Oct 2026). Unverified computation reaches 10²⁰ to 10²². A cost model posted on the thread argues that no finite sieve table can settle it. This is pushing a verification bound, which the brief rules out. **Drop.** |

## 3. Near-misses (looked attackable; why not)

- **686** (is every N ≥ 2 a ratio F_k(m)/F_k(n) of products of k consecutive integers, with
  m ≥ n + k?). Non-square N works with k = 2 by a Pell equation; I re-derived this, and the thread
  had it by Mar 2026. So the problem is about squares. The thread has about 37 comments, many of them
  AI-assisted. Tao and natso26 characterise k = 2. N = 4 is excluded for k = 2, 4, 6, 8, 12 (Vjeko
  Kovač; IRAMBONA, 5 Oct 2026), and k = 3, 5 have been searched. *My own observation, which I did not
  find written out:* a representation of 4 forces m ≳ 0.72k², and the interval [m+1, m+k] then
  holds no prime and has length k ≲ 1.18√m. Ruling out N = 4 for every k would therefore follow from
  "every interval [x, x + 1.18√x] contains a prime". That is Legendre strength, and RH gives only
  `√x log x`. **RH misses by one log factor**, and Baker–Harman–Pintz (x^0.525) misses too. The
  thread already notes the "prime gap of length k + 1" constraint. Not attackable.
- **779** (Deaconescu: a prime p ∈ (p_n, P) with P + p prime, where P is the n-th primorial). Any
  prime q ∈ (P + 1, P + p_n²) makes q − P prime automatically, because q − P is coprime to P and
  < p_n². So the statement follows from a prime in (P, P + (log P)²). That is Cramér strength, far
  beyond RH. The thread cites Fortune's conjecture. Verified to n = 4600 via OEIS A005235.
- **488** (density of multiples, constant 2). Proved for |A| = 2, for min A = 2 and for special
  "tripod" families (forum, Apr–Aug 2026). Tao (Apr 2026): it stays non-trivial even with three
  simplifications at once. The general case needs a genuinely new idea.
- **700(iii)** (f(n) ≪_A n/(log n)^A). Cambie (Jul 2026) and the thread think it is "very hard",
  and GPT-5.6 could not decide either direction. (ii) was answered by GPT-5.6 Sol Pro.
- **479** (2ⁿ ≡ k (mod n) infinitely often). Open for every k ∉ {0, −1, −2, 2^i} (Tang's note,
  Dec 2025). No RH/GRH route: it needs constructions of special n, not the distribution of primes.
- **726** (EGRS: Σ_{p≤n, n mod p ∈ (p/2,p)} 1/p ~ ½ log log n for **every** n). The primes in
  (√n, n) are handled by PNT and carry total weight log 2. The weight log log n sits on p ≤ √n, where
  the claim for every n needs equidistribution of n mod p against an adversarial n. The large sieve
  bounds the bad n ≤ N only by about √N, not by zero. GRH does not help.
- **458** (lcm inequality). RH-size gaps (√p log p) can hold about log p squares, so the product of
  their roots is far larger than p_k. It needs Legendre plus control of the small primes, which the
  commentary already says.
- **828** (φ(n) | n + a). Reduced to odd a (forum, Aug 2026); there is no handle on any odd a ≠ ±1.
- **695** (prime chains). GRH (bach-sorenson-grh) gives p_{k+1} ≪ (p_k log p_k)², which is still
  doubly exponential and no better than the Linnik bound already quoted. Worthless.
- **475, 547, 551, 556, 580, 742** ("true for all sufficiently large n/p"). Each threshold comes
  from regularity, absorption or stability methods and is ineffective or tower-sized. There is no
  finite range to close.
- **506** (Elliott, n ≤ 393 open). This is a continuous geometric problem with no finite
  reformulation I could see.

## 4. Bulk discards by reason

| Reason | Count (approx.) | Examples |
|---|---|---|
| Asymptotic or extremal estimate ("estimate f(n)", constant or exponent problems) needing new combinatorics or analysis; no finite or RH handle | ~95 | 425, 500, 507, 530, 535, 539, 544, 552, 554, 555, 558, 560, 562–564, 572, 573, 576, 609, 620, 626, 627, 643, 653, 657, 709–712, 714, 773, 787–792, 796, 802, 805, 812, 813, 817, 819 |
| Ramsey or graph-structure conjectures over all graphs or trees, open in general, small cases already checked | ~35 | 545, 550, 561, 566–569, 579, 583–585, 600, 611, 612, 614, 616, 628, 640, 642, 667, 701, 713, 719, 743, 761, 766, 778, 809–811 |
| Infinite combinatorics or set theory (independence or consistency questions) | 13 | 474, 592, 593, 595–598, 601, 602, 623, 638, 736, 738–740 |
| Need Hypothesis H, prime k-tuples, Cramér or Legendre (beyond RH) | ~20 | 415, 420, 428, 431, 452, 454, 455, 458, 463, 470, 472, 647 (as a ∞ question), 676, 679, 680, 681, 683, 693, 779, 826 |
| Distribution questions not decided by Dirichlet L-functions (φ-values, divisor sums, residues of factorials, binomial divisibility) | ~20 | 416, 417, 456, 461, 478, 479, 663, 685, 686, 699, 700, 726, 727, 731, 768, 820, 821, 824, 828, 829 |
| Hofstadter or Ulam recursive sequences (no proof technique) | 4 | 422, 423, 424, 472 |
| Analysis or probability (entire functions, random polynomials, interpolation) | 12 | 509, 510, 513, 514, 517, 520–522, 524, 671, 495, 749 |
| Discrete geometry with continuous configurations | ~18 | 503, 506, 508, 588, 589, 604, 634, 654, 655, 660–662, 668–670, 704, 706, 827 |
| Design theory needing the prime-power conjecture or a big construction | 5 | 665, 723, 724, 725, 734 |
| Already solved or claimed after the harvest, or the remaining part is crowded | 617 (r = 5 done ≥ 5×), 436 (lower bounds in Lean), 647 (kernel-checked to 10¹³), 635 (answered, GPT-5.2 / Tao), 776 (He–Tang), 539 (ProofCouncil), 700(ii), 711(ii) |
| Ambiguous statements the site itself flags as possibly mistyped | 460, 467, 662, 655 |

## Bottom line

For this slice the honest answer is **zero candidates**. The pattern from the RH-restricted search
holds without the RH restriction too. Every problem in 415–829 that has a finite or short-argument
handle has been worked through by AI-assisted groups between March and November 2026, and three of
them (617, 436, 647) have Lean artifacts of exactly the kind this workspace would produce. The one
idea that is arguably mine, the reduction of 686 at N = 4 to primes in intervals of length 1.18√x,
fails by a log factor even under RH.
