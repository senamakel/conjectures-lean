# Erdős 404(ii): exploratory spike, 2026-11-24

Written by an OpenHuman agent. Nothing here is a proof.

## Summary


**Verdict: (b).** There is a plausible invariant with strong numerical support, but no proof. I put the chance that more bounded effort closes it below 5%.

**Prior work.** Nobody has resolved (ii). By far the largest effort is AstroCat93/erdos-404-research (8–22 Oct 2026, AI-written and AI-refereed, no human check), which already sets out this route and where it stops:
- the covering programme Cov/UC, and the conjecture that tails are full;
- a "barrier lemma": any covering proof must use unboundedly many p-adic digits of the factorials' unit parts;
- the p=3 obstruction (residues 68 and 77 mod 81);
- f(1,5) ≥ 10⁶;
- their own status line: Q3 open.

Nothing new on the erdosproblems thread since Kitamura (8 Jul 2026). The one repo that says "#404 solved" (kyo-oo) only proves a fact about consecutive factorials.

**My computations** (exact, independent code, each run under 45 s):
- **Earlier results reproduced.** Part 1's coverage checks (p=3: 79/81, the missing residues being 68 and 77). Kitamura's exact values (f(110,5)=30, f(236,5)=61, f(42,7)=7 and others).
- **Full tails.** Every residue mod 5^5000, 7^40000, 11^100000 and 13^200000 is a sum of distinct n! with n ≥ 2. That gives f(1,p) ≥ those exponents, much weaker than the known bounds, but it is the stronger fullness statement.
- **Gate closing.** The window needed to close a gate grows linearly in its deficit, about 2× (p=5: 6 skipped levels close in 14 digits).
- **Subset-sum density.** The normalised density of Σε_n n! stays bounded away from zero as k grows:

  | p | min density | max density | depth checked |
  |---|---|---|---|
  | 5 | 0.348 | 1.67 | k ≤ 12 |
  | 7 | 0.790 | 1.38 | k ≤ 9 |
  | 11 | 0.900 | 1.06 | k ≤ 7 |
  | 13 | 0.990 | 1.01 | k ≤ 6 |

  At p=5 the first gate cost a factor 0.88, the second only 0.997. By contrast, at p=2 82% of residues are never hit (and growing), and at p=3 38% are never hit (stable).
- **Finiteness test.** No obstruction appears for p ≥ 5. The branching model is strongly supercritical for every p ≥ 3 and critical at p=2.

**The gap.** The natural invariant is "the density stays bounded below". It alone gives E_2 = Z_p and f(1,p) = ∞. Proving it needs uniform equidistribution of many p-adic digits of n! across gates (a deep exponential-sum bound). Worst-case transfer arguments decay to 0, and the barrier lemma rules out shallow ones. Every earlier group stopped at the same step.

**Recommendation: stop.** The one cheap optional item is about a day to push the p=5 full-tail check to depth ~10⁵ with a sparser representation. That would independently confirm AstroCat's single-implementation p=5 frontier, but it would not be a proof.


### 1. Statement and equivalences (with proofs)

f(a,p) = sup v_p(Σ_{n∈T} n!) over finite T with min T = a. E_N = {Σ_{n∈B} n! : B ⊆ [N,∞)} is compact in Z_p. P(a,p,N) (Tao's predicate) means: some finite T ⊆ [a,N) with min T = a has p^{v_p(N!)} | Σ_T n!.

- **Prop 1 (compactness).** The following are equivalent: (ii) holds with a₁ = a; f(a,p) = ∞; some infinite A with min A = a has Σ_A n! = 0 in Z_p; −a! ∈ E_{a+1}.
  - *Proof.* For each K pick a witness T_K with p^K dividing its sum. Let A be a limit point of the T_K in {0,1}^ℕ. For each M, infinitely many K have T_K ∩ [0,M] = A ∩ [0,M]. So Σ_{A∩[0,M]} ≡ −(tail of T_K) ≡ 0 mod p^{min(K, v((M+1)!))}.
  - A cannot be finite: its sum would be a positive integer divisible by every power of p. So the partial sums of A have valuation at least v(a_{k+1}!) → ∞. The converse direction is trivial. ∎
- **Lemma 2 (Tao's lemma).** Let a < N and D = v((N+H)!/N!). Suppose the subset sums of x_j = (N+j)!/N! (0 ≤ j < H) cover Z/p^D. Then P(a,p,N) ⇒ P(a,p,N+H).
  - *Proof.* Take a witness sum S = p^{v(N!)}s and write N! = p^{v(N!)}u. Pick J with Σ_J x_j ≡ −s/u mod p^D. Then S + Σ_J (N+j)! ≡ 0 mod p^{v((N+H)!)}. ∎
  - Tao's normalisation N!/p^{v(N!)} differs from this one by a unit, so the two forms are equivalent.
- **Lemma 3 (non-gates).** If p ∤ N, then P(N−1) ⇒ P(N). If p ∥ N, the p−1 block elements are units, and Cauchy–Davenport covers Z/p.
- **Lemma 4 (clean blocks).** If N = c·p^E with p ∤ c+1, then v((N+p^E)!/N!) = v((p^E)!).
- **Lemma 5.** If E_N = p^{v(N!)}Z_p and P(a,p,N) holds, then f(a,p) = ∞. In particular E_2 = Z_p implies f(1,p) = ∞.
- **Lemma 6.** Let d_k(r) = p^k·Pr[Σ_{n≥2} ε_n n! ≡ r mod p^k] with fair coins ε_n. Then min_r d_k is non-increasing in k, because d_k is the average of d_{k+1} over lifts. If inf_k min_r d_k > 0, then E_2 is dense and closed, so E_2 = Z_p.
- **Lemma 7 (periodic window; why `cover.c` is exact).** If the set T_m of subset sums from levels ≥ m is full (all of p^mZ/p^D), then each lower T_k is p^m-periodic. So the computation only needs the set mod p^{m−k}, computed top-down by sumset, and it resets whenever the set becomes full.

### 2. Prior work (checked 2026-11-24)

| Date | Who / where | What |
|---|---|---|
| 1976 | Lin, Bell Labs memo | f(2,2) ≤ 254 (memo not accessible) |
| 13 Aug 2025 | Kovač, forum | Statement corrected to the current form |
| 29 Sep 2025 | Tao, [forum thread](https://www.erdosproblems.com/forum/thread/404) | Lifting lemma; "f(1,5) possibly even infinite"; the N=0 case is key |
| 7–8 Jul 2026 | Kitamura, [p2](https://github.com/KitaKen1/erdos-404-p2-landscape) / [odd-prime](https://github.com/KitaKen1/erdos-404-odd-prime-landscape) repos | f(2,2) = 254 (Lean-checked both ways); f(a,2) for a ≤ 256; f(1,p) ≥ 20000 for p=3,5,7; no claim of infinitude |
| 25 Aug 2026 | [jig.so #159](https://jig.so/p/159) | Lean statement only; its listed routes were not closed |
| 8 Oct 2026 | formal-conjectures PR #6936 | Formalises the statement; still open |
| 8–22 Oct 2026 | [AstroCat93/erdos-404-research](https://github.com/AstroCat93/erdos-404-research) | The main effort (details below); Q3 open |
| 14 Oct 2026 | [erdosproblems.ai wiki](https://erdosproblems.ai/wiki/problems/factorials_binomials/E0404) | "No claim settles this problem" |
| Nov 2026 | kyo-oo/erdos-weak-problems | "Solved" claim covers consecutive factorials only; irrelevant |

AstroCat93's results:
- the normal form f = v_p(a!) + g_p(a);
- K_p = {g_p = ∞} is closed, nowhere dense and uncountable;
- μ(K_2) = 0;
- the barrier lemma;
- the p=3 residues 68 and 77;
- the Cov/UC framework: UC(p) ⇒ f(1,p) = ∞;
- negative results: fullness of carry fibres never suffices, supremum-type transfer has constant ≥ 1, and the plain Fourier L¹ criterion fails at p=5;
- lower bounds f(1,5) ≥ 10⁶, f(1,13) ≥ 883,708,272 and f(1,19) ≥ 1.79·10¹⁰;
- Conjecture 5.5 (E_p = pZ_p for p ≥ 5), with a p=5 tail frontier of 5^117499 from a single implementation.

Also: Roy's ResearchGate preprint (4 Oct 2026) could not be read, and searches found no posts from Sky-Yang. Nothing on the forum after 8 Jul 2026.

### 3. Computations

**3.1 Validation and reproduction**
- `cover.c` matches the dense brute force in `brute_check.py` on 17 cases.
- Clean blocks at N=0 (all subset sums of {i! : i < p^E} mod p^{v((p^E)!)}):

  | p | E=1 | E=2 | E=3 | E=4 |
  |---|---|---|---|---|
  | 2 | — | 7/8 | 92/128 | — |
  | 3 | full | 79/81 (missing 68, 77) | 97.5% | — |
  | 5 | full | full | full | full |
  | 7 | full | full | full | — |
  | 11, 13 | full | full | — | — |

- `fwd.c` reproduces f(3,3)=3, f(39,3)=25, f(110,5)=30, f(236,5)=61, f(42,7)=7, f(4,7)=0, f(6,7)=0, f(113,11)=11, f(163,13)=13, f(4,2)=6, f(3,2)=1, f(5,2)=3.

**3.2 Full tails from n=2.** Every residue mod p^D is a sum of distinct n! with n ≥ 2:

| p | D | largest window (digits) | time |
|---|---|---|---|
| 5 | 5000 | 14 | 42 s |
| 7 | 40000 | 10 | 1 s |
| 11 | 100000 | 7 | 7 s |
| 13 | 200000 | 7 | 1 s |

The p=5 run stopped at D=5000 because the 14-digit window hit the memory cap.

**3.3 Excursion width vs empty levels s** (max/mean, from `results/excursion_summary.txt`):

| s | p=5 | p=7 | p=11 | p=13 |
|---|---|---|---|---|
| 1 | 3 | 2 | 2 | 2 |
| 2 | 6 / 5.4 | 5 / 4.5 | 4 | 4 |
| 3 | 8 | 7 | 5 | 5 |
| 4 | — | 8 | 7 | 7 |
| 5 | 12 | 10 | — | — |
| 6 | 14 | — | — | — |

The width is linear in s, about 2.3s at p=5, 2s at p=7 and 1.75s at p=11, 13. The counting prediction is 1.4–1.9s.

**3.4 Clean blocks [c·p^E, (c+1)p^E) at many positions.**
- They cover at every tested position for: p=5 with E ≤ 4 (c up to 2000; at E=2 that is every class mod 5^4); p=7 with E ≤ 3; p=11 and 13 with E=2.
- At p=3 they fail at every c ≡ 0 mod 9 (E=2: 555/667 covered; E=3: 65/200).
- Extra digits covered beyond the demand, at N=0:

  | p | E=1 | E=2 | E=3 |
  |---|---|---|---|
  | 5 | 0 | 2 | ≥2 |
  | 7 | 0 | ≥4 | ≥3 |
  | 11 | 1 | ≥4 | — |
  | 13 | 1 | ≥4 | — |

  "≥" means the next step hit the window cap, not that it failed.

**3.5 Density d_k of Σ_{n≥2} ε_n n!:**

| p | min d_k | max d_k | zero residues |
|---|---|---|---|
| 2 | 0 | — | 82%, rising |
| 3 | 0 | — | 38.3%, stable; d(−1) = 2.70 |
| 5 | 0.348 | 1.669 | 0 |
| 7 | 0.790 | 1.382 | 0 |
| 11 | 0.900 | 1.057 | 0 |
| 13 | 0.990 | 1.010 | 0 |

At p=5, the gate at 25 cut the minimum by a factor 0.88 and the gate at 50 by only 0.997.

**3.6 Branching.** The quenched log-offspring per block is p·ln2 − (p/(p−1))·ln p: 0 at p=2, and 0.43, 1.45, 2.58, 4.87, 6.23 nats at p = 3, 5, 7, 11, 13. Observed carry growth matches about 2^p/p per block. This is a heuristic only.

### 4. Invariants tested
- **Clean-block coverage at all positions, plus the single points p^t.** P(1,p,p^t) for every t together with clean-block coverage implies f(1,p) = ∞, by strong induction on N = K''·p^t. Both families are infinite, so this is a reduction. It is a special case of AstroCat's UC framework.
- **Surplus digits.** Present, but surplus in lower sub-blocks provably cannot carry the extra top digit alone (AstroCat Thm 10.12 / Cor 10.13).
- **Linear gate-closing (ML_p).** Holds in all data.
- **Density bounded below.** The best candidate; supported for p ≥ 5 and false for p = 2, 3.

### 5. The gap
- **Worst-case transfer decays to zero.** F(N) ≥ (min block density)·F(N+H), and the factor is below 1, so iterating gives 0. The true minimum survives only because the low points of successive blocks don't line up.
- **Barrier lemma.** A uniform proof must control the unit-part digits beyond the gate congruence (the Morita Γ_p and harmonic-number terms).
- **What is missing.** Equivalently, a deep-shell bound on Σ_ξ Π_n |cos(π ξ n!)|. The random model predicts a ratio of 0.52 per shell at p=5, but no tool proves it.

I attempted no full proof. No candidate invariant reduced to a finite, position-independent check, and writing one out would have hidden one of these gaps.

### 6. Verdict and next step
**(b).** f(1,5) = ∞ is very likely true as a heuristic (about 90%). A proof within reach here is under 5%. Recommendation: stop.

Optional follow-ups, neither of which yields a theorem:
- about 1 day: a sparse window to push the E_2 = Z_5 check to D ≈ 10⁵, independently confirming AstroCat's p=5 frontier;
- 2–3 days: measure whether the density losses at gates are summable for p = 7, 13.

Files are in `docs/scoping/erdos-404/` (binaries removed; compile commands are in the README):
- README.md
- cover.c
- fwd.c
- count.c
- brute_check.py
- results/
