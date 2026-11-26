# Wave 3 lane `w3-arithmetic-functions` (2026-11-26)

**Status: paused, incomplete** (owner's instruction, mid-run). Research only. Nothing here was built in Lean.
Scripts (C and Python, run with `-I`) are in the session scratchpad under `w3af/scripts/`. They are not durable.

Ground: open inequalities and "for all n > N₀" statements about σ, φ, ψ, d, ω, Ω, primorials, SA/CA/HC
numbers, harmonic numbers, lcm(1..n), Chebyshev functions.

## Class A: no proof found anywhere

Three of the four are **counterexamples or disproofs** of OEIS conjectures. Easiest first.

### A1. OEIS A057635 (Jianing Song, 2019): "Conjecturally a(n) < n·f(n) for all n > 2" is FALSE
- Source (OEIS A057635, comment of Feb 16 2019): a(n) is the largest m with φ(m) = n, and
  f(n) = e^γ log log n + 2.5/log log n. Song proves a(n) < n·f(n²) and writes "Conjecturally
  a(n) < n*f(n) for all n > 2."
- **Counterexample n = 48.** Here a(48) = 210 (OEIS data) and 48·f(48) = 204.4 < 210.
- Exhaustive search over m ≤ 3·10⁸ (C sieve of φ, test m ≥ φ(m)·f(φ(m))) finds 30 pairs. The
  values of n are 48, 96, 480, 576, 960, 1440, 5760, …, 36495360 (m = 223092870 = N₉, the
  Rosser–Schoenfeld exception), and the largest is 46448640 (m = 281291010). At primorials,
  N_k/φ(N_k) − f(φ(N_k)) > 0 for k = 4…15 and < 0 for 16 ≤ k ≤ 60.
- Why it fails: f is Rosser–Schoenfeld's bound for m/φ(m) in terms of m. Replacing m by
  φ(m) < m lowers f enough to break it near primorials.
- Lean: decide φ(210) = 48, plus interval bounds for e^γ and log log 48. Effort S, tier D.
- A natural corrected theorem ("only finitely many exceptions", via RS 1962 (3.30)/(3.16) and
  primorials with k ≥ 16) is our own formulation. It is not an open statement.
- Novelty (2026-11-26): the OEIS page as fetched today shows no correction. Searched exa
  (A057635 conjecture), formal-conjectures clone `9097e2f` (no file), fc PRs (`57635`: none),
  1337 clone and openai/math clone (no hit). GitHub code search was rate-limited.

### A2. OEIS A337993 (Peter Luschny, 2020): "Conjecture: This sequence is finite" is FALSE
- Statement: the numbers k with floor(H_k + e^{H_k} log H_k) < σ(k) + k/π². The data are
  1, 2, 4, 6, 12, 24, 60, 120, 360, 2520, 5040.
- Brute force over n ≤ 10⁷ (C, long double) finds exactly the 11 listed terms.
- Terms beyond the data, computed with Decimal at 45 digits and exact exponents:
  - every colossally abundant number from the 71st on. The 71st has largest prime 229, log N =
    239.07 (≈ 10^103.8), and margin/N = 0.10113 < 1/π² = 0.10132. Checked through 18,160 CA
    numbers (log N ≤ 2·10⁵).
  - lcm(1..x) for every prime power x with 512 ≤ x ≤ 3·10⁶. The first such x is 361.
- **Proof of infinitude.** Take n = lcm(1..x) and let N_k be the primorial of the largest prime
  ≤ x.
  1. σ(n)/n ≥ (N_k/φ(N_k))·(1 − 2/√x), since every p^{a_p+1} > x.
  2. Nicolas' inequality (the nicolas-rh theorem, every k) gives N_k/φ(N_k) > e^γ log θ(x).
  3. Elementary bounds: log n = ψ(x) ≤ θ(x) + 3√x, and H_n ≤ log(n+1) + γ (Mathlib's
     `eulerMascheroniSeq` monotonicity).
  4. Together these give margin/n ≤ e^γ log(ψ/θ) + O(log x/√x) → 0, so margin/n < 1/π² for
     every large x.
- No finite check is needed, because infinitely many terms suffice. Unconditionally, it also
  follows from Solé–Zhu (Integers 16 (2016) A81) Thm 1, liminf d(n) = 0.
- Effort S–M, tier U via nicolas-rh. The catch: the bound has to be made explicit enough to
  name an x₀ (about 10⁶ by the constants above).
- Novelty: the OEIS page today still says "Conjecture: finite". Searched exa (A337993 +
  Lagarias + finite), fc clone and PRs (`337993`: none), 1337 and openai clones (no real hit),
  MathOverflow (the Lagarias question 373987 does not touch it).

### A3. OEIS A279609 (Gene Ward Smith, 2016): the "stronger conjecture" that F(n)/2ⁿ increases is FALSE
- Statement: F(n) = floor(H_k + e^{H_k} log H_k) − σ(k), with k = A004490(n) (CA numbers). The
  comment: "by inspection it appears to be monotone increasing … F(n)/2^n also appears to be
  monotone increasing."
- My exact values for n ≤ 13 equal the OEIS data. From n = 14 on, the OEIS data are off by
  small amounts (low precision); e.g. a(14): OEIS 81053635, exact 81053642.
- **Counterexample at n = 24 → 25.**
  - CA₂₄ = 395622702669701707200, F = 70751447496390094448.
  - CA₂₅ = 2·CA₂₄ = 791245405339403414400, F = 140784258857100994253.
  - The ratio is 1.98984 < 2.
  - The same failure recurs at n = 36, 51 and 77 (all steps ×2). The OEIS data stop at n = 23.
- The main conjecture (F increasing) holds:
  - exactly for n ≤ 112 (CA numbers up to 10²⁰⁰, Decimal at 300 digits);
  - in floating point for 18,160 CA numbers; the minimal log-ratio is 0.687 (×2 steps).
- Lean for the disproof: exact σ, plus H_N bounds at N ≈ 8·10²⁰ (log interval arithmetic, γ
  upper and lower bounds). Effort S–M, tier D.
- **The monotonicity conjecture itself is class A but L.** It needs two-sided Ramanujan-type
  bounds for D(N)/N·√log N on CA numbers with explicit thresholds, which robin-rh's margin
  (about 0.48 against the true 1.39) does not give. Also note "not in any obvious way implied
  by RH".
- Novelty: exa search (A279609 / CA Lagarias monotone) found nothing beyond the OEIS page.
  Also searched the fc clone and PRs and the 1337 and openai clones.

### A4. Wu / Leshchiner–Musin–Thompson, arXiv:2610.39120 (Oct 2026), Question 1: open, not closable
- The question: "If N_i is CA3 and the next CA number is N_{i+1} = 2N_i, must
  G(N_{i+1}) > G(N_i) hold?" (unconditional; Wu settled p ≥ 3).
- Numerics: 22,236 CA numbers (log N ≤ 2.5·10⁵), 19 steps by 2, 14 of them from CA3, no failure.
- Analysis: G(2N) > G(N) ⇔ 1 + 1/(2^{a+2}−2) > log(L + log 2)/log L, with L = log N. It can
  fail only if L − x(ε*) < about 1/2. That needs log N within about 1/2 of the next prime, and
  RH does not exclude it. Heuristically there are finitely many failures, but no proof route
  was found. Recorded, not proposed.

## Class B: the conditional result is published and unconditional now via the RH proof (not in our Lean)
- **Solé–Zhu's open problem** (Integers 16 (2016) A81, §5): "extend lim D(n) = ∞, D(n) = e^γ n
  log log n − σ(n), to integers that are not CA".
  - My first reading was class A. The deduction runs through robin-rh's margin: gain − tail >
    0 gives D(n) ≥ c·n/√log n for log n ≥ e³⁰.
  - It is **published**: Nicolas 2022 [cited as Nic22 Cor. 1.2 in Mishra–Sarkar arXiv:2609.26787,
    Lemma 23], under RH, σ(n)/n < e^γ(log log n − 0.095/√log n) for all n > 5040. Hence D(n) ≥
    0.095 e^γ n/√log n → ∞.
  - The Lean version is S–M: re-prove `main_estimate` keeping the slack.
- **OEIS A279291** (Shevelev 2016): "we conjecture a(n) ≤ 4 independent of RH". It follows from
  Nicolas 2012 (Acta Arith. 155), RH ⇔ c(n) ≤ c(N₆₆) = 4.0628 for n ≥ 2. Lean is L: Nicolas
  2012 is not in nicolas-rh.
- Published RH-equivalences, theorems now, not in our Lean:
  - Washington–Yang (arXiv:2008.04787): odd-n Robin and Lagarias analogues;
  - Caveney–Nicolas–Sondow: no GA2 number > 5040;
  - Massias–Nicolas–Robin: Landau's g(n);
  - Mishra–Sarkar 2026: ω-truncated Robin;
  - Musin 2026: higher-order CA classes;
  - Kalyabin's U₁/CNSH.
- Already covered in Lean elsewhere:
  - the extraordinary-number and extremely-abundant equivalences (abundant-rh);
  - kimihiro64/Robin1984, an independent Lean Robin/Lagarias formalisation, plus a cyclotomic
    "CorrectedIdealRobin", per the Sutherland verification page.

## Class C: already proved or posted (rejected)
- **A008578, Gerasimova's conjecture** (σ(k) > kΩ(k) ⇔ k = 1 or prime). I had a 5-line proof
  and checked it to 10⁷. It is already proved: formal-conjectures `OeisA8578.conjecture`,
  `formal_proof` at otoi-lab/oeis-lean-proofs (fc PR #7195, merged 2026-10-12).
- **A064377** (σ₄(n) > φ(n)⁵ is finite): proved in OEIS (Greathouse 2015). **A051250** (60 is
  the largest term): proved in OEIS.
- Aoudjit–Berkane–Dusart Question 1: answered by Axler, arXiv:2406.04018 (Cor. 1.6,
  unconditional for n > 1680).
- A003418, the lcm form of Schoenfeld: posted in OEIS by A. Ramadhan, 2026-10-06 (a sign that
  OEIS corollaries of RH are being posted now).
- A002110, "each primorial is a new minimum of φσ/n²": immediate from Wilson's comment in the
  same entry.
- A196200: Sándor's φ(ψ(n)) ≤ n is already refuted.
- A342000, "G decreases along primorials" (⇔ θ(p_n) < p_{n+1} − (log p)²/2 roughly): probably
  false beyond Skewes-type heights by Littlewood, and not decidable with our tools. Recorded.
- A176679, "every SA number > 665280 is a right-record of the Lagarias margin": class A but L
  (needs sharp two-sided CA constants). Not checked numerically, so not a candidate.
- Dimitrov arXiv:2606.12484, Conj. 1–9, and Dimitrov–Lazarova (Mathematics 2026), 4 conjectures:
  elementary φ, ψ, σ power inequalities with equality at primes. They are open but were **not
  checked numerically** (paused), so they are not candidates yet.

## What was searched (2026-11-26)
- OEIS JSON API: the entries A000203, A000010, A001615, A002110, A004394, A004490, A002182,
  A003418, A014963 and neighbours, and 20 keyword searches (239 entries).
- arXiv full text:
  - 1211.2147 (Nazardonyavi–Yakubovich), 1602.03384 (Solé–Zhu), 2406.04018 (Axler),
    math/0604314 (CLMS);
  - 1012.0671, 1010.3239, 1110.5078, 1112.6010 (CNS), 1810.12585 and 2603.24548 (Kalyabin);
  - 2610.39120, 2609.26787, 2609.33794.
- Exa: 9 queries (Robin and Lagarias conjectures, CNS, Solé–Zhu citations, Sándor and
  Dimitrov, 2026 RH-corollary notes, Zenodo).
- formal-conjectures clone `9097e2f`: grep of all open declarations on σ, φ, ω, Ω, primorials,
  and `Paper/RiemannHypothesisEquivalents.lean`, `Wikipedia/ColossallyAbundantNumber.lean`. fc
  PR search for 8578, 337993, 279609, 57635, Robin, colossally, Lagarias.
- 1337 and openai/math clones: grep.

## Not reached
- GitHub code search: rate-limited after the first query.
- Broughan's *Equivalents of RH* vol. 1, Sándor–Mitrinović handbook, Guy UPINT B: not read.
- Nicolas 2022 itself: only quoted second-hand.
- Briggs 2006 full text.
- Numerics for the Dimitrov conjectures and A176679.
- The smallest A337993 term above 5040, which is not necessarily CA or lcm.
- LivingBrain: not queried.
