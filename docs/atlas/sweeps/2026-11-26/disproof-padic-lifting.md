# Lane `disproof-padic-lifting`: p-adic valuation conjectures, refuted by lifting

Lane `disproof-padic-lifting`, 2026-11-26. Research and computation only. No Lean file and no
existing file was edited. The scripts are copied to
`disproof-scripts/padic-lifting/`; the runs were made in the session scratchpad
(`hunt-padic/src/`). The model was the 1337 refutation of Gawron–Miska–Ulas Conjecture 5.2
(`results/gawron-miska-ulas-thue-morse-valuation/PROOF.md`, read as data): a valuation formula
fitted on small data, one anomaly found by a fast modular evaluator, then lifted by a
Frobenius/Kummer-type congruence to an infinite family. Ulas-school binary-partition and
Thue–Morse statements were left alone. Claims not confirmed from a primary source are marked
*(unverified)*.

## Main finding

**Hong–Qiu's conjectured formula for `v_p(s(ap^n, ap^n − k))` is false at every irregular
prime tested (all 8 irregular primes below 160).** The error is not bounded: at `p = 37` it grows
without limit along a family of indices that are lifted level by level from Kummer's
congruences.

- **What the conjecture says.** S. Hong and M. Qiu, *On the p-adic properties of Stirling
  numbers of the first kind*, Acta Math. Hungar. 161 (2020) 366–395, arXiv:1908.05594 v2,
  §5. Write `s(n,k)` for the unsigned Stirling number of the first kind. Conjecture 5.2 is the
  `m = n` case of Conjecture 5.1(i). Conjecture 5.3 is a third, comparison formula.
- **Why the tests never saw the failure.** The conjecture's Bernoulli term, `T_k = v_p(B_{2⌊⟨k⟩/2⌋})`,
  matters only at irregular primes, and every check so far was at regular primes. The term
  reads the irregularity off the residue `⟨k⟩ = k mod (p−1)` alone. The true valuation also sees
  the higher Kummer level: whether `p^j | B_k/k`, which depends on `k` modulo `(p−1)p^{j−1}`.
- **Status in the literature.** The conjecture is open and believed.
  - Qiu–Lin–Chen proved the case `p = 3`: arXiv:2109.13458 v2 (17 May 2026), published in
    AIMS Math. 11(8) (2026) 25553–25600.
  - That paper says the case `p ≥ 5` "would require additional congruence information and a
    substantially finer decomposition".
  - Hong–Qiu's own Theorem 1.1(ii) proves only `≥` at irregular primes, and only for `n = 1`.
- **Nature of the hit.** The ingredient is classical: Zhao (IJNT 2008, Remark 2.6) saw the same
  `B_284` effect in harmonic sums at `p = 37`. The hit is therefore real but not deep. The new
  part is the unbounded family.

### The statement as published (arXiv:1908.05594 v2, §5, copied from the LaTeX)

> **Conjecture 5.2.** Let `p` be an odd prime. Let `a, n, k` be positive integers such that
> `1 ≤ a ≤ p−1` and `2 ≤ k ≤ a(p−1)p^{n−1}+1`. Then
> `v_p(s(ap^n, ap^n−k)) = n + (n+v_p(k))ε_k − 1 − v_p(⌊k/2⌋)` if `k ≡ ε_k (mod p−1)`, and
> `= n + (n+v_p(k))ε_k + v_p(B_{2⌊⟨k⟩/2⌋})` if `k ≢ ε_k (mod p−1)`.
> Here `ε_k = k mod 2` and `0 ≤ ⟨k⟩ ≤ p−2`, `k ≡ ⟨k⟩ (mod p−1)`.

Conjecture 5.1(i) generalises this to `v_p(s(ap^n, ap^m − k))` for `1 ≤ m ≤ n`. Its right-hand
side is `(a/(p−1))(p^n−p^m) − (n−m)(ap^m−k) + m + (m+v_p(k))ε_k + T_k`, with the same `T_k`.

### Witnesses

`p = 37` is irregular, with `37 | B_32`. So for `k ≡ 32, 33 (mod 36)` the conjecture puts
`T_k = 1`.

| # | Statement | Witness | Value | Conjectured |
|---|---|---|---|---|
| W1 | 5.2, `n = 2`, `a = 1` | `v_37(s(1369, 1085))` (`k = 284`) | **4** | 3 |
| W1′ | 5.2, `n = 2`, `a = 1` | `v_37(s(1369, 1084))` (`k = 285`) | **6** | 5 |
| W2 | 5.2, `n = 1`, `a = 23` | `v_37(s(851, 819))` (`k = 32`) | **3** | 2 |
| W3 | 5.1(i), `n = 2`, `m = 1`, `a = 23` | `v_37(s(31487, 819))` (`k = 32`) | **35** | 34 |
| W4 | 5.3, same parameters as W3 | left side 35 | **35** | right side `0 + 3 + 31 = 34` |

- **The integers.** `s(1369, 1085)` has 1103 decimal digits and `s(851, 819)` has 143.
- **Why W1 sits where it does.** `k = 284` is the level-2 Kummer index of the irregular pair
  `(37, 32)`: `v_37(B_284/284) = 2` (FLINT's exact `B_284`, and an independent power-sum
  congruence).
- **The `n = 1` failures.** At `n = 1` the failing `k` move with `a`. Every `a ≥ 16` has exactly
  one failing pair `k, k+1`, with `k ≡ 32 + 18(a − 23) (mod 666)`.
- **They are not covered by the theorem.** Theorem 1.1(ii) of the paper gives only `≥` there, so
  W2 contradicts nothing proved. It is the `n = 1` case of the conjecture that is false.

### The lifted family: the error is unbounded

Let `k_j` be the level-`j` Kummer index of `(37, 32)`. That is the unique `k ≡ 32 (mod 36)`
below `36·37^{j−1}` with `37^j | B_k/k`. The `λ`-invariant is 1, so `k_j` exists for every `j`,
and `k_{j+1} ≡ k_j (mod 36·37^{j−1})`.

| `j` | `k_j` | How `k_j` was computed |
|---|---|---|
| 2 | 284 | FLINT exact `B_k` |
| 3 | 37580 | FLINT exact `B_k` |
| 4 | 1072544 | power-sum congruence `B_k ≡ p^{−J} Σ_{i<p^J, p∤i} i^k (mod p^{2J−1})` |
| 5 | 55777784 | same congruence |

The witnesses are `N = 37^n` with `k = k_j`. Column `n = j` is the diagonal family, where the
excess over the conjecture is `j − 1`:

| `n` | `N = 37^n` | `k = 284` | `k = 37580` | `k = 1072544` | conjectured (all `k`) |
|---|---|---|---|---|---|
| 2 | 1369 | 4 | — | — | 3 |
| 3 | 50653 | 5 | **6** | — | 4 |
| 4 | 1874161 | 6 | 7 | **8** | 5 |
| 5 | 69343957 | 7 (C DP only, `k ≤ 300`) | 6 (C DP) | not computed | 6 |

The `n = 5` FLINT product tree (for `k_5 = 55777784`) was stopped unfinished at wind-down, so
the `n = 5` row has one implementation only, and the diagonal is verified for `j ≤ 4`.

- **Two infinite families.**
  - At fixed `k = 284`, the table gives `v_37(s(37^n, 37^n − 284)) = n + 2` for
    `n = 2, 3, 4, 5`, against the conjectured `n + 1`.
  - On the diagonal, `v_37(s(37^j, 37^j − k_j)) = 2j` for `j = 2, 3, 4`, against `j + 1`. The
    excess `j − 1` is unbounded if the pattern continues.
- **The odd companions** `k_j + 1` behave the same way. This is forced by the paper's own
  Theorem 1.3, which is proved.
- **A corrected formula that fits the data.** Replace `v_p(B_{2⌊⟨k⟩/2⌋})` by
  `v_p(B_{k_e}/k_e)`, with `k_e = 2⌊k/2⌋`. This matches every value computed for `p = 37`,
  `a = 1`, `n = 2, 3, 4`: 1332, 49284 and 1823508 values of `k`, with no exception. It is a
  conjecture, not a theorem.
  - It does not cover `a > 1` at `n = 1` (W2).
  - It does not cover `p = 67`, where the irregular index is 58 = `p − 9`. There `v = 5` at
    `k = 3292`, `n = 2`, with `v_67(B_3292/3292) = 2`. This is excess 2, and the corrected
    formula does not explain it.
- **No proof that the family continues.** It is verified for each `n` in the table. A proof
  would need a Kummer-type expansion of `e_k(1, …, p^n − 1)` to second order. Lengyel's
  Theorem 1.4 (quoted in the paper) does not apply: its hypothesis `v < n_1` fails, because the
  valuation here is `n + 2`.

### Other irregular primes (`a = 1`, `n = 2`, smallest witness)

| `p` | irregular index | `k` | `v_p(s(p², p²−k))` | conjectured | `v_p(B_k/k)` |
|---|---|---|---|---|---|
| 59 | 44 | 914 | 4 | 3 | 2 |
| 67 | 58 | 3292 | 5 | 3 | 2 |
| 101 | 68 | 5768 | 4 | 3 | 2 |
| 103 | 24 | 228 | 4 | 3 | 2 |
| 131 | 22 | 12112 | 4 | 3 | 2 |
| 149 | 130 | 11082 | 4 | 3 | 2 |
| 157 | 62, 110 | 11498 (and one more pair) | 4 | 3 | 2 |

At `n = 1` (all `a`), the mismatch counts are 58, 66, 100, 102, 130, 148 and 312 for
`p = 59, 67, 101, 103, 131, 149, 157`. Every regular prime checked agrees with the conjecture:
`p = 5` (`a ≤ 4`, `n ≤ 3`), `p = 7` (`a ∈ {1, 3, 6}`, `n ≤ 2`), and the 8568 cases with
`p ≤ 13` checked by the literature sub-agent.

### Verification (twice, independently)

1. **Row DP in C** (`hq.c`).
   - Method: `s(N, N−k) = e_k(1, …, N−1)`, computed modulo `p^E` with `E = 12` for `p = 37`
     (`37^12 < 2^63`), using 128-bit products.
   - Validation: the regular primes 5 and 7 above, with no mismatch.
   - Runs: `n = 2, 3` with all `k`; `n = 4, 5` with `k ≤ 300`.
2. **FLINT product tree** (`hq_flint.py`, `hq_flint_all.py`, `hq_nmod.py`).
   - Method: `∏_{i<N}(1 + i·y)` over `Z/37^12`, truncated at degree `K`, built two ways
     (`fmpz_mod_poly` and `nmod_poly`).
   - Agreement: the full `n = 3` table (49284 values) is **identical** to the C output. Every
     `n = 4` value quoted agrees between the two FLINT routes.
3. **Exact big integers** (`exact_newton.py`).
   - Method: Newton's identities from exact power sums, a third algorithm. It checks W1, W1′ and
     W2 exactly, and `k = 284, 285` at `n = 3` (`s(50653, 50369)` has 2012 digits; `v = 5`).
   - W3 was also checked by a separate pure-Python column DP modulo `37^45` (`hq_m.py`), as
     well as by FLINT (`hq53.py`).
4. **Precision.**
   - All quoted values are below the working precision (12, or 45 for W3).
   - The one capped value is `k = 1072545` at `n = 4`, where `v ≥ 12` (conjectured 9). It is not
     used as a witness.
5. **Conventions re-read.**
   - The paper's `s(n,k)` is unsigned (`(x)_n = x(x+1)⋯(x+n−1) = Σ s(n,k)x^k`), so the sign is
     irrelevant to valuations anyway.
   - The hypotheses `1 ≤ a ≤ p−1` and `2 ≤ k ≤ a(p−1)p^{n−1}+1` hold in every witness. For W1:
     `284 ≤ 36·37 + 1 = 1333`.

### Prior art (checked 12:29 and 12:55 UTC, 2026-11-26)

- **Searched:** Exa web search on the conjecture's wording, "Hong Qiu" with "irregular",
  counterexample and Stirling; arXiv, AIMS and journal pages; GitHub code search for `1908.05594`
  (one hit, an Epoch run listing the id as a reference, nothing about this); GitHub issue
  search; the 1337 `results/` list (170 entries, none on Stirling numbers of the first kind).
- **Papers citing the conjecture:** Qiu–Lin–Chen (p = 3), Barman–Narode–Wagh (Acta Arith.
  2026; uses Theorem 1.1 only), Qiu–Hong (p = 2).
- **Result:** no refutation found and no mention of irregular primes as a problem. The closest
  prior observation is Zhao's remark on `H(1048; 36)`, which is a different statement.
- **Competition:** an AI-assisted author on Zenodo/aiXiv (R. Blanco Gómez, per the literature
  sub-agent, *(unverified)*) is working through Sun's lists, not this paper.

### How Lean could check it

- **Definition.** Mathlib has `Nat.stirlingFirst`
  (`Mathlib/Combinatorics/Enumerative/Stirling.lean`), unsigned, with
  `stirlingFirst (n+1) (k+1) = n * stirlingFirst n (k+1) + stirlingFirst n k`.
- **Checker.** Define `rowMod M n : Array ℕ`, the `n`-th row modulo `M`. Prove by induction on
  `n`, using `stirlingFirst_succ_succ`, that `(rowMod M n)[k] = stirlingFirst n k % M`.
- **Witness.** With `native_decide`, check `stirlingFirst 1369 1085 % 37^4 = 0` and
  `stirlingFirst 1369 1085 % 37^5 ≠ 0`. That is 1369 rows of length at most 1370.
- **Refutation.**
  - State the conjecture literally, with `padicValNat` and `bernoulli`, and specialise it at
    `p = 37`, `a = 1`, `n = 2`, `k = 284`.
  - The right-hand side needs `padicValRat 37 (bernoulli 32) = 1`. Mathlib's `bernoulli 32`
    is a rational; `decide` on its numerator is feasible, or `native_decide` with
    `bernoulli'_def` unfolded.
- **Cost.** Effort S–M. W2 (`s(851, 819)`) is cheaper still.

## One-line results (shallow: they fail at the first level)

- **Amdeberhan–Moll, *Involutions and their progenies*, J. Comb. 6 (2015), arXiv:1406.2356, §4
  Conjecture.** It says the involution-number tree `T_p` has a single non-terminal vertex at every
  level, for every inefficient prime.
  - It is false at level 1 for `p = 59`. Both `I_1(24)` and `I_1(41)` are divisible by 59, and
    each class has non-constant valuation (`{1, 2}` on `24 + 59t` and `41 + 59t`, `t < 150`;
    rechecked here from `I(n) = I(n−1) + (n−1)I(n−2)` modulo `59^8`).
  - The sub-agent lists 13 inefficient primes below 400 that fail.
  - Shallow (first level), so one line.
- **Caicedo–Moll–Ramírez–Villamizar, *Extensions of set partitions and permutations*, EJC 26(2)
  (2019) P2.20, Conjecture 64 (Fubini numbers).** It says "at each step there is a single class
  where the valuation is not constant … for every prime `p > 5`".
  - It is false at level 1 for `p = 13`. `F_n mod 13` has period 12, and the classes `n ≡ 0`
    and `n ≡ 3 (mod 12)` both have valuations `{1, 2, 3}` (n < 1200, modulo `13^5`).
  - Primes with two or more zero classes below 200: 13, 23, 31, 37, 41, 47, 59, 61, 73, 83, 101,
    and others.
  - Shallow. The deeper question, whether a single root class can split as in Flórez–Higuita–Ramírez's
    `p = 971` answer to Givens–Moll (arXiv:2610.37356), was not run.

## Targets examined

| Target | Statement | Range covered | Result | Cost |
|---|---|---|---|---|
| Hong–Qiu Conj. 5.1(i), 5.2, 5.3 | above | regular `p = 5, 7`; irregular `p ≤ 157` (`n = 1`, all `a`; `n = 2`, `a = 1`); `p = 37`: `n ≤ 4` all `k`, `n = 5` for `k ≤ 300`, `n = 2` for `a ∈ {1,2,3,5,10,16,23,36}` | **refuted**, unbounded family | ≈ 1 CPU-h (the `n = 5` FLINT tree was stopped unfinished) |
| Adelberg–Lengyel, arXiv:2111.08766, Conjecture `con:a+2` | `ν₂(S(c2^h+2, b2^h+a)) = σ₂(a) + f(b,c) + ν₂(C(a+1,2)) − 1` for `a ≡ 3 (mod 4)`, `3 ≤ a ≤ 2^{h−1}` | `S(n,k) mod 2^64` by row recurrence: `h ≤ 16` with `c ≤ 8`, and `h ≤ 12` with `c ≤ 40`; about 1.3·10⁶ cases | holds wherever the companion theorem's hypothesis `2^{h−2} ≥ ν₂(C(2c−b−1, c))` holds. 35 failures, all outside that hypothesis (e.g. `h = 4`, `c = 33`, `b = 1`, `a = 7`), so they are not counted | 20 CPU-s |
| Amdeberhan–Manna–Moll, Bennett–Mosteig, Lengyel 2009, Hong–Zhao–Zhao | Stirling second kind | — | proved (Miska; Zhao–Hong–Zhao), not run | — |
| Amdeberhan–Moll involution tree | above | `p = 59`, levels 1–2 | refuted at level 1 (shallow) | seconds |
| CMRV Fubini Conj. 64 | above | `p < 200`, level 1 | refuted at level 1 (shallow) | seconds |
| Sun, Conj. 64(iii) (3-adic Apéry sums), 2019 list | `ν₃(Σ(2k+1)(−1)^k A_k) = 3ν₃(n)` and the companion | `n ≤ 1500` (sub-agent) | holds | small |
| Saikia–Sarma–Sellers 8.1, Tang 5.1–5.2, Du–Tang 11–14 | partition congruences | sub-agent spot checks only (Tang 5.2 for `p ≤ 113`) | hold where checked; not pursued | small |

## Best unfinished lead

1. **Proving the family.** The open step is to show `v_37(s(37^n, 37^n − 284)) = n + 2` for all
   `n ≥ 2`, and the diagonal `2j` law at `k_j`. That would turn a finite refutation into an
   infinite family whose error is proved unbounded.
   - Route: expand `e_k(1, …, p^n−1)` through power sums `Σ_{i<p^n} i^r = Σ_t C(r+1,t) B_t p^{n(r+1−t)}/(r+1)`
     and Newton's identities, and show that the leading `p`-adic term is
     `c · p^n · B_{k}/k` with `c` a unit.
   - The corrected formula above, `T_k = v_p(B_{k_e}/k_e)` for `a = 1`, is the natural theorem
     to aim at. Its `a > 1` and `n = 1` analogue (W2, `k ≡ 32 + 18(a−23) mod 666`) suggests the
     relevant Bernoulli argument shifts with `a`, much as Zhao's `m ≡ −s (mod p(p−1))` does.
   - The `p = 67` excess-2 case at `k = 3292` is the anomaly to explain first.
2. **Fubini and involution trees at deep levels.** Same lifting mechanics, a simple root versus a
   double root modulo `p`: look for a single-root class whose derivative vanishes, as in the
   `p = 971` Givens–Moll example. Only level 1 was run here.

## Proposed atlas lines

```jsonl
{"premise": "Computation: v_37(s(1369,1085)) = 4 (unsigned Stirling first kind; C row DP mod 37^12, FLINT product tree, exact Newton-identity big integers); v_37(B_284/284) = 2", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Hong–Qiu Conjecture 5.2 (p = 37, a = 1, n = 2, k = 284 predicts 3) is false; hence Conjecture 5.1(i) is false", "consequence_ref": "S. Hong, M. Qiu, Acta Math. Hungar. 161 (2020) 366–395, arXiv:1908.05594 v2, Conjectures 5.1, 5.2", "consequence_status": "open", "implication_source": "this sweep, disproof-scripts/padic-lifting (hq.c, hq_flint*.py, exact_newton.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route (e). Fails at every irregular prime p < 160 (n = 2, a = 1) and at n = 1 for a >= 16 (p = 37: s(851,819), v = 3 vs 2). Lifted family v_37(s(37^n,37^n-284)) = n+2 for n = 2..5; diagonal v_37(s(37^j,37^j-k_j)) = 2j for j = 2,3,4 with k_j the level-j Kummer index (284, 37580, 1072544), so the error is unbounded. Lean: Nat.stirlingFirst row checker mod 37^5 under native_decide", "novelty": "not-found", "novelty_searched": "Exa web, arXiv/AIMS (Qiu–Lin–Chen 2026 says p>=5 open), GitHub code and issues, 1337 results list; 2026-11-26 12:55 UTC", "sweep": "2026-11-26", "lane": "disproof-padic-lifting"}
{"premise": "Computation: v_37(s(31487,819)) = 35 while v_37(s(31487,37*23)) = 0 and v_37(s(31487,31455)) = 3 (p = 37, a = 23, n = 2, m = 1, k = 32)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Hong–Qiu Conjecture 5.3 (comparison formula) is false: right side 0 + 3 + 31 = 34", "consequence_ref": "arXiv:1908.05594 v2, Conjecture 5.3", "consequence_status": "open", "implication_source": "this sweep (hq53.py FLINT; hq_m.py pure-Python column DP mod 37^45; hq.c)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route (e); holds for a = 1 in the same range, fails with the n = 1 anomaly lifted to m = 1", "novelty": "not-found", "novelty_searched": "as above", "sweep": "2026-11-26", "lane": "disproof-padic-lifting"}
{"premise": "Computation: 59 | I_1(24) and 59 | I_1(41) (involution numbers), both classes mod 59 with non-constant valuation", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Amdeberhan–Moll involution-tree conjecture (single non-terminal vertex per level for every inefficient prime) is false at level 1, p = 59", "consequence_ref": "T. Amdeberhan, V. H. Moll, Involutions and their progenies, J. Comb. 6 (2015), arXiv:1406.2356, §4", "consequence_status": "open", "implication_source": "this sweep (literature sub-agent, rechecked)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "shallow: first level", "sweep": "2026-11-26", "lane": "disproof-padic-lifting"}
{"premise": "Computation: F_n (Fubini) mod 13 vanishes on two classes mod 12 (n = 0, 3), each with valuations {1,2,3}", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Caicedo–Moll–Ramírez–Villamizar Conjecture 64 (single non-constant class per level, every p > 5) is false at p = 13, level 1", "consequence_ref": "EJC 26(2) (2019) P2.20, Conjecture 64", "consequence_status": "open", "implication_source": "this sweep", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "shallow: first level; deeper multiple-root failures not searched", "sweep": "2026-11-26", "lane": "disproof-padic-lifting"}
{"premise": "Computation: S(n,k) mod 2^64, h <= 16 (c <= 8) and h <= 12 (c <= 40)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Adelberg–Lengyel conjecture con:a+2 inside the hypothesis 2^{h-2} >= nu_2(C(2c-b-1,c))", "consequence_ref": "A. Adelberg, T. Lengyel, arXiv:2111.08766, Conjecture (label con:a+2)", "consequence_status": "open", "implication_source": "this sweep (st2.c)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 20 CPU-s; 35 failures only outside that hypothesis", "sweep": "2026-11-26", "lane": "disproof-padic-lifting"}
```

```jsonl
{"construction": "Level-j Kummer indices k_j of an irregular pair (p, l) (37^j | B_{k_j}/k_j; for (37,32): 284, 37580, 1072544, 55777784), evaluated in s(a p^n, a p^n - k) = e_k(1..ap^n - 1)", "source": "docs/atlas/sweeps/2026-11-26/disproof-padic-lifting.md; disproof-scripts/padic-lifting", "computable": "v_p of e_k(1..N-1) mod p^12 by FLINT product tree (N up to 37^5) or C row DP; B_k/k mod p^{2J-1} by power sums over i < p^J", "refutes": [{"conjecture": "Hong–Qiu Conjectures 5.1(i), 5.2, 5.3", "ref": "arXiv:1908.05594 v2 §5; p = 37: s(1369,1085) has v = 4 (conjectured 3); unbounded error 2j vs j+1", "lean": "not started"}], "method": "analytic location", "neighbours_tested": [{"conjecture": "Hong–Qiu 5.2 at regular primes 5, 7 (and p <= 13 by sub-agent)", "outcome": "holds on the family", "report": "docs/atlas/sweeps/2026-11-26/disproof-padic-lifting.md"}], "neighbours_untested": ["Lengyel 2015 odd-k conjecture v_p(s(ap^{n+1},ap^{n+1}-k)) = v_p(s(ap^n,ap^n-k)) + 2 at irregular p (only 'sufficiently large n')", "Leonetti–Sanna lower-bound conjecture at irregular p", "Komatsu–Young / Adelberg exact formulas restricted to regular primes, applied at irregular p", "Hong–Qiu Theorem 1.1-type statements for s(ap, k) used as equalities elsewhere (e.g. Barman–Narode–Wagh restrict to regular p)", "p-adic valuation formulas for multiple harmonic sums H({s}^l; p^n - 1) at irregular primes (Zhao's Remark 2.6 shows the same B_284 effect)"], "sweep": "2026-11-26", "lane": "disproof-padic-lifting"}
```
