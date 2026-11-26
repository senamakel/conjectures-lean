# Lane `disproof-matroid-transplant`: the coalescence family against open matroid-polynomial conjectures

Lane `disproof-matroid-transplant`, 2026-11-26. Research and computation only. No Lean file and no
existing file was edited. The model is the Caiolo–Ferroni–Hoster (CFH) disproof in
1337isnot1337/solved-conjectures (`results/caiolo-ferroni-hoster/`, shallow clone of `main` on
2026-11-26, read as data; none of its scripts were run). Everything here was reimplemented. Scripts
are in [`disproof-scripts/matroid-transplant/`](disproof-scripts/matroid-transplant/). Claims I
could not confirm from a primary source are marked *(unverified)*. Total cost was under one
CPU-hour: everything is symbolic, or exact integer arithmetic over closed formulas.

## Main finding

**No hit.** The coalescence family was tested against every surviving open conjecture that is a
function of the lattice of flats: inverse Z unimodality and log-concavity, Z log-concavity,
dominance by the uniform matroid, rank-4 dual-Chow interlacing, and Whitney-number shapes. It
satisfies all of them, at ranks 4 to 9 and over a range of q, and so do its variants (products,
truncations, the Cheng–Liu deletions, Bose–Burton geometries). In every case the margins are
O(1) or decay only in the harmless "flattening" direction.

The target pool turned out much thinner than the brief assumed. Four of the conjectures it lists
were already refuted in 2026:

- KL log-concavity and unimodality: Cheng–Liu, arXiv:2607.24186.
- Rota's unimodality and Mason's log-concavity for Whitney numbers of the second kind: Larson
  2607.02208; Divoux–Lowen–Wang 2607.22515; Divoux–Larson–Lowen–Wang 2608.07342.
- Gao–Xie inverse-KL log-concavity: Badalov 2609.13417.
- Binder–Vecchi Conj. 1.5: it is false at i = 0, because the i = 0 polynomial is the Chow
  polynomial, which BCEL refute.

The CFH numbers were **reproduced exactly** (yes). Four independent checks confirm the machinery.

Two by-products are worth keeping.

1. **A layer formula for the inverse Z-polynomial.** It is an exact identity in the flag algebra,
   checked for every rank up to 9:
   `Y_M(t) = Σ_j c_j(M) t^j [r+1−2j]_t`, with `c_0 = β([r−1])`, `c_1 = β([r−1]∖{1})`, and in
   even rank `c_{r/2}(M) = P_{r/2−1}(T_{r−1}M) ≥ 0`. Here `T_{r−1}` is truncation to rank r−1,
   and the coefficient is the top KL coefficient of that truncation.

   So Gao–Ruan–Xie Conj. 1.4 (unimodality of Y) holds automatically in rank ≤ 4. In rank 5 it is
   equivalent to one explicit inequality on points, lines and hyperplanes:
   `Σ_H (W₂(H) − W₁(H)) ≥ W₂ − W₁`.
2. **Badalov's first-index question.** It was answered negatively in 1337 #299 (rank 5, q ≥ 17).
   It also fails on the same family at **ranks 6, 7, 8 and 9 for q ≥ 13, and at rank 5 already for
   q = 16**. This extends a claim that is already made. It is not a new resolution.

## 1. Method

### 1.1 The flag algebra (why the transplant works for KL-type invariants too)

Consider any element of the incidence algebra of a graded poset that is built from the
characteristic kernel χ by these operations: convolution, inversion, `rev`, the sign twist, the
KLS solve, and multiplication by `t^rank`. Its value on an interval is a universal linear
function of the flag f-vector of that interval: `Σ_{c ⊨ n} w(c) α(S(c))`, where c runs over the
compositions of the rank.

The weights live in the free algebra on compositions. Convolution splits a composition. The
inverse is the geometric series. The KLS solve is done composition by composition, and the code
checks that the antisymmetry of the right-hand side holds at every composition (it does, at every
rank up to 9). Flag f-vectors of graded posets satisfy no linear relations (Billera–Hetyei), so
these formulas hold on every graded poset. By uniqueness of KLS functions they are the true P, Q,
Z, Y and χ.

So P, Q, Z and Y are flag-vector functions, exactly like the dual Chow polynomial: no recursion
over contractions is needed. Implementation: `compalg.py` and `invs.py` (python-flint
`fmpz_poly`). Building the algebra up to rank 9 takes seconds.

Expansions in the flag h-vector β (`betaw.py`), in rank 5 (R = {1,2,3,4}):

| Invariant | Expansion |
|---|---|
| P (KL) | `1 + (β4 − β1) t + (β12 − β14 − β23 + β24) t²` |
| Q (inverse KL) | `β1234 + (β234 − β123) t + (β12 − β14 − β23 + β24) t²` |
| Z | `[6]_t + β4·t[4]_t + (β24 − β23)·t²[2]_t` |
| Y (inverse Z) | `β1234·[6]_t + β234·t[4]_t + (β24 − β14)·t²[2]_t` |

### 1.2 The coalescence family, general rank

`flags.py` implements `M_{k,q}` of rank r = k+1, the construction stated in the 1337 RANKS.md:

- K = F_{q^k} and V = K ⊕ K;
- m = q^k free points;
- b = q^{k²} blocks, each the graph of a linearised polynomial together with the free point
  labelled by its top coefficient;
- truncation to rank k+1 before coalescing.

Ranks below k are those of `D_{2k,m}`, the product of the subspace lattice of F_q^{2k} with the
Boolean lattice on m points. The hyperplane types are:

| Type | Multiplicity |
|---|---|
| (k,0) | `N_k − b` |
| (k,1), truncated | b |
| (k−1,1) | `m N_{k−1} − b[k,k−1]_q` |
| (d, k−d) for d ≤ k−2 | `N_d·C(m,k−d)` |

Here `N_i = [2k,i]_q`. `A(d,t;S)` is the largest-flat recursion.

### 1.3 Validation (all exact)

| Check | Result |
|---|---|
| CFH rank 5, q = 17: `(g0,g1,g2)`, `g1²−4g0g2`, `(h0,h1,h2)` | `(1367432169863264385040621589, 677031173160167651396287043, 85823997163784007690567699)`, disc `−11062769241414341239970603495681493737981374532130995`; h-triple equal to the published one. **Exact match** |
| 1337 issue #299 inverse KL at rank 5, q = 17 | `Q = 1367432169863264385040621589 + 236827334118626401257039561 t + 43971319705548460332837139 t²`. **Exact match** |
| RANKS.md: first prime power ≤ 37 where both dual polynomials fail (exact Sturm counts via `sympy.count_roots`, general-rank CFH Thm 4.9 with stable sets) | 17 (rank 5), 11 (rank 6), 7 (ranks 7 and 8). **Match** |
| Explicit matroid `M_{3,2}` (63 points of PG(5,2) and 8 free points; 512 blocks over F_8, `explicit_k3.py`): rank function, flats by closure, flags counted directly | All 8 flag numbers match the recursion: 71, 1183, 4839, 3017, 22233, 25305, 61999 |
| Second route on the same lattice (`incidence_k3.py`): direct incidence-algebra recursion over all 68,837 intervals | χ, P = 1+4768t, Q = 17536+17520t, Z = 1+4839t+20399t²+…, Y = 17536+36820t+37932t²+…: **identical** to the flag-algebra values |
| Cheng–Liu Remark 2.7 (Bose–Burton `B_{r,k}(q)`: P = G_k, Z = G_r for k < r/2; general P formula) | Match, e.g. `P_{B_{6,4}(2)} = 1+15t+34t²` |
| Cheng–Liu Prop. 2.6 on explicit PG(r−1,2) minus D, r = 5, 6 (`pgdel_explicit.py`, 105 cases) | P = G_k + s·t in every case |
| Gao–Ruan–Xie Thm 1.1 (Y of `U_{k,n}`) | Match for all 1 ≤ k ≤ 7, k ≤ n ≤ 9 |
| Sanity checks | P(Boolean) = 1, P(PG) = 1, linear KL coefficient = `W_{r−1} − W_1` |

## 2. Target pool and status (prior art first)

Statuses come from arXiv abstract and HTML pages, GitHub issues and the SymCat catalogue, read on
2026-11-26. One sub-agent ran the literature pass. Where it was the only reader, the row says so.

| # | Conjecture (source) | Flag-vector function? | Status 2026-11-26 | Outcome here |
|---|---|---|---|---|
| 1 | KL coefficients log-concave, no internal zeros (EPW 1412.7408 Conj 2.5) | yes | **refuted**, Cheng–Liu 2607.24186: non-unimodal over every F_q | already settled. The coalescence family is LC with ratios ≥ 11 |
| 2 | KL real-rooted (GPY 1611.07474 Conj 3.2) | yes | **refuted**, Cheng–Liu; Eberhardt 2609.20903 (Golay) | already settled |
| 3 | Z real-rooted (PXY 1706.05575 Conj 5.1) | yes | **refuted**, Eberhardt (Golay); proved for sparse paving (Xie–Zhang 2609.07636) | already settled |
| 4 | Z log-concave (trivial-group case of PXY Conj 6.5) | yes | open (implicit; sub-agent) | **holds on the family**; min ratio `z_i²/(z_{i−1}z_{i+1})` ≥ 6.2 (k ≤ 8, q ≤ 32); all variants ≥ 1.73 |
| 5 | Q (inverse KL) LC (Gao–Xie 2007.15349 Conj 4.2) | yes | **refuted**, Badalov 2609.13417. Gao–Xie never conjectured real-rootedness | already settled |
| 5′ | Badalov §8 first-index inequality `c₁² ≥ c₀c₂` for Q | yes | 1337 #299 claims a counterexample (rank 5, q ≥ 17; unrefereed) | reproduced. It also fails at ranks 6–9 for q ≥ 13, and at rank 5 for q = 16 (§3.3) |
| 6 | Y (inverse Z) unimodal / LC, no internal zeros (Gao–Ruan–Xie 2507.01332 Conj 1.4 / 1.5) | yes | **open**; RealRooted #1405 open; 1337 #300 claims all paving (unrefereed) | **holds on the family and every variant**. See §3.1 for margins and the structural reduction |
| 7 | Whitney numbers of the 2nd kind unimodal / LC (Rota; Mason) | yes | **refuted**: Larson 2607.02208; Divoux–(Larson–)Lowen–Wang 2607.22515, 2608.07342 (sub-agent, abstracts) | already settled. The family is LC, ratio ≥ 1.42 |
| 8 | Chow, augmented Chow, chain polynomials real-rooted or LC (FS 8.18, Huh–Stevens, AKE Conj 1.2, FMSV Conj 1.6/5.7, AKE Conj 5.1) | yes | **refuted**, BCEL 2610.17135 | already settled |
| 9 | Binder–Vecchi 2609.15946 Conj 1.5 (refined Hodge–Poincaré real-rooted for all i) | i = 0 is the Chow polynomial; i ≥ 1 is not a flag function (Koszul homology) | **false at i = 0** by BCEL; RealRooted #1395 closed negative | already settled. i ≥ 1 is not computable from the construction |
| 10 | CFH Conj 7.3 (dual Chow) and the augmented and interlacing parts | yes | **refuted** (1337 #111); rank-4 interlacing is a residual question (1337 #675) | rank-4 interlacing criterion `β123·β2 ≤ β12(β13+β23)` holds on `M_{3,q}` with ratio ≥ 2.50 (q ≤ 1009), and on all rank-4 variants with ratio ≥ 2.42 |
| 11 | Gedeon: `P_M ⪯ P_{U_{r,n}}`, `Z_M ⪯ Z_{U_{r,n}}` coefficientwise (FMSV Conj 3.29) | yes (and n) | open (sub-agent; known for paving) | **holds**; the uniform matroid dominates by orders of magnitude (n ~ q^{2k−1}) |
| 12 | GPY Conj 3.4 (interlacing of `t^{r−1}P(−t^{−2})` under contraction) | yes | formally open, but it presupposes real roots, and these fail for Golay (non-degenerate). Contraction not checked *(unverified)* | not pursued |
| 13 | Sinclair 2608.18519 Conj B/C (`H_β` LC and front-loading) | **no**: ranks of operators on the Möbius algebra, not valuative | open | not computable from the construction |
| 14 | Athanasiadis–Ferroni 2410.08812 augmented Bergman complex: f-vector unimodal | needs independent-set counts inside flats (explicit for this family) | open *question* (not a conjecture); f and h fail LC, h fails unimodality | not pursued: low-dimensional f-vectors (dim ≤ r−1) are essentially always unimodal |
| 15 | Ultra-log-concavity of the Whitney numbers of the first kind | yes | status not researched *(unverified)* | holds on the family (ratio of `w_k/C(r,k)` ≥ 1.03) |

Out of scope: the equivariant conjectures, which are stated for uniform and q-niform matroids;
Coxeter Chow (FMV Conj 1.11/1.12); `M̄_{0,n}`; the f-vector of the matroid base polytope; the h and
h* of matroid complexes (log-concavity is proved by Ardila–Denham–Huh; Stanley's pure O-sequence
conjecture is not a real-rootedness statement).

## 3. Per-target transplant analysis and computations

### 3.1 Inverse Z-polynomial (GRX 1.4 / 1.5): the one substantive survivor

**Layer formula** (`ylayers.py`, an exact identity of universal β-weights, ranks 3–9):

```
Y_M(t) = Σ_{j=0}^{⌊r/2⌋} c_j(M) t^j (1 + t + … + t^{r−2j})
c_0 = β(1..r−1)                    = |μ(M)|
c_1 = β(2..r−1)                    = Σ_x |μ(M/x)| − |μ(M)|
c_2 = β({2}∪[4,r−1]) − β({1}∪[4,r−1])
c_3 = β({1,2}∪[6,r−1]) − β({1,4}∪…) − β({2,3}∪…) + β({2,4}∪…)
c_4 (r = 8) = −β123 + β126 + β145 − β146 + β234 − β236 − β245 + β246
```

In even rank r = 2j, `c_j(M) = P_{j−1}(T_{2j−1}M)`, the top KL coefficient of the truncation. This
was checked at r = 4, 6, 8, so `c_{r/2} ≥ 0` by KL non-negativity (BHMPW).

Y is palindromic with nonnegative partial sums of the `c_j`. So:

- **Unimodality (Conj 1.4) ⇔ `c_j ≥ 0` for 1 ≤ j < r/2**, and `c_1 ≥ 0` because flag h-numbers of
  geometric lattices are nonnegative. Hence Conj 1.4 holds in every rank ≤ 4.
- In rank 5 it is equivalent to `β24 ≥ β14`. By the top-removal identity
  `β(S∪{r−1}) + β(S) = Σ_H β_H(S)`, this reads
  `Σ_{hyperplanes H} (W₂(H) − W₁(H)) ≥ W₂(M) − W₁(M)`.
- **Log-concavity in rank 4 ⇔** `W₂ − W₁ ≤ β23 + β23²/β123`. The middle index is automatic.

As far as I found, this reduction is not in the literature (searched GRX, BFMN 2510.01086, 1337
#300 and RealRooted #1405). It is my own computation, not a refereed result.

**On the family.** Y is asymptotically `|μ|·[r+1]_t`. For example, at rank 5, q = 17:

```
Y = 1367432169863264385040621589·[6]_t + 236843214584546859321057921·t[4]_t + 43973190679258315370709500·t²[2]_t
```

The log-concavity gaps are `Y1²−Y0Y2 = 3.198…·10^53` and `Y2²−Y1Y3 = 7.25·10^52`, both positive.
Relative slack at index 1 is about `(c1−c2)/c0 ≈ 2.5/q`: c₁/c₀ → 3/q and c₂/c₀ → 0.5/q. The
slacks at the inner indices tend to 0 like `q^{−c}`, because the coefficients flatten. That is not
an approach to failure: it goes with `c_j/c_{j−1} → 0`, and failure needs `c_j` large compared
with `c_{j−1}`.

Rows of `scan1.py`, smallest LC ratio of Y:

| k (rank k+1) | q = 2 | q = 17 | q = 1009 |
|---|---|---|---|
| 3 | 1.061 | 1.0000375 | 1+3.8e−12 |
| 4 | 1.234 | 1.0274 | 1+4.9e−4 |
| 5 | 1.0069 | 1+7.7e−9 | 1+3.7e−21 |
| 7 | 1.00085 | 1+1.6e−12 | 1+3.6e−30 |

All are flattening-type minima at the middle index.

**Variants** (`yscan.py`, 210 lattices): truncations to ranks 4–8 of products of lines `U_{2,s}^m`
(s ≤ 100, m ≤ 4) with Boolean factors; truncations of `PG(d,q) × B_t`; PG minus a point;
Bose–Burton `B_{r,k}(q)` for r ≤ 9, q ≤ 5 (`bbscan.py`); Cheng–Liu deletions of PG(4,2) and PG(5,2)
(`pgdel_explicit.py`, 105 cases; there Y is affine in s and independent of the choice of S). No
failure of unimodality or LC for Y, Z or P, apart from the known Cheng–Liu P anomalies at higher
rank. The largest `c₂/c₁` seen was 2.57 (`T₈(PG(2,2)×B₁₀)`), and the corresponding index stayed LC
with slack ≥ 0.17.

**Why a rank-5 failure is hard (heuristic, not a proof).** `c₂ = Σ_L (h(L)−1) − Σ_x (h(x)−1)`,
where h counts hyperplanes through a flat. Failure needs points to sit in more hyperplanes than
lines do. Uniform-like lattices give a ratio of 2/3 and projective ones 1/q. Long lines help: the
contribution of x scales as `s/avg|H/x|`. But any hyperplane through x that contains an s-point
line avoiding x already has ≥ s lines through x, which cancels the gain. I found no family where
`Σ_x h(x)` beats `Σ_L h(L)`.

### 3.2 Z log-concavity

In rank 5, LC fails only if `β24 − β23 = Σ_L (W₂(M/L) − W₁(M/L)) + W₃ − W₄ > (W₄−1)(W₄−2)`. The
left side is bounded by `Σ_H W₂(H)`. Exceeding W₄² needs hyperplanes holding more lines than there
are hyperplanes, and also non-modular rank-3 contractions. PG(4,q) meets the first condition only
barely (`[4,2]_q/[5,1]_q → 1⁺`) and fails the second, since its contractions are modular. On the
family the smallest ratio is 6.2. The gap at rank 5, q = 17 is `z1²−z0z2 = 4.88·10^48`.

### 3.3 Inverse KL (Q): first index, beyond rank 5

`scan1.py` gives the smallest ratio `Q_i²/(Q_{i−1}Q_{i+1})`. At rank 5 it drops below 1 from
q = 16 (0.9833). At ranks 6–9 it drops below 1 from **q = 13**, and the failure is at index 1
every time. Gao–Xie 4.2 is already refuted (Badalov), and the first-index rank-5 claim is 1337's
(#299), so this only extends existing claims. It is recorded so it is not rediscovered.

### 3.4 Not computable from the construction

- Binder–Vecchi i ≥ 1 needs Koszul homology. Sinclair's `H_β` needs operator ranks. Equivariant
  invariants need a group action and are stated for uniform matroids only.
- The Golay matroid G₂₄ (rank 12) and Larson's theta matroid M₂₆ (rank 76) were not evaluated for
  Y. Golay would need its flats enumerated. For M₂₆ the composition algebra has 2^75 entries; a
  series-parallel recursion might work but was not attempted.

## 4. Hits and misses

- Hits: none.
- Misses with ranges:
  - Y and Z on `M_{k,q}` for 3 ≤ k ≤ 8 and q ∈ {2,…,32} (18 values), plus q ∈ {101, 1009} at
    selected k.
  - 210 product and truncation lattices.
  - Bose–Burton r ≤ 9, q ≤ 5, all k.
  - 105 explicit Cheng–Liu deletions in PG(4,2) and PG(5,2).
  - The rank-4 CFH interlacing criterion on 21 values of q and 40 rank-4 variants.
  - Gedeon dominance on 7 members.
  - Cost: under 1 CPU-hour. There is no search to repeat; the family is closed-form.
- **Best unfinished lead: GRX Conj 1.4 in rank 5**, now equivalent to
  `Σ_H (W₂(H) − W₁(H)) ≥ W₂ − W₁`. One of two things should follow:
  - a short proof from the points–lines inequalities. Dong–Liu 2610.29893 prove Mason's
    strongest points–lines–planes inequality, and `W₂(H) ≥ 2W₁(H) − 2` in rank 4 looks true
    *(unverified)*. Such a proof would be a positive partial result on an open conjecture;
  - or a structured counterexample, which needs points in many more hyperplanes than lines.

  Second lead: rank-4 log-concavity of Y, `W₂ − W₁ ≤ β23(1 + β23/β123)`, which needs
  `Σ_L(deg L − 2) < W₃ − W₁ − 1` (deg L counts the planes through L).

## 5. Lean route (if a hit had appeared)

The 1337 pattern (`lean/Conjectures/CaioloFerroniHoster*.lean`) has three parts: a matroid
witness, flag counts by the largest-flat recursion, and Theorem 4.9 proved on finite ranked
posets. For Y or Z the extra ingredient is the universal β-expansion of §1.1. In Lean it would be
proved on finite graded posets from the KLS recursion, as an identity in the incidence algebra, as
1337 did for the CFH kernel functions in `CaioloFerroniHosterRankBridge.lean`. The counterexample
inequality itself would then be a degree-bounded polynomial identity in q, with a positivity
certificate after the shift q = q₀ + s.

## Proposed edges

```jsonl
{"premise": "Computation: flag-algebra evaluation of the inverse Z-polynomial Y on the BCEL coalescence matroids M_{k,q} (rank k+1, 3<=k<=8, q<=32 and q=101,1009) and 210 product/truncation/Bose-Burton/Cheng-Liu variants", "premise_status": "open", "premise_lean_source": "", "consequence": "counterexample to Gao-Ruan-Xie Conj 1.4/1.5 (Y_M unimodal / log-concave)", "consequence_ref": "arXiv:2507.01332 Conj 1.4, 1.5; RealRooted #1405", "consequence_status": "open", "implication_source": "", "effort": "L", "lean_exists": "", "in_1337": false, "class": 1, "notes": "negative: holds on every member; Y ~ |mu|[r+1]_t, index-1 slack ~2.5/q. New reduction: Y = sum_j c_j t^j [r+1-2j]_t; c_{r/2} = P_{r/2-1}(trunc) >= 0; Conj 1.4 automatic for rank <= 4, rank 5 iff sum_H (W2(H)-W1(H)) >= W2-W1", "sweep": "2026-11-26", "lane": "disproof-matroid-transplant"}
{"premise": "Computation: Z-polynomial on M_{k,q} and variants (flag algebra; cross-checked by direct incidence algebra on explicit M_{3,2})", "premise_status": "open", "premise_lean_source": "", "consequence": "counterexample to log-concavity of Z_M (trivial-group case of PXY Conj 6.5)", "consequence_ref": "arXiv:1706.05575 Conj 6.5 / Remark 6.6", "consequence_status": "open", "implication_source": "", "effort": "L", "lean_exists": "", "in_1337": false, "class": 1, "notes": "negative: min LC ratio >= 6.2 on the family, >= 1.73 on variants; rank-5 failure needs beta24-beta23 > (W4-1)(W4-2)", "sweep": "2026-11-26", "lane": "disproof-matroid-transplant"}
{"premise": "Computation: inverse KL polynomial Q on M_{k,q}", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Badalov first-index inequality c1^2 >= c0 c2 for Q_M fails at ranks 6-9 for q >= 13 and at rank 5 for q = 16 (index 1 each time)", "consequence_ref": "arXiv:2609.13417 Section 8; 1337isnot1337 issue #299 (rank 5, q >= 17)", "consequence_status": "refuted", "implication_source": "computed in this sweep; extends the 1337 #299 claim", "effort": "S", "lean_exists": "1337 CFH coalescence modules (rank 5 Q not formalised there)", "in_1337": true, "class": 1, "notes": "no new resolution; Gao-Xie Conj 4.2 already refuted by Badalov", "sweep": "2026-11-26", "lane": "disproof-matroid-transplant"}
{"premise": "BCEL arXiv:2610.17135 Thm A (Chow polynomials not real-rooted)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Binder-Vecchi Conj 1.5 (refined Hodge-Poincare polynomials real-rooted for all 0<=i<=n-r) is false at i=0", "consequence_ref": "arXiv:2609.15946 Conj 1.5; RealRooted #1395 (closed negative)", "consequence_status": "refuted", "implication_source": "i=0 polynomial equals the Chow polynomial (BV26 Sec. 1)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "already settled; i>=1 for non-uniform matroids not separately settled and not a flag-vector function", "sweep": "2026-11-26", "lane": "disproof-matroid-transplant"}
{"premise": "Computation: rank-4 coalescence M_{3,q} and 40 rank-4 variants", "premise_status": "open", "premise_lean_source": "", "consequence": "counterexample to rank-4 dual Chow / dual augmented interlacing (beta123*beta2 <= beta12*(beta13+beta23))", "consequence_ref": "CFH arXiv:2605.28474 Conj 7.3 (residual rank-4 case, 1337 RANKS.md, issue #675)", "consequence_status": "open", "implication_source": "", "effort": "M", "lean_exists": "", "in_1337": true, "class": 1, "notes": "negative: ratio >= 2.50 on M_{3,q} (q<=1009), >= 2.42 on variants; parent conjecture already refuted", "sweep": "2026-11-26", "lane": "disproof-matroid-transplant"}
```
