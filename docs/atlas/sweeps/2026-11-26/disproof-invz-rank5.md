# Lane `disproof-invz-rank5`: the rank-5 inequality behind Gao–Ruan–Xie Conj. 1.4

Lane `disproof-invz-rank5`, 2026-11-26. Research and computation only. No Lean file and no
existing file was edited. Scripts are in [`disproof-scripts/invz-rank5/`](disproof-scripts/invz-rank5/).
This picks up the lead from [`disproof-matroid-transplant.md`](disproof-matroid-transplant.md) §3.1.
Total compute was about 0.3 CPU-hours. The work was stopped early by the coordinator, so the last
two scans were killed before they finished (see §5).

## Outcome

1. **There is no counterexample, and the target is no longer open.** GRX Conj. 1.4 (unimodality of
   the inverse Z-polynomial) is already proved for **every** loopless matroid. The proof is in the
   Rethlas manuscript *"Unimodality of inverse Z-polynomials of matroids"* (frenzymath/Rethlas_results,
   `AlgComb/MatroidKazhdanLusztig/inverse_z_unimodal.pdf`, revision `895e3d12ba02`, 11 Sep 2026).
   It is AI-generated, its proof was checked by R. Cheng and S. Liu, and it is unrefereed. The
   manuscript credits an earlier independent solution by Luis Ferroni and a later one by Elias
   Badalov. Neither of those is public as far as I found. The key identity there is
   `y_i − y_{i−1} = q_i(M) + q_{i−1}(T(M))` for `0 ≤ i ≤ ⌊r/2⌋`, where `T` is truncation and `q` are
   inverse-KL coefficients. Nonnegativity comes from BHMPW. **This identity is exactly the "layer
   formula" of the previous report** (`c_j = q_j(M) + q_{j−1}(T M)`; its Corollary 4.1). So the
   earlier "new reduction" is prior art, and the rank-5 inequality is a special case of a known
   theorem. Nothing here should be reported as a new resolution.
2. **The inequality is true, with an elementary proof (verified).** The proof below is
   combinatorial and avoids BHMPW. It gives the stronger, sharp bound
   `Σ_H (W₂(H) − W₁(H)) − (W₂ − W₁) ≥ W₁`, with equality for the lattice of B₅. That is an
   elementary proof of the rank-5 case of a known theorem, with an explicit lower bound. It is a
   by-product, not a new result on an open conjecture. I did not search whether this explicit bound,
   or the rank-4 lemma, is already in the literature *(unverified novelty)*.
3. **Log-concavity (GRX Conj. 1.5) remains open in general.** 1337 #300 claims it for paving
   matroids (unrefereed), and the Rethlas manuscript states that its identity does not give
   log-concavity. In rank 5, log-concavity is equivalent to `c₁(c₀ + c₁) ≥ c₀c₂` (see §4). This is
   the best unfinished lead.

## 1. Prior art (searched 2026-11-26)

| Source | What it says |
|---|---|
| GRX arXiv:2507.01332 v1 (only version) | Definitions (2)–(3); Conj 1.4 (unimodal), Conj 1.5 (LC, no internal zeros); proved for sparse paving. No small-rank claims |
| RealRooted #1405 (open, last comment 2026-10-29) | Lists both conjectures as open; does not know of the Rethlas proof |
| 1337isnot1337/solved-conjectures #300 (open) | Claims strict LC for all paving matroids (commit `6bd762a`), partial progress |
| Rethlas manuscript (above) | **Proves Conj 1.4 for all loopless matroids** via the truncation identity |
| evidencepress.org "Equivariant unimodality of inverse Z-polynomials" (Zenodo 10.5281/zenodo.23995561, 2026-11-06) | Lifts the Rethlas identity equivariantly (GLX Conj 1.2). It is where I found the Rethlas reference |
| arXiv:2601.17314 (Gao–Li–Xie), 2603.25254 (fan matroids), 2609.13417 (Badalov) | Nothing on general non-equivariant unimodality or LC (abstracts read) |

I read the Rethlas proof (§3, about one page). It uses the inverse-KL functional equation for `M`
and for `T(M)`, plus `xχ_T(x) = χ_M(x) + (x−1)μ_M`, and I found no gap. I also checked its
identity numerically (§3). The searches were web search, arXiv abstract pages, `gh search` over
issues, PRs and code, and evidence-press-site PR #756. Google Scholar was not searched.

## 2. Elementary proof of the rank-5 inequality

Notation: `M` is a simple rank-5 matroid with lattice of flats `L`. `W_k` is the number of rank-k
flats, `W_k(F)` is the same count inside a flat `F`, and `h(F)` is the number of hyperplanes
containing `F`. Write `α₁₄ = Σ_H W₁(H)` and `α₂₄ = Σ_H W₂(H) = Σ_L h(L)`. With flag h-numbers,
`c₂ := β₂₄ − β₁₄ = α₂₄ − α₁₄ − W₂ + W₁`, and in rank 5
`Y = c₀[6]_t + c₁ t[4]_t + c₂ t²[2]_t`, so unimodality is equivalent to `c₂ ≥ 0` (`c₁ = β₂₃₄ ≥ 0`).

**Lemma (rank 4).** A simple rank-4 matroid `F` on `n` points has `W₂(F) ≥ 2n − 2`.

*Proof.* Fix a point `x` and let `d` be the number of lines through `x`. Then
`d = W₁(F/x) ≥ 3`, and `Σ_{L∋x}(|L| − 1) = n − 1`, because every other point lies on exactly
one line through `x`. Each line not through `x` lies in exactly one plane through `x`, namely
`cl(L ∪ x)`. For a plane `π ∋ x`, let `λ_π` be the number of lines through `x` inside `π`. Then
`W₁(π) = 1 + Σ_{L∋x, L⊆π}(|L| − 1)`, and de Bruijn–Erdős in the rank-3 flat `π` gives
`W₂(π) ≥ W₁(π)`. Hence

`W₂ = d + Σ_π (W₂(π) − λ_π) ≥ d + Σ_π [1 + Σ_{L∋x, L⊆π}(|L| − 2)] = d + W₂(F/x) + Σ_{L∋x}(|L| − 2)·deg L`,

where `deg L` is the number of planes containing `L`. Two facts about the rank-3 geometric
lattice `[x, 1̂]` finish it. First, de Bruijn–Erdős gives `W₂(F/x) ≥ d`. Second, `deg L ≥ 2`,
since each atom of a rank-3 geometric lattice lies on at least two coatoms. So
`W₂ ≥ 2d + 2(n − 1 − d) = 2n − 2`. ∎

Equality holds for B₄ and for a line plus two points. Numerically: all 191,291 rank-4 matroids on
≤ 9 elements satisfy it, and 156 attain equality.

**Theorem (rank 5).** `c₂ = Σ_H (W₂(H) − W₁(H)) − (W₂ − W₁) ≥ W₁ > 0`. In particular `Y_M` is
unimodal in rank 5.

*Proof.* There are three facts.

- (A) `h(L) ≥ 3` for every line, because `[L, 1̂]` is a rank-3 geometric lattice and so has at
  least 3 coatoms. Hence `W₂ ≤ α₂₄/3`.
- (B) The Lemma applied to each hyperplane gives `α₂₄ ≥ 2α₁₄ − 2W₄`.
- (C) Each hyperplane has at least 4 points, so `α₁₄ ≥ 4W₄`.

Then

`c₂ ≥ (2/3)α₂₄ − α₁₄ + W₁ ≥ (2/3)(2α₁₄ − 2W₄) − α₁₄ + W₁ = α₁₄/3 − (4/3)W₄ + W₁ ≥ W₁`. ∎

Equality needs every hyperplane to be B₄ and every line to lie in exactly 3 hyperplanes. In the
database, every matroid with `c₂ = W₁` has Whitney numbers `(1,5,10,10,5,1)`, which means the
lattice is B₅: 26 matroids, all of them B₅ with loops or parallel elements added.

## 3. Verification (exact integer arithmetic)

- `lattice.py` is an independent direct implementation. It builds the flats from a rank oracle,
  computes μ, χ and the KL polynomial `P` by the KLS recursion, and gets `Q̂ = P⁻¹`,
  `Q = (−1)^rk Q̂`, then `Y` from GRX eqs. (2)–(3). It uses no flag algebra.
  - `test_direct.py` matches GRX Thm 1.1 for every `U_{k,n}` with k ≤ 5 and n ≤ 8, and gives
    `Q(U_{2,5}) = 4` and `Y(B₅) = (1+t)⁵`.
- `dbscan.py` runs exhaustively over every rank-5 matroid on ≤ 9 elements. These are the duals of
  the Matsumoto–Moriyama–Imai–Bremner rank ≤ 4 lists in the `matroid_database` 0.3 wheel from
  PyPI. The counts by n are 1, 6, 37, 325 and 190,214. It also covers every rank-4 matroid on ≤ 9
  elements.
  - Checks (A), (B) and (C) and `c₂ ≥ W₁` hold for all of them, with no failures.
  - Direct Y was computed on 4,174 rank-5 matroids (all with n ≤ 8, and every 50th with n = 9). On
    those, `Y = c₀[6] + c₁t[4] + c₂t²[2]` with `c₂` equal to the flag value, and Y is
    log-concave.
  - The rank-4 Lemma holds on all of them, and Y is unimodal and LC on the direct subset.
  - The run took about 70 s wall on 16 cores.
- `tight.py` produced the equality-case census above.

## 4. Log-concavity (Conj. 1.5): the open lead

In rank 5, `y₂² ≥ y₁y₃` is the same as `y₂ ≥ y₁` (because `y₂ = y₃`), so it follows from the
theorem. That leaves index 1, which is equivalent to `c₁(c₀ + c₁) ≥ c₀c₂`. Here
`c₀ = |μ(M)|`, `c₁ = Σ_x |μ(M/x)| − |μ(M)|` and `c₂` is as above. The stronger `c₁ ≥ c₂` is
false: for B₅, `c₁ = 4` and `c₂ = 5`. So a proof must use the quadratic form.

A natural next step is to pair the upper bound `c₂ ≤ α₂₄ − α₁₄` with lower bounds on `c₁` from
`|μ(M/x)| ≥ W₂(M/x) − W₁(M/x) + …`. I did not attempt it. The rank-4 analogue is
`W₂ − W₁ ≤ β₂₃(1 + β₂₃/β₁₂₃)` (previous report).

## 5. Not checked or not finished

- `lcscan.py` was killed by the wind-down before it printed anything. It runs direct Y and the LC
  check on all 381,505 database matroids of rank 4 and 5, and tests the Rethlas identity on every
  20th one against a directly computed `Q(T(M))`. So **full-database LC and the direct identity
  check are not done**. LC is confirmed only on the direct subsets in §3: 4,174 rank-5 matroids,
  and the rank-4 matroids with n ≤ 8 plus every 50th with n = 9. The
  identity was checked only indirectly: `c₂` agreed with `q₂(M) + q₁(T)` through the β-expansions
  `q₂ = β₁₂ − β₁₄ − β₂₃ + β₂₄` and `q₁(T) = β₂₃ − β₁₂`, the latter *(by analogy with the rank-5 table,
  not computed)*.
- `families.py` (PG(4,2), AG(4,2), T₅PG(5,2), AG(4,3), PG(4,3) and direct sums with long lines)
  was also killed before it produced output. The theorem covers these families anyway.
- No search for prior statements of the rank-4 Lemma or of the bound `c₂ ≥ W₁`.
- Rank ≥ 6 was not examined. Unimodality there is covered by the Rethlas proof.

## Proposed edge

```jsonl
{"premise": "Rethlas truncation identity y_i - y_{i-1} = q_i(M) + q_{i-1}(T M) + BHMPW nonnegativity of inverse KL", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Gao-Ruan-Xie Conj 1.4: inverse Z-polynomial unimodal for all matroids", "consequence_ref": "arXiv:2507.01332 Conj 1.4; frenzymath/Rethlas_results inverse_z_unimodal.pdf @895e3d12 (unrefereed; credits Ferroni, Badalov)", "consequence_status": "proved", "implication_source": "Rethlas manuscript Thm 1.1-1.2", "effort": "M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "kills the disproof lead from disproof-matroid-transplant; the layer formula there is Rethlas Cor 4.1. Elementary rank-5 proof with sharp bound c2 >= W1 (equality iff lattice B5) in disproof-invz-rank5.md; LC (Conj 1.5) still open, rank 5 iff c1(c0+c1) >= c0 c2", "sweep": "2026-11-26", "lane": "disproof-invz-rank5"}
```
