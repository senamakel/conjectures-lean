# Blueprint: formalizing Bach's explicit GRH bounds

Goal: remove the two `sorry`s in `Erdos985/Bach.lean`. A weaker explicit constant is acceptable:
`Numerics.lean` and the computation can be redone for a larger constant `K` (see the table at
the end).

Sources:
- E. Bach, *Comments on search procedures for primitive roots*, Math. Comp. 66 (1997), Lemma 2.1.
- E. Bach, *Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990), p. 292.
- Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic non-residue
  and related problems*, arXiv:1309.3595, Section 2. These are similar explicit-formula lemmas,
  with full proofs.
- A. E. Ingham, *The Distribution of Prime Numbers* (1932), p. 73. The weighted explicit
  formula for ζ.

## Target statements

For `p` prime, `χ ≠ χ₀` mod `p`, `N ≥ 1`, assuming GRH:

```
(T1)  |Σ_{n<N} Λ(n)(1 − n/N) − N/2| ≤ √N/20 + 3                     (needs RH only)
(T2)  |Σ_{n<N} Λ(n)χ(n)(1 − n/N)| ≤ c(p,N) √N log p
```

Simplification: because `p` is prime, every non-principal `χ` mod `p` is primitive, so no
reduction from imprimitive characters is needed. For `N ≤ p`, `χ₀(n) = 1` for all `0 < n < N`.

## Proof of (T2), following Bach 1997

1. **Weighted explicit formula** (Bach 1990, p. 292). For primitive non-principal χ and N ≥ 1:
   `|Σ_{n<N} Λ(n)χ(n)(1 − n/N)| ≤ (√N + 2 + 3/N) · Σ_ρ |1/(ρ(ρ+1))| + log N + 2`,
   where ρ runs over the nontrivial zeros, all with Re ρ = 1/2 under GRH.
   - Source of the bound: `Σ_{n<N} Λ(n)χ(n)(N − n) = (1/2πi) ∫_{(2)} −L'/L(s,χ) N^{s+1}/(s(s+1)) ds`.
   - Shift the contour to the far left. Residues at ρ give `−N^{ρ+1}/(ρ(ρ+1))`, with absolute
     value at most `N^{3/2}/|ρ(ρ+1)|`. Residues at s = 0, s = −1 and the trivial zeros give the
     lower-order terms.
2. **Zero-sum bound** (Bach 1997, via Lemma 6 of Bach's thesis). Under GRH, with ρ = 1/2 + iγ:
   `|ρ(ρ+1)| ≥ (3/4)|3/2 − ρ|²`, so
   `Σ_ρ |1/(ρ(ρ+1))| ≤ (4/3) Σ_ρ 1/|3/2 − ρ|² = (2/3) Σ_ρ (1/(3/2−ρ) + 1/(3/2−ρ̄)) ≤ (2/3)(log p + 5/3)`.
   The last step is the Hadamard identity at s = 3/2:
   `Re Σ_ρ 1/(s − ρ) = Re L'/L(s,χ) + ½ log(q/π) + ½ Re ψ((s + a)/2)`, with a = 0 or 1 the
   parity of χ. Then bound `|L'/L(3/2)| ≤ −ζ'/ζ(3/2)` and evaluate ψ at 3/4 or 5/4.
3. Combining 1 and 2 gives `c(p,N) = (2/3)(1 + 2/√N + 3/N^{3/2})(1 + 5/(3 log p)) + (log N + 2)/(√N log p)`.

(T1) is the same argument for ζ, which has an explicit, small zero sum:
`Σ_ρ |1/(ρ(ρ+1))| ≤ Σ_ρ (1/ρ + 1/ρ̄) = 2 + γ − log 4π < 1/20`.

## Analytic prerequisites and their status

| # | Ingredient | Mathlib (fc4f59e5) | riemann-hypothesis repo |
|---|---|---|---|
| P1 | Completed L-function, functional equation | **yes**: `completedLFunction`, `completedLFunction_one_sub` | — |
| P2 | Jensen, Borel–Carathéodory, Phragmén–Lindelöf, three lines | **yes**, all in `Analysis/Complex` | — |
| P3 | Hadamard factorization of entire functions of order 1 | no | no |
| P4 | ξ(s,χ) has order 1 (growth of Γ and of L in the strip) | partial | ? (audit pending) |
| P5 | Partial fractions for L'/L and `Σ Re 1/(s−ρ)` identity | no (needs P3) | no |
| P6 | Contour shift with kernel `x^{s+1}/(s(s+1))`, horizontal segments between zeros, left half-plane bound for L'/L via the functional equation | no | truncated explicit formula, constants existential |
| P7 | Digamma values and bounds at 3/4 and 5/4 | partial | ? |
| P8 | Zero counting in windows, `N(T+1) − N(T) ≪ log(qT)` | no | `count_zeros_window`, constant existential |

## Audit of the riemann-hypothesis repo (2026-11-22)

- **How it handles zeros.** It avoids a Hadamard product. It uses a local Landau/Jensen lemma
  (`GlobalTheory.LogDerivZeros.main`, `GI/NormOneSubConjMul.lean:130`), the strip version
  `LWide.logDeriv_LFunction_strip`, and a rectangle residue theorem
  (`ExplicitRect.residue_identity`, `ResRect.residue_rectangle`). Here
  `GI = Development/AbelianVarietyTheory/Proofs/GlobalInterpolation`.
- **Constants.** Every one is explicit inside its proof, but they multiply along the chain to
  roughly 10⁴–10⁶. That kills Route B: K that large would push the computation beyond 10²⁰.
- **Reusable.** An 18-file core of about 4,100 lines that imports only Mathlib:
  `AnalyticAtDslope`, `BdIntEqZeroOfPrimitive`, `NormOneSubConjMul`, `LogDerivLFunctionStrip`,
  `SummableNinePowMulInvSqSucc`, the Perron kernel files, `FiniteBox`, and
  `CompletedLFunctionNeZeroOfReNonpos` (trivial zeros). It provides rectangle residues, zero
  finiteness and multiplicities, and Perron-kernel calculus.
- **Missing there.** The 1/(s(s+1)) kernel, L'/L on the far left via the functional equation,
  digamma, the exact `Σ Re 1/(s−ρ)` identity, and any Hadamard factorization.

Conclusion: **Route A**, reusing the 18-file core for the contour and residue mechanics.

## Two routes

**Route A (faithful).** Build P3, P4 and P5, then P6 and P7, and get Bach's constants exactly.
P3 is a general complex-analysis library: canonical products and Hadamard's theorem via
Jensen and Borel–Carathéodory. It would be a worthwhile contribution to Mathlib in its own
right.

**Route B (no Hadamard).** Replace P3 and P5 with local partial fractions:
`L'/L(s) = Σ_{|ρ − s| ≤ 1} 1/(s − ρ) + O(log q(|t|+2))` with an explicit O. This follows from
Borel–Carathéodory plus Jensen, both already in Mathlib, applied to a convexity bound for L.
Then do the contour shift with explicit truncation errors. The constants come out worse.

Effect of a larger constant `K` in (T2) (taking the same `K` for the principal error):

| K | computation needed up to |
|---|---|
| 0.73 (Bach) | 4.3·10⁷ (done) |
| 1 | 4.1·10⁸ |
| 2 | 8.8·10⁹ |
| 3 | 2.1·10¹⁰ |
| 5 | 2.9·10¹¹ |
| 10 | 1.3·10¹² |

## Proposed milestones

1. M1: Γ and digamma facts (P7), and growth of L in the strip (P4). These are small,
   self-contained and needed by both routes.
2. M2: zero counting (P8) with explicit constants via Jensen.
3. M3: either Hadamard (Route A) or local partial fractions (Route B).
4. M4: weighted explicit formula with explicit error (P6).
5. M5: assemble (T1) and (T2); redo `Numerics.lean` for the constant obtained; extend the
   computation if needed.
