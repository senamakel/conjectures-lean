# Montgomery–Vaughan's bound for squarefree and k-free numbers under RH in Lean

Let `Q_k(x)` count the `k`-free integers up to `x` and `E_k(x) = Q_k(x) − x/ζ(k)`. For `k = 2`,
`Q = Q_2` counts the squarefree integers and `E(x) = Q(x) − (6/π²)x`. This repository proves in
Lean that RH implies Montgomery and Vaughan's bound `E_k(x) = O(x^{1/(k+1)+ε})` for every
`k ≥ 2` and every `ε > 0`, and in particular `E(x) = O(x^{1/3+ε})` for squarefree numbers
(`MV.montgomeryVaughan_of_RH`, `MV.squarefreeError_mv_of_RH`). `Unconditional/` closes the
hypothesis with the certified proof of RH in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
so `montgomeryVaughan_unconditional` and `squarefreeError_mv_unconditional` prove both bounds
unconditionally in Lean. The library also proves Axer's earlier bounds `E(x) = O(x^{2/5+ε})`
and `E_k(x) = O(x^{2/(2k+1)+ε})`, with RH as a hypothesis and unconditionally.

**Status in the literature.** RH-consequence. The bound `1/(k+1)` is Montgomery and Vaughan's,
*The distribution of squarefree numbers*, Recent Progress in Analytic Number Theory, Vol. 1
(Durham 1979), Academic Press 1981, pp. 247-256, as quoted by Pappalardi (*A survey on
k-freeness*, 2003, §1) and Meng (arXiv:1408.0429, §1). The shape of their argument (Theorem 1,
the Dirichlet series `ζ(s) ∑_{d>y} μ(d) d^{-ks}` and RH bounds for `ζ` and `1/ζ`) is taken from
K. J. Powell, *Topics in Analytic Number Theory* (BYU thesis, 2009), §2; the 1981 paper was not
read. Axer's exponents (1911, also RH-consequences) are attributed through Montgomery–Vaughan,
*Multiplicative Number Theory I*, Exercise 13.2.1.14, read through a secondary source, and
proved by the reduction of Exercise 6.2.1.8 there plus Littlewood's bound
`M(x) = O(x^{1/2+ε})` under RH. The proof of RH is L. Alpöge's, certified by the Lean FRO and
the Mathlib Initiative on 2026-11-21. Unconditionally the best known bounds are
`E(x) ≪ x^{1/2−o(1)}` and
`E_k(x) ≪ x^{1/k} exp(−c k^{−8/5} (log x)^{3/5} (log log x)^{−1/5})` (Walfisz 1963, the second as
quoted by Meng). Erdős Problem 969 asks for the true order of `E(x)` (probably `x^{1/4}`). It is
open under RH as well, and these bounds do not settle it.

The main library is a complete Lean proof that RH implies these bounds, following
Montgomery–Vaughan (1981) and Axer (1911):

```lean
-- Unconditional/Erdos969Unconditional.lean
theorem montgomeryVaughan_unconditional {k : ℕ} (hk : 2 ≤ k) :
    Erdos969.MontgomeryVaughanBound k
theorem squarefreeError_mv_unconditional :
    ∀ ε : ℝ, 0 < ε → (fun x : ℕ => |Erdos969.squarefreeCountingError x|) =O[Filter.atTop]
      fun x : ℕ => (x : ℝ) ^ (1 / 3 + ε)
theorem axer_unconditional : Erdos969.AxerBound
theorem axerKFree_unconditional {k : ℕ} (hk : 2 ≤ k) : Erdos969.AxerKFreeBound k

-- Montgomery–Vaughan (Erdos969/MV/Main.lean)
theorem Erdos969.MV.montgomeryVaughan_of_RH (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) :
    Erdos969.MontgomeryVaughanBound k
theorem Erdos969.MV.squarefreeError_mv_of_RH (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → (fun x : ℕ => |Erdos969.squarefreeCountingError x|) =O[Filter.atTop]
      fun x : ℕ => (x : ℝ) ^ (1 / 3 + ε)

-- the explicit form: for 1 ≤ Y ≤ N, |E_k(N)| ≤ Y + C Y^{1/2+3ε-k(1/2+ε)} (N+1)^{1/2+5ε}
theorem Erdos969.MV.abs_error_le_mv (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 12) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ Y : ℕ, 1 ≤ Y → Y ≤ N →
      |Erdos969.kFreeCountingError k N| ≤
        Y + C * (Y : ℝ) ^ (1 / 2 + 3 * ε - k * (1 / 2 + ε)) * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε)

-- RH inputs proved on the way (Erdos969/MV/Twisted.lean)
theorem Erdos969.MV.twisted_mertens (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (N : ℕ), 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        K * (|t| + 2) ^ ε * ((N : ℝ) + 1) ^ (1 / 2 + 3 * ε)
theorem Erdos969.MV.tail_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) :
    ∃ K : ℝ, 0 < K ∧ ∀ (σ t : ℝ), 1 < σ → 1 / 2 + 3 * ε < σ → ∀ Y : ℕ, 1 ≤ Y →
      ‖Mertens.invZ ((σ : ℂ) + t * I) -
          ∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤
        K * (1 + σ / (σ - (1 / 2 + 3 * ε))) * (|t| + 2) ^ ε * (Y : ℝ) ^ (1 / 2 + 3 * ε - σ)

theorem Erdos969.axer_of_RH (hRH : RiemannHypothesis) : Erdos969.AxerBound

-- the intermediate reduction, with no RH: a Mertens exponent α gives the exponent 1/(3-α)
theorem Erdos969.squarefreeError_le {K α : ℝ} (hα0 : 0 ≤ α) (hα2 : α < 2)
    (hM : Erdos969.MBound K α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |Erdos969.squarefreeCountingError N| ≤ C * (N : ℝ) ^ (1 / (3 - α))

-- a free corollary under RH
theorem Erdos969.erdos_969_prime_number_theorem_of_RH (hRH : RiemannHypothesis) :
    (fun x => |Erdos969.squarefreeCountingError x|) =o[Filter.atTop] (fun x : ℕ => (x : ℝ).sqrt)

-- k-free numbers, every k ≥ 2 (Erdos969/KFree/Main.lean)
theorem Erdos969.KFree.axerKFree_of_RH (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) :
    Erdos969.AxerKFreeBound k

-- the reduction, with no RH: a Mertens exponent α < k gives the exponent 1/(k+1-α)
theorem Erdos969.KFree.kFreeError_le {k : ℕ} (hk : 2 ≤ k) {K α : ℝ} (hα0 : 0 ≤ α) (hαk : α < k)
    (hM : Erdos969.MBound K α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |Erdos969.kFreeCountingError k N| ≤ C * (N : ℝ) ^ (1 / ((k : ℝ) + 1 - α))

-- consistency: at k = 2 the k-free target is the squarefree one
theorem Erdos969.KFree.axerKFreeBound_two_iff : Erdos969.AxerKFreeBound 2 ↔ Erdos969.AxerBound
```

The targets, fixed in `Erdos969/Statement.lean`:

```lean
def squarefreeCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter Squarefree).card

noncomputable def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x

def AxerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => |squarefreeCountingError x|) =O[atTop] fun x : ℕ => (x : ℝ) ^ (2 / 5 + ε)
```

and, for `k`-free numbers, in `Erdos969/Statement2.lean`:

```lean
def Powerfree (k : ℕ) (m : M) : Prop :=
  ∀ ⦃x : M⦄, x ^ k ∣ m → IsUnit x

noncomputable def kFreeCounting (k x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (Powerfree k)).card

noncomputable def kFreeCountingError (k x : ℕ) : ℝ :=
  (kFreeCounting k x : ℝ) - x / (riemannZeta k).re

def AxerKFreeBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => |kFreeCountingError k x|) =O[atTop]
      fun x : ℕ => (x : ℝ) ^ (2 / (2 * (k : ℝ) + 1) + ε)

-- the Montgomery–Vaughan target (proved: Erdos969.MV.montgomeryVaughan_of_RH)
def MontgomeryVaughanBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => |kFreeCountingError k x|) =O[atTop]
      fun x : ℕ => (x : ℝ) ^ (1 / ((k : ℝ) + 1) + ε)
```

`(riemannZeta k).re` is `ζ(k)`: for an integer `k ≥ 2` the value is real
(`KFree.hasSum_moebius_pow` proves `∑ μ(n)/n^k = 1/(riemannZeta k).re`).

## Tier and provenance

| Theorem | Tier | Hypothesis | Literature |
|---|---|---|---|
| `Erdos969.squarefreeError_le` | C | `MBound K α`: `\|M(k)\| ≤ K (k+1)^α`, a bound on the Mertens function; for `α < 1` it is known only under RH | Montgomery–Vaughan, Ex. 6.2.1.8 |
| `Erdos969.axer_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) | RH-consequence (Axer 1911) |
| `Erdos969.erdos_969_prime_number_theorem_of_RH` | C | `RiemannHypothesis` | known, via GRH here (see below) |
| `axer_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis | RH-consequence |
| `Erdos969.KFree.kFreeError_le` | C | `MBound K α`, as above | Axer's reduction for `k`-free numbers |
| `Erdos969.KFree.axerKFree_of_RH` | C | `RiemannHypothesis` | RH-consequence (Axer 1911) |
| `Erdos969.KFree.axerKFreeBound_two_iff` | D | none (ties the `k`-free definitions to the squarefree ones) | none |
| `axerKFree_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis | RH-consequence |
| `Erdos969.MV.twisted_mertens` | C | `RiemannHypothesis` | Littlewood's bound for `μ(n)n^{-it}`, uniform in `t` (a step, not a target) |
| `Erdos969.MV.tail_le` | C | `RiemannHypothesis` | the tail of `1/ζ` on `σ > 1` (a step) |
| `Erdos969.MV.abs_error_le_mv` | C | `RiemannHypothesis` | Montgomery–Vaughan's Theorem 1, in the form used |
| `Erdos969.MV.montgomeryVaughan_of_RH` | C | `RiemannHypothesis` | RH-consequence (Montgomery–Vaughan 1981) |
| `Erdos969.MV.squarefreeError_mv_of_RH` | C | `RiemannHypothesis` | RH-consequence (Montgomery–Vaughan 1981, `k = 2`) |
| `montgomeryVaughan_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis | RH-consequence |
| `squarefreeError_mv_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis | RH-consequence |

`squarefreeCounting` and `squarefreeCountingError` are copied word for word from
google-deepmind/formal-conjectures,
[`FormalConjectures/ErdosProblems/969.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/ErdosProblems/969.lean)
(commit `86a2f58a`). That file has no RH-conditional statement, so `AxerBound` is this repository's
own. `Powerfree` is copied word for word from formal-conjectures,
[`FormalConjecturesForMathlib/Algebra/Powerfree.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjecturesForMathlib/Algebra/Powerfree.lean)
(commit `9097e2f9`), placed in the `Erdos969` namespace; formal-conjectures has no statement on
the count of `k`-free numbers, so `kFreeCounting`, `kFreeCountingError`, `AxerKFreeBound` and
`MontgomeryVaughanBound` are this repository's own. The main library takes RH as a hypothesis
and never imports riemann-hypothesis. The Mertens bound comes from
[mertens-rh](../mertens-rh/) (`98c6eab`,
`Mertens.abs_mertens_nat_le`), which proves it from RH. The Montgomery–Vaughan proof uses
mertens-rh's `1/ζ ≪ |t|^ε` (`Mertens.norm_invZ_le`), its contour shift and Cesàro-difference
lemmas, erdos-985's weighted Perron formula, and lindelof-rh's logarithm of `ζ` (for
`ζ ≪ |t|^ε` on `σ ≥ 1/2 + δ`), all at the pins already required.

The corollary `E = o(√x)` is the conclusion of the formal-conjectures variant
`erdos_969.variants.prime_number_theorem` (marked `research solved` there, via the prime number
theorem), so its label is *known, via GRH here*: this repository proves it through RH, as
`axer_of_RH` with `ε = 1/20`, and it is also a theorem by other means. No other
formal-conjectures statement on Erdős 969 is settled here.

## Axioms

`scripts/check-axioms.sh` (`lake env lean` on a file with `#print axioms` after `import Erdos969`):

```
'Erdos969.squarefreeError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.axer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.erdos_969_prime_number_theorem_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.KFree.kFreeError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.KFree.axerKFree_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.KFree.axerKFreeBound_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.MV.twisted_mertens' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.MV.tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.MV.abs_error_le_mv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.MV.montgomeryVaughan_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.MV.squarefreeError_mv_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository has no `sorry`, no `native_decide`, no `axiom` declarations and no finite
computation.

## Proof outline

The full plan is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

1. `Q(N) = ∑_{d ≤ N} μ(d) ⌊N/d²⌋`, from `∑_{d² ∣ n} μ(d) = [n squarefree]`
   (`Erdos969/Identity.lean`).
2. `∑ μ(n)/n² = 6/π²`, and for `|M(k)| ≤ K (k+1)^α`, `0 ≤ α < 2`: the tail
   `|6/π² − ∑_{d ≤ Y} μ(d)/d²| ≤ C Y^{α−2}`, by Abel summation (`Erdos969/Series.lean`).
3. Hyperbola split: `∑_{Y<d≤N} μ(d)⌊N/d²⌋ = ∑_{m} ∑_{Y<d≤⌊√(N/m)⌋} μ(d)`, bounded by
   `C N Y^{α−2}` using `M` at `⌊√(N/m)⌋` (`Erdos969/Hyperbola.lean`).
4. `|E(N)| ≤ Y + C N Y^{α−2}`; take `Y ≍ N^{1/(3−α)}` (`Erdos969/Main.lean`).
5. Under RH, `α = 1/2 + 3ε'` and `1/(3−α) ≤ 2/5 + ε'` for `ε' ≤ 1/12`.
6. `k`-free numbers (`Erdos969/KFree/`), the same five steps with `d²` replaced by `d^k`:
   `Q_k(N) = ∑ μ(d)⌊N/d^k⌋` (the `d` with `d^k ∣ n` are the divisors of Mathlib's
   `Nat.floorRoot k n`); `|1/ζ(k) − ∑_{d≤Y} μ(d)/d^k| ≤ C Y^{α−k}` (weights
   `|1/(u+1)^k − 1/u^k| ≤ k/u^{k+1}`); the hyperbola split over `Y < d ≤ ⌊(N/m)^{1/k}⌋`
   gives `C N Y^{α−k}`; `|E_k(N)| ≤ Y + C N Y^{α−k}`, `Y ≍ N^{1/(k+1−α)}`. Under RH,
   `α = 1/2 + ε'` and `1/(k+1/2−ε') ≤ 2/(2k+1) + ε'` for `ε' ≤ 1/12`.
7. Montgomery–Vaughan (`Erdos969/MV/`). Split at `Y`:
   `E_k(N) = −∑_{d≤Y} μ(d){N/d^k} + B(N)`, `B(N) = ∑_{Y<d≤N} μ(d)⌊N/d^k⌋ − N ∑_{d>Y} μ(d)/d^k`.
   The first sum is at most `Y`. `B(N) = ∑_{n≤N} a(n)` where `a = h * 1 − G_Y(k)`, `h(d^k) = μ(d)`
   for `d > Y` (`MV/Coeff.lean`), and `L(a, s) = ζ(s)(G_Y(ks) − G_Y(k))` with
   `G_Y(w) = 1/ζ(w) − ∑_{d≤Y} μ(d)d^{-w}`: subtracting the constant `G_Y(k)` cancels the pole of
   `ζ` at `1`, so `Φ(s) = ζ₁(s)·dslope (G_Y(k·)) 1 s` is holomorphic on `σ > 1/(2k)` and no
   residue is computed. A Cesàro–Perron bound (`MV/Perron.lean`, mertens-rh's proof of
   Littlewood's theorem with `1/ζ` replaced by any `Φ`) gives
   `‖∑_{n≤N} a(n)‖ ≤ K A (N+1)^{σ₀+2ε}` whenever `‖Φ(σ₀+it)‖ ≤ A(|t|+2)^ε`: the sharp sum is the
   difference of the Cesàro means at `N+1` and `N`, and no truncated Perron formula is needed.
   On `σ₀ = 1/2 + ε`, `‖ζ‖ ≪ (|t|+2)^ε` (`MV/Twisted.lean`, lindelof-rh's logarithm of `ζ`) and
   `‖G_Y(k(σ₀+it))‖ ≪ (|t|+2)^ε Y^{1/2+3ε−kσ₀}` (`tail_le`): partial summation against the real
   weights `d^{−kσ₀}` of the twisted sums `∑_{n≤u} μ(n)n^{−ikt} ≪ (|t|+2)^ε u^{1/2+3ε}`
   (`twisted_mertens`, the Cesàro–Perron bound for `Φ(s) = 1/ζ(s + ikt)`). So
   `|E_k(N)| ≤ Y + C Y^{(1−k)/2+(3−k)ε} N^{1/2+5ε}`, and `Y = ⌈N^{1/(k+1)}⌉` gives
   `N^{1/(k+1)+6ε}` (`MV/Main.lean`). This is Montgomery–Vaughan's Theorem 1 with the sawtooth
   sum bounded trivially by `Y`.

Montgomery and Vaughan apply a Perron formula to
`ζ(s)∑_{d>y} μ(d)d^{−ks}` and compute residues (as summarised by Powell 2009). This repository
uses a Cesàro-weighted Perron formula instead, takes the difference of the means at `N+1` and
`N` to recover the sharp sum, removes the pole at `s = 1` by subtracting the constant
`G_Y(k)` from the coefficients, and gets the uniform bound for the tail of `1/ζ` from a twisted
Littlewood bound plus partial summation. The theorem proved is the same; the constants are
existential.

## Layout

| File | Content |
|---|---|
| `Erdos969/Statement.lean` | Target definitions (fixed) |
| `Erdos969/Identity.lean` | Step 1 |
| `Erdos969/Series.lean` | Step 2 |
| `Erdos969/Hyperbola.lean` | Step 3 |
| `Erdos969/Main.lean` | Steps 4 and 5, headline theorems |
| `Erdos969/Statement2.lean` | `k`-free target definitions (fixed) |
| `Erdos969/KFree/Identity.lean` | `Q_k(N) = ∑ μ(d)⌊N/d^k⌋`; the `k = 2` consistency lemmas |
| `Erdos969/KFree/Series.lean` | `∑ μ(n)/n^k = 1/ζ(k)` and its tail |
| `Erdos969/KFree/Hyperbola.lean` | Hyperbola split with integer `k`-th roots |
| `Erdos969/KFree/Main.lean` | `k`-free headline theorems (Axer) |
| `Erdos969/MV/Perron.lean` | Cesàro–Perron bound for partial sums of a Dirichlet series |
| `Erdos969/MV/Twisted.lean` | `ζ`, `1/ζ` bounds on vertical lines; `twisted_mertens`; `tail_le` |
| `Erdos969/MV/Coeff.lean` | the coefficients of `ζ(s) G_Y(ks)` and their partial sums |
| `Erdos969/MV/Main.lean` | Montgomery–Vaughan headline theorems |
| `Unconditional/Erdos969Unconditional.lean` | One-line discharge from riemann-hypothesis |

## Deviations from the literature

For squarefree numbers this repository proves the exponent `1/3`, the `k = 2` case of
Montgomery–Vaughan's general bound. In the same paper Montgomery and Vaughan reach `9/28` for
`k = 2` by bounding the sawtooth sum `∑_{d≤Y} μ(d)ψ(x/d²)` with exponential sums. Later RH
exponents are `8/25` (Graham 1981), `7/22` (Baker–Pintz 1985), `17/54` (Jia 1993) and `11/35`
(H.-Q. Liu, *J. Number Theory* 159 (2016)), the best known; for `k ≥ 3`, Graham–Pintz and
Baker–Powell improve on `1/(k+1)`. All of these work on the same sawtooth sum, which is bounded
trivially by `Y` here. They need a truncated Fourier expansion of `ψ` and van der Corput or
exponent-pair estimates, which Mathlib does not have at this pin. No method gives the order
`x^{1/4}` under RH.

Every bound here carries `+ε` in the exponent, because the Mertens bound
`M(x) = O(x^{1/2+ε})` does, and every constant is existential. For Axer's `x^{2/5+ε}`, whether
the textbook exercise states it with an `ε` or with a power of `log x` was not checked.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb` and mertens-rh `98c6eab`).

```
lake exe cache get
lake build            # target `Erdos969`
```

A clean build of the four `Erdos969` modules (mertens-rh and erdos-985 already built) took about
7 min wall on a box at load average over 200 (about 130 s for `Identity`, 140 s for `Series`,
75 s for `Hyperbola`, 60 s for `Main`; most of that was queueing). No module is expensive.
The five `k`-free modules (`Statement2`, `KFree.*`) built one at a time on 2026-11-24 at load
average about 80, each in under 40 s. The four `MV.*` modules built one at a time on
2026-11-24 at load average about 75, each in 11 to 35 s; `lake build` of the whole library with
everything else cached took 34 s wall.

## Unconditional version

`Unconditional/Erdos969Unconditional.lean` proves Montgomery–Vaughan's and Axer's bounds, for
squarefree and for `k`-free numbers, with no hypothesis. It imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and discharges the hypothesis with `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `axer_unconditional` | `Erdos969.AxerBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `axerKFree_unconditional` | `∀ k, 2 ≤ k → Erdos969.AxerKFreeBound k` | `propext`, `Classical.choice`, `Quot.sound` |
| `montgomeryVaughan_unconditional` | `∀ k, 2 ≤ k → Erdos969.MontgomeryVaughanBound k` | `propext`, `Classical.choice`, `Quot.sound` |
| `squarefreeError_mv_unconditional` | `E(x) = O(x^{1/3+ε})` for every `ε > 0` | `propext`, `Classical.choice`, `Quot.sound` |

```
scripts/check-unconditional.sh [RH_DIR]
```

Run on 2026-11-24 against riemann-hypothesis `507a75d91d` (cache build, not `RH_FULL_BUILD`),
library and `Unconditional/` as of erdos-969 commit `79aa3ec`; 13 min wall, most of it waiting
for and loading the RH cache. Output:

```
'axer_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'axerKFree_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomeryVaughan_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'squarefreeError_mv_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `ulimit -n 2000000` or `nofile` in `/etc/security/limits.conf`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* [erdos-985](../erdos-985/) (`9538edb`) and
  [lindelof-rh](../lindelof-rh/) (`9165bfe`), lake dependencies through
  mertens-rh. Same author, no licence file yet.
* [mertens-rh](../mertens-rh/) (`98c6eab`): `Mertens.abs_mertens_nat_le`,
  `Mertens.abel_identity`, and for `Erdos969/MV/` the lemmas `norm_invZ_le`,
  `integral_vertical_eq_of_strip`, `norm_diff_le_mvt`, `norm_diff_le_triv`, `le_rpow_mul_rpow`
  (used, not copied); `MV/Perron.lean` and `norm_zeta_le_strip` follow the structure of its
  `Littlewood.lean` and `InvZeta.lean`. Same author.
* `squarefreeCounting` and `squarefreeCountingError`: google-deepmind/formal-conjectures, commit
  `86a2f58a`, Apache License 2.0.
* `Powerfree` (the definition only): google-deepmind/formal-conjectures,
  `FormalConjecturesForMathlib/Algebra/Powerfree.lean`, commit `9097e2f9`, Apache License 2.0.
* Nothing is vendored from riemann-hypothesis, Woett/Lean-files or PrimeNumberTheoremAnd; the
  identity `Q(N) = ∑ μ(d) ⌊N/d²⌋` is reproved here from Mathlib.
