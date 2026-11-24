# Axer's bound for squarefree and k-free numbers under RH in Lean

**Literature status: RH-consequence.** Let `Q(x)` count the squarefree integers up to `x` and
`E(x) = Q(x) − (6/π²)x`. The Riemann hypothesis implies `E(x) = O(x^{2/5+ε})` for every `ε > 0`;
this is Axer's theorem (1911; the paper was not consulted, the attribution is from
Montgomery–Vaughan, *Multiplicative Number Theory I*, Exercise 13.2.1.14, via a secondary
source), whose proof is the reduction of Exercise 6.2.1.8 there (`E(x)` in terms of the Mertens
function) plus Littlewood's bound `M(x) = O(x^{1/2+ε})` under RH. Unconditionally the best known
bound is `E(x) ≪ x^{1/2−o(1)}` (Walfisz, 1963). **Better published RH-conditional exponents
exist**: `1/3`, `9/28` (Montgomery–Vaughan 1981), `8/25` (Graham 1981), `7/22` (Baker–Pintz
1985), `17/54` (Jia 1993) and `11/35` (H.-Q. Liu, *J. Number Theory* **159** (2016)), the last
being the best known. This repository proves the first of them, Axer's exponent `2/5`, and
`Unconditional/` proves `E(x) = O(x^{2/5+ε})` unconditionally in Lean, with RH supplied by the
certified proof in leanprover-community/riemann-hypothesis. **Erdős Problem 969**, which asks for
the true order of `E(x)` (probably `x^{1/4}`), stays open, also under RH.

**`k`-free numbers (literature status: RH-consequence).** For every `k ≥ 2` let `Q_k(x)` count
the `k`-free integers up to `x` and `E_k(x) = Q_k(x) − x/ζ(k)`. This repository proves in Lean
that RH implies `E_k(x) = O(x^{2/(2k+1)+ε})` for every `ε > 0` and every `k ≥ 2`, and
`Unconditional/` proves the bound unconditionally with the certified proof of RH. At `k = 2` it is
the `2/5` above. The exponent is Axer's (1911); Montgomery and Vaughan (*The distribution of
squarefree numbers*, Recent Progress in Analytic Number Theory, Vol. 1, Durham 1979, Academic
Press 1981, pp. 247–256) lowered it under RH to `1/(k+1)`. Both attributions are as quoted by
Pappalardi (*A survey on k-freeness*, 2003, §1) and Meng (arXiv:1408.0429, §1). The
Montgomery–Vaughan exponent is stated here as the target `MontgomeryVaughanBound`; the gap is
measured in "Deviations from the literature". Unconditionally,
`E_k(x) ≪ x^{1/k} exp(−c k^{−8/5} (log x)^{3/5} (log log x)^{−1/5})` (Walfisz 1963, as quoted by
Meng).

The main library is a complete Lean proof that RH implies Axer's bound, following Axer (1911):

```lean
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

-- consistency: at k = 2 the new target is the old one
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

-- the Montgomery–Vaughan target (not yet proved here)
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
| `Erdos969.squarefreeError_le` | C | `MBound K α`: `M(k)` bounded by `K (k+1)^α` in absolute value, a bound on the Mertens function (it is a hypothesis; for `α < 1` it is known only under RH, so this is a reduction, not an unconditional result) | Montgomery–Vaughan, Ex. 6.2.1.8 |
| `Erdos969.axer_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) | RH-consequence (Axer 1911) |
| `Erdos969.erdos_969_prime_number_theorem_of_RH` | C | `RiemannHypothesis` | known, via GRH here (see below) |
| `axer_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis | RH-consequence |
| `Erdos969.KFree.kFreeError_le` | C | `MBound K α`, as above | Axer's reduction for `k`-free numbers |
| `Erdos969.KFree.axerKFree_of_RH` | C | `RiemannHypothesis` | RH-consequence (Axer 1911) |
| `Erdos969.KFree.axerKFreeBound_two_iff` | D | none (ties the `k`-free definitions to the squarefree ones) | — |
| `axerKFree_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis | RH-consequence |
| `MontgomeryVaughanBound k` | target, not proved | — | RH-consequence (Montgomery–Vaughan 1981) |

`squarefreeCounting` and `squarefreeCountingError` are copied word for word from
google-deepmind/formal-conjectures,
[`FormalConjectures/ErdosProblems/969.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/ErdosProblems/969.lean)
(commit `86a2f58a`). That file has no RH-conditional statement, so `AxerBound` is this repository's
own. `Powerfree` is copied word for word from formal-conjectures,
[`FormalConjecturesForMathlib/Algebra/Powerfree.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjecturesForMathlib/Algebra/Powerfree.lean)
(commit `9097e2f9`), placed in the `Erdos969` namespace; formal-conjectures has no statement on
the count of `k`-free numbers, so `kFreeCounting`, `kFreeCountingError`, `AxerKFreeBound` and
`MontgomeryVaughanBound` are this repository's own. The main library takes RH as a hypothesis and never imports riemann-hypothesis. The Mertens
bound comes from [mertens-rh](https://github.com/senamakel/mertens-rh) (`98c6eab`,
`Mertens.abs_mertens_nat_le`), which proves it from RH.

**The `E = o(√x)` corollary is a known theorem.** It is the conclusion of the formal-conjectures
variant `erdos_969.variants.prime_number_theorem` (marked `research solved` there, via the prime
number theorem). Our proof goes through RH and is the weaker one; it is stated here because it
falls out of `axer_of_RH` with `ε = 1/20`. No other formal-conjectures statement is settled.

## Axioms

`scripts/check-axioms.sh` (`lake env lean` on a file with `#print axioms` after `import Erdos969`):

```
'Erdos969.squarefreeError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.axer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.erdos_969_prime_number_theorem_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.KFree.kFreeError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.KFree.axerKFree_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos969.KFree.axerKFreeBound_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no `axiom` declarations, no finite computation.

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

## Layout

| File | Content |
|---|---|
| `Erdos969/Statement.lean` | Target definitions (fixed) |
| `Erdos969/Identity.lean` | Step 1 |
| `Erdos969/Series.lean` | Step 2 |
| `Erdos969/Hyperbola.lean` | Step 3 |
| `Erdos969/Main.lean` | Steps 4–5, headline theorems |
| `Erdos969/Statement2.lean` | `k`-free target definitions (fixed) |
| `Erdos969/KFree/Identity.lean` | `Q_k(N) = ∑ μ(d)⌊N/d^k⌋`; the `k = 2` consistency lemmas |
| `Erdos969/KFree/Series.lean` | `∑ μ(n)/n^k = 1/ζ(k)` and its tail |
| `Erdos969/KFree/Hyperbola.lean` | Hyperbola split with integer `k`-th roots |
| `Erdos969/KFree/Main.lean` | `k`-free headline theorems |
| `Unconditional/Erdos969Unconditional.lean` | One-line discharge from riemann-hypothesis |

## Deviations from the literature

**Exponent `2/5`, not `11/35`.** The method gives `1/(3−α)` from `M(x) ≪ x^α`, which is `2/5` at
`α = 1/2`. Every better published exponent needs exponential-sum estimates (a truncated Fourier
expansion of the sawtooth function, van der Corput's method, exponent pairs, a Vaughan-type
decomposition of `μ`), none of which is in Mathlib. The order `x^{1/4}` that would settle
Erdős 969 is not known under RH by any method.

**`k`-free numbers: exponent `2/(2k+1)`; Montgomery–Vaughan have `1/(k+1)`.** The gap is in
the `d > Y` part, `∑_{Y<d} μ(d)⌊x/d^k⌋ − x ∑_{d>Y} μ(d)/d^k`. At the balancing point
`Y = x^{1/(k+1)}` the `m`-range of the hyperbola sum is `m ≤ X = x/Y^k = Y`, and both the
hyperbola sum `∑_{m ≤ X} (M((x/m)^{1/k}) − M(Y))` and the scaled series tail must be
`O(x^{1/(k+1)+ε})`. Bounding each `M` separately by `M(t) ≪ t^{1/2+ε}`, as here, gives
`x^{1/(2k)} X^{1−1/(2k)}` and `x Y^{1/2−k}`, both `x^{3/(2(k+1))}`: a factor `x^{1/(2(k+1))}`
too large. So the `d > Y` part needs square-root cancellation on average over `m`, which no
pointwise bound on `M` supplies. The Montgomery–Vaughan paper was not available here, so the
route below is our reconstruction, not their argument: write that part as a Perron integral of
`(∑_{m ≤ X} m^{−s}) · ∑_{d > Y} μ(d) d^{−ks}` and use RH through `1/ζ(σ+it) ≪ |t|^ε` for
`σ > 1/2` together with a mean-value estimate for the Dirichlet polynomial. In Lean that needs a
truncated Perron formula with an explicit error term and a mean-value theorem for Dirichlet
polynomials; neither is in Mathlib at this pin. `1/ζ ≪ |t|^ε` is in mertens-rh
(`invZeta_bound_of_RH`). `k = 2` (exponent `1/3`) needs the same input.

**`x^{2/5+ε}`, not `x^{2/5}`.** The Mertens bound `M(x) = O(x^{1/2+ε})` costs an `ε`, which
passes to the exponent. Whether the textbook exercise has an `ε` or a logarithm was not checked.

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
average about 80, each in under 40 s.

## Unconditional version

`Unconditional/Erdos969Unconditional.lean` proves Axer's bounds, for squarefree and for
`k`-free numbers, with no hypothesis. It imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and discharges the hypothesis with `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `axer_unconditional` | `Erdos969.AxerBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `axerKFree_unconditional` | `∀ k, 2 ≤ k → Erdos969.AxerKFreeBound k` | `propext`, `Classical.choice`, `Quot.sound` |

```
scripts/check-unconditional.sh [RH_DIR]
```

Run on 2026-11-24 against riemann-hypothesis `507a75d91d` (cache build, not `RH_FULL_BUILD`),
library and `Unconditional/` as of erdos-969 commit `13e153c`; 27 min wall, most of it waiting
for and loading the RH cache. Output:

```
'axer_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'axerKFree_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `ulimit -n 2000000` or `nofile` in `/etc/security/limits.conf`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* [erdos-985](https://github.com/senamakel/erdos-985) (`9538edb`) and
  [lindelof-rh](https://github.com/senamakel/lindelof-rh) (`9165bfe`), lake dependencies through
  mertens-rh. Same author, no licence file yet.
* [mertens-rh](https://github.com/senamakel/mertens-rh) (`98c6eab`): `Mertens.abs_mertens_nat_le`
  and `Mertens.abel_identity`. Same author.
* `squarefreeCounting` and `squarefreeCountingError`: google-deepmind/formal-conjectures, commit
  `86a2f58a`, Apache License 2.0.
* `Powerfree` (the definition only): google-deepmind/formal-conjectures,
  `FormalConjecturesForMathlib/Algebra/Powerfree.lean`, commit `9097e2f9`, Apache License 2.0.
* Nothing is vendored from riemann-hypothesis, Woett/Lean-files or PrimeNumberTheoremAnd; the
  identity `Q(N) = ∑ μ(d) ⌊N/d²⌋` is reproved here from Mathlib.
