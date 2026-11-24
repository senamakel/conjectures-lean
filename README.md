# Cramér's prime-gap and mean-square theorems under RH in Lean

This repository proves in Lean, with the explicit hypothesis `RiemannHypothesis`, two theorems of
Cramér, and proves both unconditionally in `Unconditional/` with the certified Lean proof of RH
(L. Alpöge, 2026):

* **prime gaps** (Cramér 1920, *Arkiv för Matematik, Astronomi och Fysik* **15**, no. 5):
  every interval `(x, x + 2√x log x]` with `x ≥ 2` contains a prime, so
  `p_{n+1} − p_n ≤ 2√p_n log p_n` and `p_{n+1} − p_n = O(√p_n log p_n)`;
* **the mean square of `ψ(x) − x`** (Cramér 1922, *Ein Mittelwertsatz in der Primzahltheorie*,
  *Math. Z.* **12**, 147–153; Montgomery–Vaughan, *Multiplicative Number Theory I*, Thm 13.5):
  `∫_X^{2X} (ψ(x) − x)² dx ≪ X²`, `∫_1^X (ψ(x) − x)² dx ≪ X²` and
  `∫_1^X ((ψ(x) − x)/x)² dx ≪ log X`.

**Literature status: RH-consequence** for both. The prime-gap bound is Cramér's; explicit forms
are due to Dudek (2015, *Int. J. Number Theory* **11**, 771–778) and
Carneiro–Milinovich–Soundararajan (2019, *Comment. Math. Helv.* **94**, 533–568), who reach
`p_{n+1} − p_n < (22/25) √p_n log p_n` for `p_n > 3` (our constant is `2`, see "Deviations").
Without RH the best gap exponent is Baker–Harman–Pintz (2001), `O(p_n^{0.525})`. The mean-square
bound is Cramér's; Brent–Platt–Trudgian (2022, *J. Number Theory* **238**, 740–762) give the
constant `0.8603` for `lim sup X^{-2} ∫_X^{2X}`, and Montgomery–Vaughan (Thm 13.6, Ex. 13.1.1.3)
the asymptotic `∫_1^X ((ψ − x)/x)² ∼ (Σ_ρ m_ρ/|ρ|²) log X`. This is Cramér's theorem, not his
1936 conjecture `p_{n+1} − p_n = O(log² p_n)`.

The main library is a complete Lean proof that RH implies Cramér's bounds. The gap bound follows
Cramér (1920) through a triangular (Fejér-type) weight, the second difference of `ψ₁`. The mean
square follows the classical route through the explicit formula and the convergence of
`Σ_ρ log|γ|/|ρ|²`:

```lean
theorem Cramer.primeInShortInterval_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInShortInterval 2

theorem Cramer.primeGapExplicit_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeGapExplicit 2

theorem Cramer.cramer_of_RH (hRH : RiemannHypothesis) : Cramer.CramerGapBound

theorem Cramer.dyadicMeanSquare_of_RH (hRH : RiemannHypothesis) :
    Cramer.CramerDyadicMeanSquare

theorem Cramer.meanSquare_of_RH (hRH : RiemannHypothesis) : Cramer.CramerMeanSquare

theorem Cramer.logMeanSquare_of_RH (hRH : RiemannHypothesis) : Cramer.CramerLogMeanSquare
```

The targets, fixed in `Cramer/Statement.lean`:

```lean
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

def CramerGapBound : Prop :=
  (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n))

def PrimeInShortInterval (c : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + c * Real.sqrt x * Real.log x

def PrimeGapExplicit (c : ℝ) : Prop :=
  ∀ n : ℕ, (primeGap n : ℝ) ≤
    c * Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)
```

The mean-square targets, fixed in `Cramer/Statement2.lean` (`ψ` is Mathlib's `Chebyshev.psi`,
`ψ x = Σ_{0 < n ≤ x} Λ(n)`):

```lean
def CramerDyadicMeanSquare : Prop :=
  (fun X : ℝ => ∫ x in X..2 * X, (ψ x - x) ^ 2) =O[Filter.atTop] (fun X : ℝ => X ^ 2)

def CramerMeanSquare : Prop :=
  (fun X : ℝ => ∫ x in (1 : ℝ)..X, (ψ x - x) ^ 2) =O[Filter.atTop] (fun X : ℝ => X ^ 2)

def CramerLogMeanSquare : Prop :=
  (fun X : ℝ => ∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2) =O[Filter.atTop] Real.log
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Cramer.primeInShortInterval_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `Cramer.primeGapExplicit_of_RH` | C | `RiemannHypothesis` |
| `Cramer.cramer_of_RH` | C | `RiemannHypothesis` |
| `cramer_primeInShortInterval` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_primeGapExplicit` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_gapBound` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `Cramer.dyadicMeanSquare_of_RH` | C | `RiemannHypothesis` |
| `Cramer.meanSquare_of_RH` | C | `RiemannHypothesis` |
| `Cramer.logMeanSquare_of_RH` | C | `RiemannHypothesis` |
| `cramer_dyadicMeanSquare` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_meanSquare` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_logMeanSquare` (`Unconditional/`) | U | none; RH from riemann-hypothesis |

`primeGap` is copied word for word from google-deepmind/formal-conjectures,
[`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean),
and `CramerGapBound` is the conclusion of `cramer_conjecture.variants.conditional_rh` in
[`FormalConjectures/Wikipedia/CramerConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/CramerConjecture.lean)
(commit `86a2f58a`), whose hypothesis is Mathlib's `RiemannHypothesis`, as here. The explicit
forms `PrimeInShortInterval` and `PrimeGapExplicit` are this repository's own, and so are the
three mean-square statements: formal-conjectures has no mean-square statement for `ψ`
(searched 2026-11-24 at `9097e2f9`). The main library
takes RH as a hypothesis and never imports riemann-hypothesis. No cited-hypothesis (tier H)
inputs: the range below the gap theorem's analytic threshold is checked in Lean, and the
mean-square proof uses erdos-233's real-`x` explicit formula and zero-density lemma, both proved
there from Mathlib and erdos-985.

## Axioms

`lake env lean` on a file with `#print axioms` after `import Cramer`:

```
'Cramer.primeInShortInterval_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeGapExplicit_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.cramer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.dyadicMeanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.meanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.logMeanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/check-axioms.sh` reruns this and fails unless all six use only the standard axioms.
No `sorry`, no `native_decide`, no `axiom` declarations. The finite check (`Cramer/Small.lean`)
uses kernel `decide` and `norm_num`, which add no axioms.

## Proof outline

The full plan, with every intermediate statement, is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).
`Ψ₁(n) = Σ_{k<n} Λ(k)(n − k)`, and erdos-985 supplies the explicit formula and Hadamard's
product for `ξ`.

1. `Ψ₁(a+2h) − 2Ψ₁(a+h) + Ψ₁(a) ≤ h Σ_{a≤k<a+2h} Λ(k)` (`Cramer/Psi1.lean`).
2. For `Re ρ = 1/2`, the second difference `D_ρ` of `t^{ρ+1}/(ρ(ρ+1))` satisfies
   `‖D_ρ‖ ≤ min(h²/√a, 4(a+2h)^{3/2}/‖ρ(ρ+1)‖)` (`Cramer/SecondDiff.lean`).
3. Under RH, `Σ_ρ m_ρ min(A, B/‖ρ(ρ+1)‖) ≤ 2Aσ (L(1/2+σ) + 1/40)` whenever `B ≤ Aσ²`, with
   `L(s) = 1/s + 1/(s−1) + ½ log(s/2) − ½ log π ≥ Re ξ'/ξ(s)`; the pointwise step is
   `min(A, B/(¼+γ²)) ≤ 2Aσ Re 1/(s−ρ)` and Hadamard at real `s = 1/2 + σ` sums it
   (`Cramer/ZeroSum.lean`).
4. erdos-985's `explicit_formula_zeta`, multiplied by `n` and second-differenced, gives
   `ΔΨ₁ ≥ h² − 2h²a^{−1/2}σ(L(1/2+σ) + 1/40) − 3` (`Cramer/Identity.lean`).
5. Proper prime powers in `[a, b)`, `b ≤ 2a`, weigh at most
   `log b ((√b − √a + 1) + (b^{1/3} + 1))` (`Cramer/PrimePowers.lean`).
6. With `σ = 2b/h`, Steps 1–5 give a prime in `[a, a+2h)` once one explicit inequality holds
   (`Cramer/Interval.lean`).
7. For `x ≥ 10^6`, `a = ⌊x⌋ + 1`, `h = ⌈√x log x⌉ − 1`: writing `x = t⁶`, the inequality
   reduces to `(ℓ+0.7)(ℓ+2+1.26t²) + 2ℓ² + 3 < 5.84t³`, `ℓ = log x` (`Cramer/Large.lean`).
8. For `2 ≤ x < 10^6`: a chain of 99 primes from 2 to 1005161 with checked gaps
   (`Cramer/Small.lean`).
9. Assembly (`Cramer/Main.lean`).

### Mean square

`psi1 y = Σ_{n ≤ y} Λ(n)(y − n) = ∫_0^y ψ` is erdos-233's; its explicit formula for real `y`
converges absolutely, so no truncated Perron formula is needed.

1. `acoef δ ρ = ((1+δ)^{ρ+1} − 1)/(δρ(ρ+1))` satisfies `‖acoef δ ρ‖ ≤ 2/|ρ|` uniformly in `δ`
   and `≤ 20/(δ(1+γ²))`; with the unit-window zero count,
   `Σ_ρ m_ρ ‖acoef δ ρ‖² log(|γ|+2) ≤ C`, `C` independent of `δ`
   (`Cramer/MeanSquare/Coeff.lean`). This is where `Σ_ρ log|γ|/|ρ|² < ∞` enters.
2. For `h = δy ∈ [1, 4]`:
   `|ψ₁(y+h) − ψ₁(y) − hy| ≤ h (B + √y ‖Σ_ρ m_ρ acoef δ ρ y^{iγ}‖)`, from the explicit
   formula, `|y^{ρ+1}| = y^{3/2}` under RH and the absolutely convergent
   `K = Σ_ρ m_ρ (1/(2−ρ) + 1/ρ)` (`Cramer/MeanSquare/Explicit.lean`).
3. `hψ(y) ≤ ψ₁(y+h) − ψ₁(y) ≤ hψ(y+h)` and `ψ(y+4) − ψ(y) ≤ 4 log(y+4)`
   (`Cramer/MeanSquare/Psi.lean`).
4. One block, `δ = 1/Y`: `|ψ(y) − y| ≤ B + √y‖G(log y)‖ + 4 log(y+4)` on `[Y, 4Y]`; erdos-233's
   Gaussian-weight mean value theorem gives `∫_Y^{4Y} y‖G(log y)‖² dy ≤ 16 C_m C Y²`, hence
   `∫_Y^{4Y} (ψ(y) − y)² dy ≤ C' Y²` for `Y ≥ 2` (`Cramer/MeanSquare/Block.lean`).
5. Splitting `[2, X] = [2, X/4] ∪ [X/4, X]` and inducting on `X ≤ 8·4^n`:
   `∫_2^X (ψ − y)² ≤ C' X²` and `∫_2^X ((ψ − y)/y)² ≤ C' + (C'/log 4) log X`
   (`Cramer/MeanSquare/Main.lean`).

## Layout

| File | Content |
|---|---|
| `Cramer/Statement.lean` | Target definitions (fixed) |
| `Cramer/Psi1.lean` | Step 1 |
| `Cramer/SecondDiff.lean` | Step 2 |
| `Cramer/ZeroSum.lean` | RH for `ξ`; Step 3 |
| `Cramer/Identity.lean` | Step 4 |
| `Cramer/PrimePowers.lean` | Step 5 |
| `Cramer/Interval.lean` | Step 6 |
| `Cramer/Large.lean` | Step 7 (`x ≥ 10^6`) |
| `Cramer/Small.lean` | Step 8 (`2 ≤ x < 10^6`), the prime chain |
| `Cramer/Main.lean` | Headline theorems (prime gaps) |
| `Cramer/Statement2.lean` | Mean-square target definitions (fixed) |
| `Cramer/MeanSquare/Coeff.lean` | Mean square, Step 1 |
| `Cramer/MeanSquare/Explicit.lean` | Mean square, Step 2 |
| `Cramer/MeanSquare/Psi.lean` | Mean square, Step 3 |
| `Cramer/MeanSquare/Block.lean` | Mean square, Step 4 |
| `Cramer/MeanSquare/Main.lean` | Mean square, Step 5; headline theorems |
| `Unconditional/CramerUnconditional.lean` | One-line discharges from riemann-hypothesis |

## Deviations from the literature

**Constant `2` instead of `22/25`.** The weight used in Step 3,
`min(A, B/q) ≤ 2Aσ²/(σ² + γ²)`, is the best of its form (`min(1, 1/t) ≤ α/(1 + t/β)` forces
`α√β ≥ 2`), and with it the method gives exactly `p_{n+1} − p_n ≤ (2 + o(1))√p_n log p_n`; the
lower-order margin is about `2√x log(π log x)`, so `c = 2` holds from `x ≈ 2·10^3` on, while any
`c < 2` eventually fails for this argument (for `c = 1.8`, around `x ≈ 10^{52}`, by a numerical
estimate). Carneiro–Milinovich–Soundararajan reach `22/25` with Fourier optimisation
(Beurling–Selberg-type majorants in the Guinand–Weil explicit formula), which needs an explicit
formula for general test functions; erdos-985 provides only the Riesz-weighted one
(`Σ Λ(n)(1 − n/x)`). The statements are parametrised by `c` (`PrimeInShortInterval c`,
`PrimeGapExplicit c`), so a sharper constant can be added later without touching them.

**Mean square: `O`-constants, no asymptotic.** The three mean-square theorems are `IsBigO`
statements with an existential constant; it is not computed (it passes through erdos-233's
zero-density constant). Brent–Platt–Trudgian's `0.8603` and Montgomery–Vaughan's asymptotic
`∼ c₁ log X`, `c₁ = Σ_ρ m_ρ/|ρ|² ≈ 0.046`, are not proved here: the asymptotic needs the
off-diagonal terms `∫ y^{i(γ−γ')}` to average out, which this block-by-block argument with a
`Y`-dependent smoothing does not give.

**Analytic threshold `10^6`.** The exact form of the Step 6 inequality already holds with
`c = 2` from about `1.9·10^3`; Step 7 uses simpler polynomial bounds that need `x ≥ 10^6`. The
range below is covered by the 99-prime chain, so no cited computation remains.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`); erdos-233 at `1ff9f39` for the
mean square.

```
lake exe cache get
lake build            # target `Cramer`
```

A clean build of the `Cramer` modules (erdos-985 already built) took 2 min 57 s wall,
143 s CPU on this box under load. The slowest modules: `Cramer.Large` 56 s (nonlinear
arithmetic), `Cramer.Small` about 30 s (kernel `decide` over the chain and 99 `norm_num`
primality proofs), `Cramer.Identity` 23 s.

The mean-square modules (Round 5, 2026-11-24, on a box at load average about 80): erdos-233's
modules took about 3 min wall to build here; each of `Cramer.MeanSquare.{Coeff, Explicit, Psi,
Block, Main}` elaborates in about 15 s wall. No `native_decide`, no finite computation.

## Unconditional version

`Unconditional/CramerUnconditional.lean` proves Cramér's gap bound with constant `2` and his
mean-square bounds unconditionally in Lean, with the certified proof of RH. It imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and discharges the hypothesis with `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `cramer_primeInShortInterval` | `Cramer.PrimeInShortInterval 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeGapExplicit` | `Cramer.PrimeGapExplicit 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_gapBound` | `Cramer.CramerGapBound` | `propext`, `Classical.choice`, `Quot.sound` |

```
scripts/check-unconditional.sh [RH_DIR]
```

Run on 2026-11-24 against riemann-hypothesis `507a75d91d` (cache build, not `RH_FULL_BUILD`),
library and `Unconditional/` as of cramer-rh commit `a8cbd47` (unchanged since); 48 min wall, most of it waiting for and
loading the RH cache. Output:

```
'cramer_primeInShortInterval' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeGapExplicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_gapBound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `ulimit -n 2000000` or `nofile` in `/etc/security/limits.conf`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh).
This check links against the community build cache and does not repeat those kernel checks.

## Credits

* [erdos-985](https://github.com/senamakel/erdos-985) (`9538edb`, lake dependency): the weighted
  explicit formula `explicit_formula_zeta`, Hadamard's factorisation `hadamard_logDeriv`, the
  digamma bounds and the numerics for `ξ`. Same author, no licence file yet.
* [erdos-233](https://github.com/senamakel/erdos-233) (`1ff9f39`, lake dependency, mean square
  only): `psi1`, its real-`x` explicit formula `psi1_formula`, `zero_density`, `mean_value`,
  `series_bound` and the `CoeffAux` derivative bounds. `Cramer/MeanSquare/Coeff.lean`
  (`sq_log_sums`) and `Cramer/MeanSquare/Block.lean` (`G_mean_square`) adapt the proofs of
  erdos-233's `coef_sums` and `mean_square`. Same author, no licence file yet.
* `Cramer.xiZeta_ne_zero_of_half_lt_RH` and `Cramer.xiZeta_zero_re_RH` (`Cramer/ZeroSum.lean`)
  repeat the proofs of the same-named lemmas in
  [robin-rh](https://github.com/senamakel/robin-rh) `Robin/RH/Bach.lean`. Same author.
* `primeGap` and the `CramerGapBound` statement: google-deepmind/formal-conjectures, commit
  `86a2f58a`, Apache License 2.0.
* Nothing is vendored from riemann-hypothesis; it is imported only by `Unconditional/`.
