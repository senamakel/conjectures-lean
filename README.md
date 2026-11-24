# Cramér's prime-gap theorem under RH in Lean

Cramér (1920, *Arkiv för Matematik, Astronomi och Fysik* **15**, no. 5) proved that the Riemann
hypothesis implies `p_{n+1} − p_n = O(√p_n log p_n)`. This is his theorem, not his 1936
conjecture `p_{n+1} − p_n = O(log² p_n)`, which is open even under RH. The best explicit form is
Carneiro–Milinovich–Soundararajan (2019, *Comment. Math. Helv.* **94**, 533–568):
`p_{n+1} − p_n < (22/25) √p_n log p_n` for every `p_n > 3`, under RH. Unconditionally the best
exponent is Baker–Harman–Pintz (2001): `p_{n+1} − p_n = O(p_n^{0.525})`.

This project proves Cramér's theorem under RH with the explicit constant `2`:

```lean
theorem Cramer.primeInShortInterval_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInShortInterval 2

theorem Cramer.primeGapExplicit_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeGapExplicit 2

theorem Cramer.cramer_of_RH (hRH : RiemannHypothesis) : Cramer.CramerGapBound
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

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Cramer.primeInShortInterval_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `Cramer.primeGapExplicit_of_RH` | C | `RiemannHypothesis` |
| `Cramer.cramer_of_RH` | C | `RiemannHypothesis` |
| `cramer_primeInShortInterval` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_primeGapExplicit` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_gapBound` (`Unconditional/`) | U | none; RH from riemann-hypothesis |

`primeGap` is copied word for word from google-deepmind/formal-conjectures,
[`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean),
and `CramerGapBound` is the conclusion of `cramer_conjecture.variants.conditional_rh` in
[`FormalConjectures/Wikipedia/CramerConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/CramerConjecture.lean)
(commit `86a2f58a`), whose hypothesis is Mathlib's `RiemannHypothesis`, as here. The explicit
forms `PrimeInShortInterval` and `PrimeGapExplicit` are this repository's own. The main library
takes RH as a hypothesis and never imports riemann-hypothesis. No cited-hypothesis (tier H)
inputs: the range below the analytic threshold is checked in Lean.

## Axioms

`lake env lean` on a file with `#print axioms` after `import Cramer`:

```
'Cramer.primeInShortInterval_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeGapExplicit_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.cramer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

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
| `Cramer/Main.lean` | Headline theorems |
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

**Analytic threshold `10^6`.** The exact form of the Step 6 inequality already holds with
`c = 2` from about `1.9·10^3`; Step 7 uses simpler polynomial bounds that need `x ≥ 10^6`. The
range below is covered by the 99-prime chain, so no cited computation remains.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build            # target `Cramer`
```

A clean build of the `Cramer` modules (erdos-985 already built) took 2 min 57 s wall,
143 s CPU on this box under load. The slowest modules: `Cramer.Large` 56 s (nonlinear
arithmetic), `Cramer.Small` about 30 s (kernel `decide` over the chain and 99 `norm_num`
primality proofs), `Cramer.Identity` 23 s.

## Unconditional version

`Unconditional/CramerUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and discharges the hypothesis with `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `cramer_primeInShortInterval` | `Cramer.PrimeInShortInterval 2` | not yet run |
| `cramer_primeGapExplicit` | `Cramer.PrimeGapExplicit 2` | not yet run |
| `cramer_gapBound` | `Cramer.CramerGapBound` | not yet run |

```
scripts/check-unconditional.sh [RH_DIR]
```

Not yet run on this box: the axiom column is filled in from the script's real output once it has run.

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `ulimit -n 2000000` or `nofile` in `/etc/security/limits.conf`).

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

* [erdos-985](https://github.com/senamakel/erdos-985) (`9538edb`, lake dependency): the weighted
  explicit formula `explicit_formula_zeta`, Hadamard's factorisation `hadamard_logDeriv`, the
  digamma bounds and the numerics for `ξ`. Same author, no licence file yet.
* `Cramer.xiZeta_ne_zero_of_half_lt_RH` and `Cramer.xiZeta_zero_re_RH` (`Cramer/ZeroSum.lean`)
  repeat the proofs of the same-named lemmas in
  [robin-rh](https://github.com/senamakel/robin-rh) `Robin/RH/Bach.lean`. Same author.
* `primeGap` and the `CramerGapBound` statement: google-deepmind/formal-conjectures, commit
  `86a2f58a`, Apache License 2.0.
* Nothing is vendored from riemann-hypothesis; it is imported only by `Unconditional/`.
