# Cramér's prime-gap and mean-square theorems under RH in Lean

This project proves in Lean that every interval `(x, x + (107/100)√x log x]` with `x ≥ 2`
contains a prime, so `p_{n+1} − p_n ≤ 1.07 √p_n log p_n` for every `n` and
`p_{n+1} − p_n = O(√p_n log p_n)`. It also proves Cramér's mean-square theorems for `ψ(x) − x`:
`∫_1^X (ψ(x) − x)² dx ≪ X²`, its dyadic and logarithmic forms, and the asymptotic
`∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X` with `c₁ = Σ_ρ m_ρ/|ρ|²`. `Unconditional/` proves all of
them unconditionally in Lean from the standard three axioms, with RH supplied by the certified
proof of L. Alpöge (2026). The main library holds complete Lean proofs that RH implies each one.

The prime-gap bound is Cramér's (1920, *Arkiv för Matematik, Astronomi och Fysik* **15**, no. 5).
The constant `1.07` is below Dudek's `4/π ≈ 1.273` (2015, *Int. J. Number Theory* **11**,
771-778; a prime in `(x − (2/π)√x log x, x + (2/π)√x log x)`, as quoted by Dudek, Grenié and
Molteni). Dudek, Grenié and Molteni (2016, *Int. J. Number Theory* **12**, 1391-1407,
Theorem 1.1) give half-width `(1/2 + 2/log x)√x log x` for `x ≥ 2`, and Carneiro, Milinovich and
Soundararajan (2019, *Comment. Math. Helv.* **94**, 533-568, Theorem 5) a prime in
`[x, x + (22/25)√x log x]` for `x ≥ 4`; see "Deviations from the literature". Without RH the best
gap exponent is Baker, Harman and Pintz's `O(p_n^{0.525})` (2001).

The mean-square bound is Cramér's (1922, *Ein Mittelwertsatz in der Primzahltheorie*, *Math. Z.*
**12**, 147-153; Montgomery and Vaughan, *Multiplicative Number Theory I*, Thm 13.5).
Brent, Platt and Trudgian (2022, *J. Number Theory* **238**, 740-762) give the constant `0.8603`
for `lim sup X^{-2} ∫_X^{2X}`. The asymptotic `∼ c₁ log X`, with zeros counted with multiplicity
and the series for `c₁` convergent, also goes back to Cramér (1922), in the form of
Montgomery–Vaughan Theorem 13.6 and Exercise 13.1.1.3. The statement and the convention for
multiplicities were checked against Brent, Platt and Trudgian (arXiv:2008.06140, §5.1 eq. (18)
and the proof of their Theorem 5), and Montgomery–Vaughan is cited through them.

Literature status: **RH-consequence** for all of these.

The gap bound follows Cramér (1920) through a triangular (Fejér-type) weight, the second
difference of `ψ₁`. The constant `107/100` comes from bounding each zero's contribution by its
size `h²m^{−1/2} sin²x/x²` (`x = γh/2m`, `m` the centre of the interval) up to an `O(h/(mx))`
error, and majorising that by 53 pairs of Lorentzians centred at `±τ`, which Hadamard's product
at complex points sums exactly. The mean square goes through the explicit formula and the
convergence of `Σ_ρ log|γ|/|ρ|²`, as in the classical proof.

```lean
theorem cramer_primeInShortInterval_107 : Cramer.PrimeInShortInterval (107 / 100)  -- Unconditional/
theorem cramer_primeGapExplicit_107 : Cramer.PrimeGapExplicit (107 / 100)          -- Unconditional/
theorem cramer_meanSquare : Cramer.CramerMeanSquare                                -- Unconditional/
theorem cramer_logMeanSquareAsymptotic : Cramer.CramerLogMeanSquareAsymptotic      -- Unconditional/

theorem Cramer.primeInShortInterval_107_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInShortInterval (107 / 100)

theorem Cramer.primeGapExplicit_107_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeGapExplicit (107 / 100)

theorem Cramer.primeInClosedInterval_107_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInClosedInterval 2 (107 / 100)

theorem Cramer.cramer_of_RH (hRH : RiemannHypothesis) : Cramer.CramerGapBound

theorem Cramer.dyadicMeanSquare_of_RH (hRH : RiemannHypothesis) :
    Cramer.CramerDyadicMeanSquare

theorem Cramer.meanSquare_of_RH (hRH : RiemannHypothesis) : Cramer.CramerMeanSquare

theorem Cramer.logMeanSquare_of_RH (hRH : RiemannHypothesis) : Cramer.CramerLogMeanSquare

theorem Cramer.logMeanSquareAsymptotic_of_RH (hRH : RiemannHypothesis) :
    Cramer.CramerLogMeanSquareAsymptotic
```

The repository also keeps the gap theorems with the constants `2` and `3/2`, which use simpler
majorants (see "Proof outline"):

```lean
theorem Cramer.primeInShortInterval_three_halves_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInShortInterval (3 / 2)

theorem Cramer.primeGapExplicit_three_halves_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeGapExplicit (3 / 2)

theorem Cramer.primeInClosedInterval_three_halves_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInClosedInterval 2 (3 / 2)

theorem Cramer.primeInShortInterval_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInShortInterval 2

theorem Cramer.primeGapExplicit_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeGapExplicit 2
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

The Carneiro–Milinovich–Soundararajan form, fixed in `Cramer/Statement4.lean` (Theorem 5 of
arXiv:1708.04122, read in the arXiv source). Their interval is closed and starts at `x = 4`.
`PrimeInShortInterval (22/25)` would be false (`(2, 2.86…]` holds no prime), so the paper's form
has its own definition. `PrimeInClosedInterval` carries the `107/100` theorem; `CMSPrimeInterval`
and `CMSPrimeGap` are open targets (see "Deviations from the literature"):

```lean
def PrimeInClosedInterval (x₀ c : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + c * Real.sqrt x * Real.log x

def CMSPrimeInterval : Prop := PrimeInClosedInterval 4 (22 / 25)

def CMSPrimeGap : Prop :=
  ∀ n : ℕ, 3 < Nat.nth Nat.Prime n → (primeGap n : ℝ) ≤
    22 / 25 * Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)
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

The asymptotic target, fixed in `Cramer/Statement3.lean`, uses Mathlib's `riemannZeta` and
`analyticOrderNatAt` only:

```lean
def NontrivialZeros : Set ℂ := {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}

noncomputable def cramerTerm (ρ : NontrivialZeros) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2

noncomputable def cramerConstant : ℝ := ∑' ρ : NontrivialZeros, cramerTerm ρ

def CramerLogMeanSquareAsymptotic : Prop :=
  Summable cramerTerm ∧
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2) / Real.log X) atTop
      (𝓝 cramerConstant)
```

`NontrivialZeros` lists each zero once, so the classical `c₁ = Σ_ρ m_ρ/|ρ|²`, in which
(Brent–Platt–Trudgian §5.1) "each zero ρ is counted according to its multiplicity m_ρ", is
`Σ_{ρ distinct} m_ρ²/|ρ|²`. That is also the mean square of the almost periodic function
`−Σ_{ρ distinct} (m_ρ/ρ) e^{iγu}` that `(ψ(e^u) − e^u)e^{−u/2}` approximates. The statement
asserts convergence of the series, so `cramerConstant` is not `∑'`'s junk value.

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Cramer.primeInShortInterval_107_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `Cramer.primeGapExplicit_107_of_RH` | C | `RiemannHypothesis` |
| `Cramer.primeInClosedInterval_107_of_RH` | C | `RiemannHypothesis` |
| `cramer_primeInShortInterval_107` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_primeGapExplicit_107` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_primeInClosedInterval_107` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `Cramer.primeInShortInterval_three_halves_of_RH` | C | `RiemannHypothesis` |
| `Cramer.primeGapExplicit_three_halves_of_RH` | C | `RiemannHypothesis` |
| `Cramer.primeInClosedInterval_three_halves_of_RH` | C | `RiemannHypothesis` |
| `cramer_primeInShortInterval_three_halves` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_primeGapExplicit_three_halves` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_primeInClosedInterval_three_halves` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `Cramer.primeInShortInterval_of_RH` | C | `RiemannHypothesis` |
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
| `Cramer.logMeanSquareAsymptotic_of_RH` | C | `RiemannHypothesis` |
| `cramer_logMeanSquareAsymptotic` (`Unconditional/`) | U | none; RH from riemann-hypothesis |

`primeGap` is copied word for word from google-deepmind/formal-conjectures,
[`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean),
and `CramerGapBound` is the conclusion of `cramer_conjecture.variants.conditional_rh` in
[`FormalConjectures/Wikipedia/CramerConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/CramerConjecture.lean)
(commit `86a2f58a`), whose hypothesis is Mathlib's `RiemannHypothesis`, as here. The explicit
forms `PrimeInShortInterval` and `PrimeGapExplicit` are this repository's own, and so are the
four mean-square statements: formal-conjectures has no mean-square statement for `ψ`
(searched 2026-11-24 at `9097e2f9`). The main library
takes RH as a hypothesis and never imports riemann-hypothesis. There are no tier-H inputs. The
range below the gap theorem's analytic threshold is checked in Lean, and the
mean-square proof uses erdos-233's real-`x` explicit formula and zero-density lemma, both proved
there from Mathlib and erdos-985.

Cramér's 1936 conjecture `p_{n+1} − p_n = O(log² p_n)` is a separate, stronger statement and is
not a target here.

## Axioms

`lake env lean` on a file with `#print axioms` after `import Cramer`:

```
'Cramer.primeInShortInterval_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeGapExplicit_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.cramer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.dyadicMeanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.meanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.logMeanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.logMeanSquareAsymptotic_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeInShortInterval_three_halves_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeGapExplicit_three_halves_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeInClosedInterval_three_halves_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeInShortInterval_107_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeGapExplicit_107_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.primeInClosedInterval_107_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/check-axioms.sh` reruns this and fails unless all thirteen use only the standard axioms.
No `sorry`, no `native_decide`, no `axiom` declarations. The finite checks (`Cramer/Small.lean`,
`Cramer/Sharp/Small.lean`, `Cramer/Shift/Small.lean`, `Cramer/Shift/Data.lean`,
`Cramer/Shift/Facts.lean`) use kernel `decide` (`decide +kernel` for the prime chains and the
4033 majorant cells) and `norm_num`, which add no axioms.

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
6. With `σ = 2b/h`, Steps 1 to 5 give a prime in `[a, a+2h)` once one explicit inequality holds
   (`Cramer/Interval.lean`).
7. For `x ≥ 10^6`, `a = ⌊x⌋ + 1`, `h = ⌈√x log x⌉ − 1`: writing `x = t⁶`, the inequality
   reduces to `(ℓ+0.7)(ℓ+2+1.26t²) + 2ℓ² + 3 < 5.84t³`, `ℓ = log x` (`Cramer/Large.lean`).
8. For `2 ≤ x < 10^6`: a chain of 99 primes from 2 to 1005161 with checked gaps
   (`Cramer/Small.lean`).
9. Assembly (`Cramer/Main.lean`).

### Constant `3/2`

Steps 1, 4 and 5 are shared; `Cramer/Identity.lean` states Step 4 for any bound `Z` on
`Σ_ρ m_ρ ‖D_ρ‖` (`psi1N_second_diff_ge_of_zeroSum`).

1. `sin x ≤ x − x³/6 + x⁵/120` and `v − v²/2 ≤ log(1+v)` for `x, v ≥ 0`
   (`Cramer/Sharp/Taylor.lean`).
2. For `ρ = 1/2 + iγ`, `γ ≠ 0`, `D_ρ` is the second difference of `φ(u) = g(a+u)`,
   `φ'' = (a+u)^{ρ−1}`. Against `ψ(u) = −a^{ρ−1}κ^{−2}e^{iκu}` (`κ = γ/a`), whose second
   difference has norm `h²a^{−1/2} sin²x/x²` (`x = γh/2a`), and with
   `‖φ'' − ψ''‖ ≤ a^{−1/2}(u/2a + |γ|u²/2a²)`:
   `‖D_ρ‖ ≤ h²a^{−1/2}(sin²x/x² + h/a + 2|γ|h²/a²)` (`Cramer/Sharp/SecondDiff.lean`).
3. If `400h ≤ a`, every zero has `‖D_ρ‖ ≤ (9/7)A σ²/(σ²+γ²)`, `A = h²a^{−1/2}`, `σ = 7a/(3h)`,
   i.e. `A·(7/4)/(49/36 + x²)`: for `x² ≤ 2` from Step 2, `sin²x/x² ≤ (1 − x²/6 + x⁴/120)²` and
   `(T² + δ(3+2y))(49/36+y) ≤ 7/4` on `[0, 2]`, `δ ≤ 1/400`; for `x² ≥ 2` from
   `‖D_ρ‖ ≤ 4(a+2h)^{3/2}/γ²`. Hadamard at `s = 1/2 + σ` sums the Lorentzian:
   `Σ_ρ m_ρ ‖D_ρ‖ ≤ (9/7)Aσ(L(1/2+σ) + 1/40) = 3h√a (L(1/2+σ) + 1/40)`
   (`Cramer/Sharp/Majorant.lean`).
4. Hence a prime in `[a, a+2h)` once `400h ≤ a` and
   `log b(√b − √a + 1 + b^{1/3} + 1) < h − 3√a(L(1/2 + 7a/3h) + 1/40) − 3/h`
   (`Cramer/Sharp/Interval.lean`).
5. For `x ≥ 6.4·10^7`, `a = ⌊x⌋ + 1`, `h = ⌈(3/4)√x log x⌉ − 1`, `x = t⁶`: the condition reduces
   to `(ℓ + 0.7)(0.75ℓ + 2 + 1.26t²) + 3 < 4.8t³` (`Cramer/Sharp/Large.lean`).
6. For `2 ≤ x < 6.4·10^7`: a chain of 696 primes from 2 to 64165103 with
   `q_{i+1} − q_i ≤ (3/2)√q_i log q_i`, `log q_i` bounded below through `2^k ≤ q_i^8`
   (`Cramer/Sharp/Small.lean`).
7. Assembly (`Cramer/Main4.lean`).

### Constant `107/100`

Steps 1, 4 and 5 of the first outline are shared (`psi1N_second_diff_ge_of_zeroSum` takes any
bound on the zero sum). Files are in `Cramer/Shift/`.

1. Centred bound (`Center.lean`). With `m = a + h`, `ε = h/m`, write
   `(1 ± ε)^{ρ+1} = e^{±iγε} e^{w±}`. Then `‖D_ρ‖ ≤ m^{3/2}(4 sin²(γε/2) + 2(w + w²))/γ²`,
   `w = (3/2)ε/(1−ε) + |γ|(ε²/2 + ε³/(1−ε))`. Relative to `A = h²m^{−1/2}` the error is
   `O(ε/x)`, not `O(εx)` as in the left-endpoint bound, so the zeros of `sin²x` can be used up to
   `x ≈ 10`.
2. Three envelopes (`PerZero.lean`). For `ε ≤ 1/800` and `y = |γh/2m|`, `‖D_ρ‖/A` is at most
   `802/(800y²)` (trivial bound), `((1 − cos 2y) + w(y) + w(y)²)/(2y²)` with
   `w(y) = (1200 + 801y)/639200` (Step 1), or, for `y ≤ 1`,
   `(800/799)(T(y²)² + (799 + 3200y)/638401)` (the `3/2` bound, `T(u) = 1 − u/6 + u²/120`).
3. The majorant (`Check.lean`, `Data.lean`, `Tail.lean`, `Facts.lean`).
   `M(x) = Σ c (lor(σ, x−τ) + lor(σ, x+τ))`, `lor(σ, y) = σ²/(σ²+y²)`, 53 terms with
   `σ ∈ {0.15, 4, 14, 30}`, `τ ∈ {0, 1/8, …, 12}`, `Σ 2cσ = 1.0671`, found by a linear program
   (`scripts/shift_lp.py`). 4033 cells cover `[0, 150]`; on each, `cellOK` checks one envelope
   against the smaller endpoint value of each Lorentzian, in integer arithmetic: `1 − cos 2x` is
   bounded by writing `2x = kπ + t`, `|t| ≤ 3`, with `3.141592 < π < 3.141593` and
   `cos ≥ T₁₀`, `cos ≤ T₈` (`Cramer/Shift/Taylor.lean`). For `x ≥ 150` the centred terms alone beat
   `802/(800x²)`. All of it is kernel `decide`; `cellOK_sound`, `chainOK_sound`, `tail_good` prove
   the checks sound.
4. Zero sums at complex points (`ZeroSum.lean`, `MajSum.lean`). Hadamard's product at
   `s = 1/2 + S + iT` gives `Σ_ρ m_ρ S²/(S² + (γ−T)²) ≤ S(Lc(S,T) + 1/40)` under RH, where
   `Lc` bounds `Re ξ'/ξ(s)` with `Re ψ(σ+it) ≤ log σ + ½ log(1 + t²/(σ−1)²)` (vendored, see
   Credits) and `Re ζ'/ζ(s) ≤ 1.52 · 2^{3/2−Re s}`. In `γ`, each `lor(σ, x ∓ τ)` is such a
   Lorentzian with `S = 2mσ/h`, `T = ±2mτ/h`.
5. Two numbers (`Bucket.lean`). Each term gets a bucket `4^{n−6}` above
   `(σ + 1/3200)²(1 + τ²/(σ − 3/3200)²)`, so the zero term is at most
   `4√m (SS · ½ log(m/h) + NS · ½ log 2)`, `SS = Σ cσ ≤ 0.5336`, `NS = Σ cσ(n−6) ≤ 0.207`.
6. Analytic range (`Interval.lean`, `Large.lean`). For `x ≥ 10^8`, `a = ⌊x⌋ + 1`,
   `h = ⌈(107/200)√x log x⌉ − 1`: `800h ≤ a + h`, `log(m/h) ≤ ℓ/2 − 2`, and the condition reduces
   to `(ℓ + 0.7)(0.535ℓ + 2 + 1.26t²) + 0.18ℓ² + 3 < 1.847t³`, `x = t⁶`, `ℓ = log x`.
7. Finite range (`Small.lean`). A chain of 1176 primes from 2 to 100102841 with
   `q_{i+1} − q_i ≤ (107/100)√q_i log q_i`, `log q_i` bounded below through `2^k ≤ q_i^16`
   (`scripts/shift_chain.py`).
8. Assembly (`Cramer/Main5.lean`).

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

### Mean-square asymptotic

Write `f(y) = (ψ(y) − y)/y` and, for a finite set `S` of zeros,
`g_S(y) = y^{−1/2} W_S(log y)` with `W_S(u) = Σ_{ρ∈S} (m_ρ/ρ) e^{iγu}`.

1. The first-difference identity of Step 2 kept with its sign: on `[Y, 4Y]`, `δ = 1/Y`,
   `‖(ψ(y) − y) + √y G(log y)‖ ≤ B + 4 log(y+4)` (`Cramer/MeanSquare/Approx.lean`).
2. A finite sum with distinct frequencies (distinct ordinates, since under RH `ρ = ½ + iγ`):
   `|∫_a^b |W_S|² − (b − a) Σ_{ρ∈S} m_ρ²/|ρ|²| ≤ Σ_{ρ≠ρ'} 2 m_ρ m_ρ'/(|ρ||ρ'||γ − γ'|)`, a bound
   independent of `a, b`; and `acoef δ ρ → 1/ρ` as `δ → 0⁺` (`Cramer/MeanSquare/Finite.lean`).
3. `G = Σ_{ρ∈S} m_ρ acoef δ ρ e^{iγu} + (tail)`, the finite part is within
   `η_S(δ) = Σ_{ρ∈S} m_ρ |acoef δ ρ − 1/ρ| → 0` of `W_S`, and the tail has
   `∫_U^{U+2} |tail|² ≤ C Σ_{ρ∉S} m_ρ log(|γ|+2)/|ρ|²` uniformly in `δ` and `U` (erdos-233's
   mean value theorem); `m_ρ ≪ log(|γ|+2)` makes `Σ m_ρ²/|ρ|²` converge
   (`Cramer/MeanSquare/Tail.lean`).
4. On a block, `f + g_S = ((ψ − y) + √y G)/y − (G − W_S)/√y`, so
   `∫_Y^{4Y} |f + g_S|² ≤ K/√Y + 9 η_S(1/Y)² + 3C·tail(S)`; summing blocks from `Y₀` on,
   `∫_1^X |f + g_S|² ≤ K' + ε log X` once `S` and `Y₀` are large. With `y = e^u`,
   `∫_1^X |g_S|² = ∫_0^{log X} |W_S|²` (`Cramer/MeanSquare/Asymptotic.lean`).
5. `f² ≤ (1+t)|g_S|² + (1+1/t)|f + g_S|²` and its mirror, integrated, squeeze
   `(∫_1^X f²)/log X` to `Σ_ρ m_ρ²/|ρ|²` (`Cramer/MeanSquare/Limit.lean`,
   `Cramer/MeanSquare/Asymptotic.lean`).
6. The zeros of erdos-985's `ξ` are the nontrivial zeros of `ζ` with the same multiplicities,
   which moves the constant to `cramerConstant` (`Cramer/MeanSquare/Zeros.lean`,
   `Cramer/MeanSquare/Main3.lean`).

No smoothing independent of the block is needed: the off-diagonal terms are handled only for the
finite part `W_S`, whose coefficients do not depend on `δ`, and the infinite tail is small in
mean square uniformly in `δ`.

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
| `Cramer/Main.lean` | Headline theorems (prime gaps, constant `2`) |
| `Cramer/Statement4.lean` | Carneiro–Milinovich–Soundararajan form (fixed) |
| `Cramer/Sharp/Taylor.lean` | Constant `3/2`, Step 1 |
| `Cramer/Sharp/SecondDiff.lean` | Constant `3/2`, Step 2 (sharp `‖D_ρ‖`) |
| `Cramer/Sharp/Majorant.lean` | Constant `3/2`, Step 3 (Lorentzian majorant, zero sum) |
| `Cramer/Sharp/Interval.lean` | Constant `3/2`, Step 4 |
| `Cramer/Sharp/Large.lean` | Constant `3/2`, Step 5 (`x ≥ 6.4·10^7`) |
| `Cramer/Sharp/Small.lean` | Constant `3/2`, Step 6 (the 696-prime chain) |
| `Cramer/Main4.lean` | Headline theorems (constant `3/2`) |
| `Cramer/Vendor/Digamma.lean` | `Re ψ(σ+it)` bound, vendored from calr3/ternary-goldbach |
| `Cramer/Shift/Taylor.lean` | Constant `107/100`: `cos` Taylor bounds to degree 10 |
| `Cramer/Shift/Center.lean` | Constant `107/100`, Step 1 (centred `‖D_ρ‖`) |
| `Cramer/Shift/Check.lean` | Step 3: the integer cell check and its soundness |
| `Cramer/Shift/PerZero.lean` | Step 2: `‖D_ρ‖ ≤ A·M(x)` from good cells |
| `Cramer/Shift/ZeroSum.lean` | Step 4: Hadamard at complex `s`, `Lc` |
| `Cramer/Shift/MajSum.lean` | Step 4: the zero sum of the majorant |
| `Cramer/Shift/Tail.lean` | Step 3: the tail `x ≥ 150`, assembly of the cells |
| `Cramer/Shift/Bucket.lean` | Step 5 |
| `Cramer/Shift/Interval.lean` | Step 6: prime in `[a, a+2h)` |
| `Cramer/Shift/Large.lean` | Step 6 (`x ≥ 10^8`) |
| `Cramer/Shift/Data.lean` | Step 3: `maj107` and the 4033 cells (generated) |
| `Cramer/Shift/Facts.lean` | Step 3, 5: the checked facts about `maj107` |
| `Cramer/Shift/Small.lean` | Step 7: the 1176-prime chain (generated) |
| `Cramer/Main5.lean` | Headline theorems (constant `107/100`) |
| `Cramer/Statement2.lean` | Mean-square target definitions (fixed) |
| `Cramer/MeanSquare/Coeff.lean` | Mean square, Step 1 |
| `Cramer/MeanSquare/Explicit.lean` | Mean square, Step 2 |
| `Cramer/MeanSquare/Psi.lean` | Mean square, Step 3 |
| `Cramer/MeanSquare/Block.lean` | Mean square, Step 4 |
| `Cramer/MeanSquare/Main.lean` | Mean square, Step 5; headline theorems |
| `Cramer/Statement3.lean` | Mean-square asymptotic target definitions (fixed) |
| `Cramer/MeanSquare/Approx.lean` | Asymptotic, Step 1 |
| `Cramer/MeanSquare/Finite.lean` | Asymptotic, Step 2 |
| `Cramer/MeanSquare/Tail.lean` | Asymptotic, Step 3 |
| `Cramer/MeanSquare/Limit.lean` | Asymptotic, Step 5 (the squeeze) |
| `Cramer/MeanSquare/Asymptotic.lean` | Asymptotic, Steps 4 and 5 |
| `Cramer/MeanSquare/Zeros.lean` | Asymptotic, Step 6 (zeros of `ζ` and `ξ`) |
| `Cramer/MeanSquare/Main3.lean` | Asymptotic headline theorem |
| `Unconditional/CramerUnconditional.lean` | One-line discharges from riemann-hypothesis |

## Deviations from the literature

### Constant `107/100` instead of `22/25`

The gap theorem here has constant `107/100 = 1.07`. Carneiro–Milinovich–Soundararajan prove
`22/25 = 0.88` (for `x ≥ 4`, closed interval), Dudek–Grenié–Molteni `1 + 4/log x` and Dudek
`4/π ≈ 1.273` (both as total interval lengths in units of `√x log x`). `1.07` is below Dudek's constant, and below
`1 + 4/log x` for `x < e^{57}`; for larger `x` Dudek–Grenié–Molteni's interval is shorter.
`22/25` is not proved here.

The constant comes from the majorant. All three versions use the triangular weight on
`[a, a+2h]`, whose transform at a zero is `‖D_ρ‖ ≈ h²m^{−1/2} sin²x/x²`, `x = γh/2m`, and sum over zeros through
Hadamard's product, which sums a Lorentzian exactly. With zero density `(1/2π) log T`, a
Lorentzian majorant `M(x) ≥ sin²x/x²` gives the constant `∫M/π` (`∫ sin²x/x² = π` would give
`1`).

* Constant `2` (`Cramer/ZeroSum.lean`): `‖D_ρ‖ ≤ min(A, B/γ²)`, one Lorentzian, `∫M = 2π`.
* Constant `3/2` (`Cramer/Sharp/`): one centred Lorentzian above `sin²x/x²` for `x² ≤ 2`,
  `∫M = (3/2)π`. Mixtures of centred Lorentzians cannot beat `≈ 1.4492`.
* Constant `107/100` (`Cramer/Shift/`): Lorentzians centred at `±τ` (Hadamard at complex
  points), which can follow the zeros of `sin²x`, and the centred error bound, which keeps the
  error `O(ε/x)`. The linear program gives `∫M/π = 1.0671` with `σ ≥ 0.15`, `τ ≤ 12` and a 0.4%
  safety margin; `107/100` leaves 0.3% for the finite range of `x`.

Routes to a smaller constant, sized but not formalised:

| Route | Constant | What it needs |
|---|---|---|
| Narrower shifted Lorentzians (`σ ≥ 0.1`) | `≈ 1.064` | more terms and cells; same proof |
| Piecewise-linear weight, 3 knots, shifted Lorentzians | `≈ 1.05` (LP, `σ ≤ 4`) | the explicit formula for 5-point second differences of `Ψ₁`, the centred bound for them, two-sided `sin²` enclosures |
| Triangle weight, exact zero density | `→ 1.0` | an explicit `N(T)`: schoenfeld-rh proves Rosser's, at the cost of about 95,000 vendored lines |
| Piecewise-linear weights, exact zero density | `→ 0.925` | the above; `0.925` is the floor of `∫\|ŵ\|/(4π∫w)` over weights supported in the interval |
| Carneiro–Milinovich–Soundararajan | `22/25` | weights negative outside the interval, paid for by an explicit Brun–Titchmarsh inequality |

So `22/25` is out of reach of any weight supported in `[x, x + c√x log x]`: such weights stop at
`≈ 0.925`. CMS go below by letting the weight extend past the interval and bounding the primes
there with Montgomery–Vaughan's `π(x+y) − π(x) < 2y/log y`. Their proof needs (i) the
explicit formula for their band-limited kernel (their Lemma 9, for
`Σ Λ(n)n^{−1/2}cos(ϑ log(a/n))`; erdos-985 has the explicit formula only for `Ψ₁`-type weights),
(ii) an explicit `N(T)` (their Lemma 10 is Trudgian's; Rosser's, proved in schoenfeld-rh,
`|N(T) − (T/2π)log(T/2πe) − 7/8| < 0.137 log T + 0.443 log log T + 1.588`, would do), (iii) the
Brun–Titchmarsh inequality (large sieve or Selberg sieve; not in Mathlib) and (iv) a certified
value of their extremal ratio `J(F) ≥ 25/22`. They assume `x ≥ 4·10^18` only to cover the rest
with the gap computation of Oliveira e Silva, Herzog and Pardi. Their final inequality,
`(cJ/2) log x ≤ ½ log x − log((c log 2/2) log x) + 1.16 + E(x)`, is contradictory as soon as
`log(0.305 log x) > 1.16 + E(x)`, where `E(x)` collects the prime-power and discretisation terms
they bounded using `x ≥ 4·10^18`; with those terms recomputed at finite `x` (the prime powers cost
`≈ 2(log x + 1)³/(log 2 · √x)`) the analytic part would work from about `x ≈ 3·10^9`, and the
range below needs a chain of about 5,700 primes, well within reach of the kernel checks used here.
This sizing was done for this repository, not by CMS, and is not checked in Lean.

### Mean square: `O`-constants and the asymptotic's error term

The three mean-square bounds are `IsBigO` statements with an existential constant; it is not
computed (it passes through erdos-233's zero-density constant). Brent–Platt–Trudgian's `0.8603`
for `lim sup X^{-2} ∫_X^{2X} (ψ − x)²` is not proved. The asymptotic
`∫_1^X ((ψ − x)/x)² ∼ c₁ log X` is proved with the exact constant `c₁`, with an `o(log X)`
error: Montgomery–Vaughan's `O(1)` error term is not proved, and the numerical value
`c₁ ≈ 0.046` is not computed in Lean.

### Analytic thresholds `10^6`, `6.4·10^7` and `10^8`

The exact form of the Step 6 inequality already holds with
`c = 2` from about `1.9·10^3`; Step 7 uses simpler polynomial bounds that need `x ≥ 10^6`. The
range below is covered by the 99-prime chain, so no cited computation remains.

For `3/2` the threshold comes from the error in the sharp bound: `h/a ≤ 1/400` is needed for the
polynomial inequality of Step 3, i.e. `√x/log x ≳ 300`, and `x ≥ 6.4·10^7` (`t = x^{1/6} ≥ 20`)
makes Step 5 clean. Below it the 696-prime chain checks every gap; no cited computation remains.

For `107/100` the threshold `10^8` comes from the majorant, which is checked for `ε = h/m ≤ 1/800`;
`ε ≈ 0.535 log x/√x` drops below `1/800` near `6·10^7`. The exact inequality of Step 6 holds with
a wide margin from `10^6` on. Below `10^8` the 1176-prime chain checks every gap.

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

The mean-square modules (2026-11-24, on a box at load average about 80): erdos-233's
modules took about 3 min wall to build here; each of `Cramer.MeanSquare.{Coeff, Explicit, Psi,
Block, Main}` elaborates in about 15 s wall. They use no `native_decide` and no finite computation.

The asymptotic modules (same box and load): `Cramer.MeanSquare.Approx` 25 s,
`Finite` 14 s, `Asymptotic` 16 s, the others under 10 s each; `lake build` of the whole
library after a change to them took 42 s wall.

The constant-`3/2` modules (same box, load average about 80): `Cramer.Sharp.Small`
about 40 s wall (62 s CPU: kernel `decide` over the 696-entry chain and 696 `norm_num`
primality proofs, in 18 chunks), `Cramer.Sharp.Large` about 33 s, the others under 20 s each;
`lake build` of the whole library with them took 1 min 16 s wall.

The constant-`107/100` modules (same box, load average about 80): `Cramer.Shift.Data`
393 s wall (kernel `decide` over the 4033 cells, 53 Lorentzian pairs each, in 10 chunks),
`Cramer.Shift.Small` 182 s (the 1176-entry chain and 1176 `norm_num` primality proofs),
`Cramer.Vendor.Digamma` about 10 s, the others under 40 s each; `lake build` of the whole
library with them took 7 min 7 s wall.

## Unconditional version

`Unconditional/CramerUnconditional.lean` proves Cramér's gap bound with constant `107/100` (and
`3/2`, `2`) and his mean-square bounds and asymptotic unconditionally in Lean, with the certified
proof of RH. It imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and discharges the hypothesis with `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `cramer_primeInShortInterval_107` | `Cramer.PrimeInShortInterval (107 / 100)` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeGapExplicit_107` | `Cramer.PrimeGapExplicit (107 / 100)` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeInClosedInterval_107` | `Cramer.PrimeInClosedInterval 2 (107 / 100)` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeInShortInterval_three_halves` | `Cramer.PrimeInShortInterval (3 / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeGapExplicit_three_halves` | `Cramer.PrimeGapExplicit (3 / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeInClosedInterval_three_halves` | `Cramer.PrimeInClosedInterval 2 (3 / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeInShortInterval` | `Cramer.PrimeInShortInterval 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_primeGapExplicit` | `Cramer.PrimeGapExplicit 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_gapBound` | `Cramer.CramerGapBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_dyadicMeanSquare` | `Cramer.CramerDyadicMeanSquare` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_meanSquare` | `Cramer.CramerMeanSquare` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_logMeanSquare` | `Cramer.CramerLogMeanSquare` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_logMeanSquareAsymptotic` | `Cramer.CramerLogMeanSquareAsymptotic` | `propext`, `Classical.choice`, `Quot.sound` |

```
scripts/check-unconditional.sh [RH_DIR]
```

Run on 2026-11-24 against riemann-hypothesis `507a75d91d` (cache build, not `RH_FULL_BUILD`),
library and `Unconditional/` as of cramer-rh commit `3ab896d` (constant `107/100`
included); 14 min 31 s wall, most of it restoring and loading the RH cache. Output:

```
'cramer_primeInShortInterval' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeGapExplicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_gapBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_dyadicMeanSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_meanSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_logMeanSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_logMeanSquareAsymptotic' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeInShortInterval_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeGapExplicit_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeInClosedInterval_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeInShortInterval_107' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeGapExplicit_107' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_primeInClosedInterval_107' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `ulimit -n 2000000` or `nofile` in `/etc/security/limits.conf`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* [erdos-985](https://github.com/senamakel/erdos-985) (`9538edb`, lake dependency): the weighted
  explicit formula `explicit_formula_zeta`, Hadamard's factorisation `hadamard_logDeriv`, the
  digamma bounds and the numerics for `ξ`. Same author, no licence file yet.
* [erdos-233](https://github.com/senamakel/erdos-233) (`1ff9f39`, lake dependency, mean square
  only): `psi1`, its real-`x` explicit formula `psi1_formula`, `zero_density`, `mean_value`,
  `series_bound` and the `CoeffAux` derivative bounds. `Cramer/MeanSquare/Coeff.lean`
  (`sq_log_sums`) and `Cramer/MeanSquare/Block.lean` (`G_mean_square`) adapt the proofs of
  erdos-233's `coef_sums` and `mean_square`. Same author, no licence file yet.
* `Cramer/MeanSquare/Zeros.lean` repeats the proofs of `xiZeta_eq_zero_of_mem` and
  `mem_strip_of_xiZeta_eq_zero` from [li-criterion-rh](https://github.com/senamakel/li-criterion-rh)
  `LiCriterion/Zeros.lean` and of `analyticOrderNatAt_riemannZeta_eq_xiZeta` from
  [density-rh](https://github.com/senamakel/density-rh) `Density/ZeroCount/Xi.lean`. Same author.
* `Cramer.xiZeta_ne_zero_of_half_lt_RH` and `Cramer.xiZeta_zero_re_RH` (`Cramer/ZeroSum.lean`)
  repeat the proofs of the same-named lemmas in
  [robin-rh](https://github.com/senamakel/robin-rh) `Robin/RH/Bach.lean`. Same author.
* `primeGap` and the `CramerGapBound` statement: google-deepmind/formal-conjectures, commit
  `86a2f58a`, Apache License 2.0.
* `Cramer/Vendor/Digamma.lean`: Dirichlet's integral for `ψ` and the bound
  `Re ψ(σ + it) ≤ log σ + ½ log(1 + t²/(σ−1)²)` (`re_digamma_le`), vendored from
  [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach)
  `TernaryGoldbach/Explicit/Digamma.lean` at commit `330a61c7`, Copyright 2026 Charlie Reams,
  Apache License 2.0; the licence and NOTICE are in `Cramer/Vendor/`. Changes: namespace, the
  file stops at `re_digamma_le`, two `fun_prop` continuity steps written out for this Mathlib pin.
* Nothing is vendored from riemann-hypothesis; it is imported only by `Unconditional/`.
