# Cramér's prime-gap and mean-square theorems under RH in Lean

This project proves in Lean Carneiro, Milinovich and Soundararajan's prime-gap theorem under RH:
every interval `[x, x + (22/25)√x log x]` with `x ≥ 4` contains a prime, so
`p_{n+1} − p_n ≤ (22/25)√p_n log p_n` for every prime `p_n > 3` and
`p_{n+1} − p_n = O(√p_n log p_n)`. It also proves Cramér's mean-square theorems for `ψ(x) − x`:
`∫_1^X (ψ(x) − x)² dx ≪ X²`, its dyadic and logarithmic forms, and the asymptotic
`∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X` with `c₁ = Σ_ρ m_ρ/|ρ|²`. `Unconditional/` proves all of
them unconditionally in Lean from the standard three axioms, with RH supplied by the certified
proof of L. Alpöge (2026). The main library holds complete Lean proofs that RH implies each one.

The prime-gap bound is Cramér's (1920, *Arkiv för Matematik, Astronomi och Fysik* **15**, no. 5).
The constant `22/25` and the range `x ≥ 4` are Carneiro, Milinovich and Soundararajan's (2019,
*Comment. Math. Helv.* **94**, 533-568, Theorem 5), the best explicit form in the literature.
Earlier ones are Dudek's `4/π ≈ 1.273` (2015, *Int. J. Number Theory* **11**, 771-778; a prime in
`(x − (2/π)√x log x, x + (2/π)√x log x)`, as quoted by Dudek, Grenié and Molteni) and Dudek,
Grenié and Molteni's half-width `(1/2 + 2/log x)√x log x` for `x ≥ 2` (2016, *Int. J. Number
Theory* **12**, 1391-1407, Theorem 1.1). The proof of `22/25` follows Carneiro, Milinovich and
Soundararajan's strategy with a different weight and Brun–Titchmarsh from the large sieve; see
"Deviations from the literature". The repository also keeps gap theorems with the constants
`107/100`, `3/2` and `2` on `(x, x + c√x log x]`, `x ≥ 2`. Without RH the best
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

The `22/25` bound uses a weight that extends past the interval and is negative there; the
primes outside the gap are bounded by Montgomery and Vaughan's large-sieve Brun–Titchmarsh
inequality, and the zero sum through Rosser's `N(T)` and a step majorant certified on 7076
cells. The earlier gap bounds follow Cramér (1920) through a triangular (Fejér-type) weight, the
second difference of `ψ₁`. The constant `107/100` comes from bounding each zero's contribution by its
size `h²m^{−1/2} sin²x/x²` (`x = γh/2m`, `m` the centre of the interval) up to an `O(h/(mx))`
error, and majorising that by 53 pairs of Lorentzians centred at `±τ`, which Hadamard's product
at complex points sums exactly. The mean square goes through the explicit formula and the
convergence of `Σ_ρ log|γ|/|ρ|²`, as in the classical proof.

```lean
theorem cramer_cmsPrimeInterval : Cramer.CMSPrimeInterval                          -- Unconditional/
theorem cramer_cmsPrimeGap : Cramer.CMSPrimeGap                                    -- Unconditional/
theorem cramer_meanSquare : Cramer.CramerMeanSquare                                -- Unconditional/
theorem cramer_logMeanSquareAsymptotic : Cramer.CramerLogMeanSquareAsymptotic      -- Unconditional/

theorem Cramer.cmsPrimeInterval_of_RH (hRH : RiemannHypothesis) : Cramer.CMSPrimeInterval

theorem Cramer.cmsPrimeGap_of_RH (hRH : RiemannHypothesis) : Cramer.CMSPrimeGap

theorem Cramer.primeInShortInterval_cms_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 5 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 22 / 25 * Real.sqrt x * Real.log x

theorem Cramer.cramer_of_RH (hRH : RiemannHypothesis) : Cramer.CramerGapBound

theorem Cramer.dyadicMeanSquare_of_RH (hRH : RiemannHypothesis) :
    Cramer.CramerDyadicMeanSquare

theorem Cramer.meanSquare_of_RH (hRH : RiemannHypothesis) : Cramer.CramerMeanSquare

theorem Cramer.logMeanSquare_of_RH (hRH : RiemannHypothesis) : Cramer.CramerLogMeanSquare

theorem Cramer.logMeanSquareAsymptotic_of_RH (hRH : RiemannHypothesis) :
    Cramer.CramerLogMeanSquareAsymptotic
```

The repository also keeps the gap theorems with the constants `107/100`, `2` and `3/2`, which use
triangular weights and Lorentzian majorants (see "Proof outline"):

```lean
theorem Cramer.primeInShortInterval_107_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInShortInterval (107 / 100)

theorem Cramer.primeGapExplicit_107_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeGapExplicit (107 / 100)

theorem Cramer.primeInClosedInterval_107_of_RH (hRH : RiemannHypothesis) :
    Cramer.PrimeInClosedInterval 2 (107 / 100)

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
has its own definition. `CMSPrimeInterval` and `CMSPrimeGap` are proved
(`cmsPrimeInterval_of_RH`, `cmsPrimeGap_of_RH`); `PrimeInClosedInterval` also carries the
`107/100` and `3/2` theorems:

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
| `Cramer.cmsPrimeInterval_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `Cramer.cmsPrimeGap_of_RH` | C | `RiemannHypothesis` |
| `Cramer.primeInShortInterval_cms_of_RH` | C | `RiemannHypothesis` |
| `cramer_cmsPrimeInterval` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `cramer_cmsPrimeGap` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
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
forms `PrimeInShortInterval` and `PrimeGapExplicit` are this repository's own; `CMSPrimeInterval`
and `CMSPrimeGap` transcribe Carneiro–Milinovich–Soundararajan's Theorem 5 and the sentence
before it (formal-conjectures has no statement of either). So are the
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
'Cramer.cmsPrimeInterval_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cramer.cmsPrimeGap_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/check-axioms.sh` reruns this and fails unless all fifteen use only the standard axioms.
No `sorry`, no `native_decide`, no `axiom` declarations. The finite checks (`Cramer/Small.lean`,
`Cramer/Sharp/Small.lean`, `Cramer/Shift/Small.lean`, `Cramer/Shift/Data.lean`,
`Cramer/Shift/Facts.lean`, `Cramer/CMS/Small.lean`, `Cramer/CMS/ZeroBound.lean`,
`Cramer/CMS/PrimeSide.lean` and the 708 modules `CramerCompute/CMSData/W*.lean`) use kernel
`decide` (`decide +kernel` for the prime chains, the 4033 majorant cells and the 7076 CMS
cells) and `norm_num`, which add no axioms.

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

### Constant `22/25` (Carneiro–Milinovich–Soundararajan)

Files are in `Cramer/CMS/` and `CramerCompute/`. The weight has knots `n_j = B + js`,
`j = 0, …, 32`, `s = 8s'`; it is `w(n) = Σ_j a_j max(n_j − n, 0)`, `a_j` the second differences of
integers `c_j` (`φ` at scale `2^20`, symmetric about `j = 16`, `Σ c_j = 11989718`,
`Σ |a_j| = 740648`). It is positive on the gap `[n_8, n_24)` and negative outside.

1. Explicit formula (`Weight.lean`). `Σ_n Λ(n) w(n) = Σ_j a_j Ψ₁(n_j)`, and under RH
   `Σ_j a_j Ψ₁(n_j) ≥ s² Σ c_j − Z − (3/2) Σ |a_j|` whenever
   `Σ_ρ m_ρ ‖Σ_j a_j g_ρ(n_j)‖ ≤ Z`, `g_ρ(t) = t^{ρ+1}/(ρ(ρ+1))` (erdos-985's explicit formula).
2. Per zero (`PerZero.lean`, `Trig.lean`). With `m = n_16`, `θ = γs/m`,
   `‖Σ_j a_j g_ρ(n_j)‖ ≤ s² m^{−1/2}(A(θ)/θ² + errors)`, `A(θ) = (2 − 2cos θ)|Q(cos θ)|`, `Q` a
   degree-16 polynomial with integer Chebyshev coefficients; three forms (`θ ≤ 1`, decaying like
   `θ^{−2}`, trivial).
3. Cells (`Taylor.lean`, `Cells.lean`, `CramerCompute/CMSCheck.lean`). 7076 cells cover
   `θ ∈ [0, 120]`; on each, `cos` is enclosed by Taylor polynomials of degree 13 and 14 after
   reduction by `3.14159265358979323846 < π < 3.14159265358979323847`, and `|Q|` by an exact
   Taylor shift at the midpoint, all in integer arithmetic (scales `2^20`, `2^64`, `2^40`). The
   checks run by kernel `decide` in 708 Lean-core-only modules of 11 cells each
   (`CramerCompute/CMSData/`), glued in `Glue.lean` and `CramerCompute/CMSAll.lean`; `chk_sound`
   proves the check sound.
4. Zero sum (`ZeroSum.lean`, `Assembly.lean`, `ZeroBound.lean`). Abel summation of the step
   majorant against Rosser's `N(T)` (schoenfeld-rh's `rosserZeroCount`), and
   `Σ_{γ>T} m_ρ/γ² ≤ τ(T)/T` beyond `θ = 120`, give `Z ≤ s² m^{−1/2} Zc(s/m)` (`zeroBound`), with
   `Zc` explicit in the certified sums.
5. Brun–Titchmarsh (`BrunTitchmarsh.lean`). For `√(2N/3) ≤ M₀`, the primes in `(M₀, M₀ + N]`
   number at most `N/W(√(2N/3))`, `W(R) ≥ log(R − 1) + 1/2 − log 2`: Montgomery's inequality and
   the weighted large sieve over the Farey points (vendored, see Credits).
6. Prime side (`PrimeSide.lean`). If no prime lies in the gap,
   `Σ Λ(n) w(n) ≤ s'² log n_32 · 18838744/W + s' · 8388608 · (prime powers)`, from step 5 on each
   of the 128 pieces of length `s'` outside the gap (16 segments, 8 pieces each).
7. Analytic range (`Final.lean`, `FinalPoly.lean`, `Large.lean`). For `x ≥ 10^8`,
   `s' = ⌊(q − 2)/128⌋`, `q = (22/25)√x log x`, `B = ⌊x⌋ + 1 − 64s'`, so the gap lies in
   `(x, x + q]`. With `t = log x` every term is bounded by a rational function of `t`, and the
   contradiction is `Mb + EVb + Cb + BTb + PPt + 11 < 11989718` (`final_poly`), whose numerator
   has positive coefficients in `t − 18`. The margin is `2.4·10^6` at `t = 18` and `1.0·10^5`
   (`0.9%`) as `t → ∞`.
8. Finite range (`Small.lean`). A chain of 1426 primes from 5 to 100044563 with
   `q_{i+1} − q_i ≤ (22/25)√q_i log q_i` (`scripts/cms_chain.py`); `x ∈ [4, 5)` takes `p = 5`.
9. Assembly (`Cramer/Main6.lean`). The prime found is `> x` for `x ≥ 5`
   (`primeInShortInterval_cms_of_RH`), which gives the gap form.

The data generators are in `scripts/cms/`; `scripts/cms_gen.py` lists the pipeline.

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
| `Cramer/CMS/Weight.lean` | Constant `22/25`, Step 1: the weight and its explicit formula |
| `Cramer/CMS/PerZero.lean` | Step 2: the three per-zero bounds |
| `Cramer/CMS/Trig.lean` | Step 2: `‖Σ a_j e^{ijθ}‖ = (2 − 2cos θ)\|Q(cos θ)\|` |
| `Cramer/CMS/Taylor.lean` | Step 3: `cos` Taylor enclosures |
| `Cramer/CMS/Cells.lean` | Step 3: soundness of the integer cell check |
| `Cramer/CMS/Glue.lean` | Step 3: gluing the checked windows |
| `CramerCompute/CMSCheck.lean` | Step 3: the cell check (Lean core only) |
| `CramerCompute/CMSData/` | Step 3: `Q` and 708 windows of 11 cells, each checked by `decide` (generated) |
| `CramerCompute/CMSAll.lean` | Step 3: the glued windows and their sums (generated) |
| `Cramer/CMS/ZeroSum.lean` | Step 4: Abel summation against Rosser's `N(T)`, the tail |
| `Cramer/CMS/Assembly.lean` | Step 4: the zero sum from the cells |
| `Cramer/CMS/ZeroBound.lean` | Step 4: `zeroBound` with the certified constants |
| `Cramer/CMS/BrunTitchmarsh.lean` | Step 5 |
| `Cramer/CMS/PrimeSide.lean` | Step 6 |
| `Cramer/CMS/Final.lean` | Step 7: each term as a function of `t = log x` |
| `Cramer/CMS/FinalPoly.lean` | Step 7: the closing polynomial inequality |
| `Cramer/CMS/Large.lean` | Step 7 (`x ≥ 10^8`) |
| `Cramer/CMS/Small.lean` | Step 8: the 1426-prime chain (generated) |
| `Cramer/Main6.lean` | Headline theorems (constant `22/25`) |
| `Cramer/Vendor/LS/` | Montgomery's inequality and the weighted large sieve, vendored from calr3/ternary-goldbach |
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

### Constant `22/25`: the route differs from Carneiro–Milinovich–Soundararajan's

`cmsPrimeInterval_of_RH` is their Theorem 5 with their constant `22/25`, their closed interval
and their range `x ≥ 4`; `cmsPrimeGap_of_RH` is the gap form for `p_n > 3`. The proof follows
their strategy (a weight that is negative outside the interval, Brun–Titchmarsh for the primes
there, an explicit `N(T)` for the zeros) but not their details:

| | Carneiro–Milinovich–Soundararajan | here |
|---|---|---|
| Weight | band-limited extremal function, explicit formula of their Lemma 9 | piecewise linear, 33 knots, second differences of `Ψ₁` (erdos-985's explicit formula) |
| Extremal ratio | `1/J(F) < 22/25` | linear-program optimum `J = 1.1569`, `1/J = 0.8644`; the certified zero-sum constant is `0.5%` above the exact one |
| Brun–Titchmarsh | Montgomery–Vaughan, `π(x+y) − π(x) < 2y/log y` | the large-sieve form `N/W(√(2N/3))`, `W(R) ≥ log(R − 1) + 1/2 − log 2` |
| `N(T)` | Trudgian's (their Lemma 10) | Rosser's (schoenfeld-rh `rosserZeroCount`) |
| Analytic range | `x ≥ 4·10^18` | `x ≥ 10^8` |
| Below it | the gap computation of Oliveira e Silva, Herzog and Pardi | a chain of 1426 primes checked in Lean |

The weight was found by a linear program (`scripts/cms/design2.py`). Without the
Brun–Titchmarsh term its optimum is `J ≈ 1.0835` (constant `≈ 0.923`, above `22/25`); with it,
and 8 sub-pieces per segment, `J = 1.1569`. The final margin is `0.9%` of the main term as
`x → ∞`, and larger below.

The earlier constants `107/100` (`Cramer/Shift/`), `3/2` (`Cramer/Sharp/`) and `2` use the
triangular weight on `[a, a+2h]`, whose transform at a zero is `‖D_ρ‖ ≈ h²m^{−1/2} sin²x/x²`,
`x = γh/2m`, summed over zeros through Hadamard's product with a Lorentzian majorant `M`; the
constant is `∫M/π`. Weights supported inside the interval cannot go below about `0.925`, which is
why `22/25` needs the weight to extend past it.

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

For `22/25` the threshold `10^8` is where the explicit terms (Rosser's error term, the prime
powers, the discretisation of the weight) fit inside the `0.9%` margin with the simple bounds of
`Cramer/CMS/Final.lean` (`√x ≥ 29(log x)²`, `x^{1/6} ≥ 3.3(log x − 12)`). Below it the
1426-prime chain checks every gap.

For `107/100` the threshold `10^8` comes from the majorant, which is checked for `ε = h/m ≤ 1/800`;
`ε ≈ 0.535 log x/√x` drops below `1/800` near `6·10^7`. The exact inequality of Step 6 holds with
a wide margin from `10^6` on. Below `10^8` the 1176-prime chain checks every gap.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`); erdos-233 at `1ff9f39` for the
mean square; schoenfeld-rh at `b2c3137` for Rosser's `N(T)` (constant `22/25`). Building
schoenfeld-rh's vendored Rosser proof from cold costs about 3 CPU-hours.

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

The constant-`22/25` modules (2026-11-25, same box under load): the 708 window modules
`CramerCompute.CMSData.W*` took about 3260 s of summed module time (kernel `decide`, 11 cells
each; one window per module, because kernel time grows faster than linearly within a module),
`CramerCompute.CMSAll` 7 s, `Cramer.CMS.Small` 146 s (the 1426-entry chain and its primality
proofs).

## Unconditional version

`Unconditional/CramerUnconditional.lean` proves the gap bound with Carneiro, Milinovich and
Soundararajan's constant `22/25` (and `107/100`, `3/2`, `2`), Cramér's mean-square bounds and
the asymptotic unconditionally in Lean, with the certified proof of RH. It imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and discharges the hypothesis with `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `cramer_cmsPrimeInterval` | `Cramer.CMSPrimeInterval` | `propext`, `Classical.choice`, `Quot.sound` |
| `cramer_cmsPrimeGap` | `Cramer.CMSPrimeGap` | `propext`, `Classical.choice`, `Quot.sound` |
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

Run on 2026-11-25 against riemann-hypothesis `507a75d91d` (cache build, not `RH_FULL_BUILD`),
library and `Unconditional/` as of cramer-rh commit `fb22f0a` (constant `22/25` included);
about 15 min wall on a loaded box, most of it restoring and loading the RH cache. Output:

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
'cramer_cmsPrimeInterval' depends on axioms: [propext, Classical.choice, Quot.sound]
'cramer_cmsPrimeGap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `ulimit -n 2000000` or `nofile` in `/etc/security/limits.conf`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* [erdos-985](../erdos-985/) (`9538edb`, lake dependency): the weighted
  explicit formula `explicit_formula_zeta`, Hadamard's factorisation `hadamard_logDeriv`, the
  digamma bounds and the numerics for `ξ`. Same author, no licence file yet.
* [erdos-233](../erdos-233/) (`1ff9f39`, lake dependency, mean square
  only): `psi1`, its real-`x` explicit formula `psi1_formula`, `zero_density`, `mean_value`,
  `series_bound` and the `CoeffAux` derivative bounds. `Cramer/MeanSquare/Coeff.lean`
  (`sq_log_sums`) and `Cramer/MeanSquare/Block.lean` (`G_mean_square`) adapt the proofs of
  erdos-233's `coef_sums` and `mean_square`. Same author, no licence file yet.
* `Cramer/MeanSquare/Zeros.lean` repeats the proofs of `xiZeta_eq_zero_of_mem` and
  `mem_strip_of_xiZeta_eq_zero` from [li-criterion-rh](../li-criterion-rh/)
  `LiCriterion/Zeros.lean` and of `analyticOrderNatAt_riemannZeta_eq_xiZeta` from
  [density-rh](../density-rh/) `Density/ZeroCount/Xi.lean`. Same author.
* `Cramer.xiZeta_ne_zero_of_half_lt_RH` and `Cramer.xiZeta_zero_re_RH` (`Cramer/ZeroSum.lean`)
  repeat the proofs of the same-named lemmas in
  [robin-rh](../robin-rh/) `Robin/RH/Bach.lean`. Same author.
* `primeGap` and the `CramerGapBound` statement: google-deepmind/formal-conjectures, commit
  `86a2f58a`, Apache License 2.0.
* `Cramer/Vendor/Digamma.lean`: Dirichlet's integral for `ψ` and the bound
  `Re ψ(σ + it) ≤ log σ + ½ log(1 + t²/(σ−1)²)` (`re_digamma_le`), vendored from
  [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach)
  `TernaryGoldbach/Explicit/Digamma.lean` at commit `330a61c7`, Copyright 2026 Charlie Reams,
  Apache License 2.0; the licence and NOTICE are in `Cramer/Vendor/`. Changes: namespace, the
  file stops at `re_digamma_le`, two `fun_prop` continuity steps written out for this Mathlib pin.
* `Cramer/Vendor/LS/` (7 files): Montgomery's inequality (`montgomery_ineq`), the
  Montgomery–Vaughan weighted large sieve (`large_sieve_weighted`, with Shan's spacing lemma and
  the Hilbert-inequality files behind it) and `Σ_{n ≤ t} 1/n ≤ Σ_{r ≤ t squarefree} 1/φ(r)`,
  vendored from [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) at commit
  `330a61c`, Copyright 2026 Charlie Reams, Apache License 2.0 (licence and NOTICE in
  `Cramer/Vendor/`). Namespace renamed, one proof repair; the file list and changes are in
  `Cramer/Vendor/LS/PORTING.md`. `Cramer/CMS/BrunTitchmarsh.lean` copies `frac_sep` and
  `le_dist_round_of_forall` from the same commit's `TernaryGoldbach/MinorArcs/TypeII.lean`.
* [schoenfeld-rh](../schoenfeld-rh/) (`b2c3137`, lake dependency,
  constant `22/25` only): `rosserZeroCount` (Rosser's `N(T)`), the zero-sum lemmas of
  `Schoenfeld.ZeroSums` used for the tail, and the exponential `e` of its vendored
  `TernaryGoldbach.CircleMethod`. Same author; its vendored files carry their own licences.
* Nothing is vendored from riemann-hypothesis; it is imported only by `Unconditional/`.
