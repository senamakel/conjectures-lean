# Powerful numbers: the error term below `x^{1/6}` under RH

Written 2026-11-24. Research only: no repo was edited and lake was not run. Every claim is
checked against a primary source unless it is marked (unverified).

**Short answer.** "RH ⇒ the Bateman–Grosswald error term is `O(x^{1/6−δ})`" is a **published
theorem**: Suryanarayana and Sitaramachandra Rao, Ark. Mat. 11 (1973) 195–201, Theorem 3.2 and
Corollary 3.2, which give `O(x^{13/81+ε})`. At least seven later papers improve the exponent
under RH. The label is **RH-consequence**, verdict **(a)**. Bateman and Grosswald (1958) also
remarked that an exponent below `1/6` should be possible *if and only if* ζ has a zero-free
half-plane `Re s > 1 − η`. So the formal-conjectures "open" statement is open for the same
reason quasi-RH is open, and an unconditional proof through riemann-hypothesis would prove
nothing beyond that repo's claim.

The cost question has a definite answer: **the elementary lattice-point bound is not enough.**
The two-dimensional count `#{a²b³ ≤ y}` must have error `O(y^θ)` with `θ < 1/6`. Elementary
methods give `θ = 1/5`, and with `θ = 1/5` no Möbius bound, RH included, gets below
`x^{1/5}`. An exponential-sum estimate is needed: at least van der Corput's second-derivative
test, with Kusmin–Landau and a Fourier truncation of `ψ`. Mathlib has none of these. That one
module is the cost. Everything else is M.

---

## 1. The problem

**Source.** formal-conjectures `FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean` at
`main` = `86a2f58a`, fetched with `gh api` on 2026-11-24. Last change to the file: `7db2ea3b`
(2026-10-14), "chore: remove prop valued `answer(...)`s (#6762)". **The `answer(sorry) ↔`
wrapper the brief mentions is gone.** The open statement is now a plain existential, so proving
it outright settles it. There's no yes/no answer to supply.

Definitions, verbatim:

```lean
/-- $Q(x)$ is the number of powerful integers $n$ with $1 \le n \le x$. -/
noncomputable abbrev Q (x : ℝ) : ℕ := {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x}.ncard

/-- The leading constant $\zeta(3/2)/\zeta(3) = 2.173\ldots$ -/
noncomputable abbrev A : ℝ := (riemannZeta (3 / 2)).re / (riemannZeta 3).re

/-- The second-order constant $\zeta(2/3)/\zeta(2)$, where $\zeta(2/3)$ is given by analytic
continuation. -/
noncomputable abbrev B : ℝ := (riemannZeta (2 / 3)).re / (riemannZeta 2).re
```

`Nat.Powerful` is `(2).Full` from `FormalConjecturesForMathlib/Data/Nat/Full.lean`, where
`def Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n`. It is not in Mathlib `fc4f59e5`,
so copy it verbatim into `Statement.lean` (rule 2). Note that `ζ(2/3) < 0` (about −2.45,
unverified numerically), so `B < 0`.

The three theorems, verbatim:

```lean
@[category research solved, AMS 11]
theorem asymptotic_erdos_szekeres :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 3) := by
  sorry

@[category research solved, AMS 11]
theorem asymptotic_bateman_grosswald :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 6) := by
  sorry

/--
Can the exponent $1/6$ in the error term of the Bateman–Grosswald asymptotic be improved
unconditionally? ... Improvements are known under the Riemann Hypothesis.
-/
@[category research open, question, AMS 11]
theorem error_term_improvement :
    ∃ δ > (0 : ℝ),
      (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
        fun x => x ^ ((1 : ℝ) / 6 - δ) := by
  sorry
```

`asymptotic_bateman_grosswald` is also listed in `FormalConjectures/Subsets/FC100SolvedSet2.lean`,
a list of solved statements waiting for a Lean proof. No `formal_proof` attribute is attached
to any of the three. A GitHub code search for `PowerfulNumbersDensity` /
`asymptotic_bateman_grosswald` and a repo search for "powerful numbers lean" (2026-11-24) found
only formal-conjectures itself and review-bot data dumps. No Lean proof of any of the three
was found.

**Status.** Unconditionally the exponent `1/6` has not been improved. Bateman–Grosswald 1958
and Suryanarayana–Sitaramachandra Rao 1973 only save a factor `exp(−c log^{3/5} x (log log x)^{−1/5})`.
Liu (Ark. Mat. 1994) says: "The above estimate cannot be improved unconditional due to our
current knowledge concerning the zero-free region of the zeta-function."

## 2. What is already known

Notation: `Δ(x) = Q(x) − A x^{1/2} − B x^{1/3}`. `Δ_{2,3}(y)` is the error in
`#{(a,b) ∈ ℕ²_{≥1} : a²b³ ≤ y} = ζ(3/2) y^{1/2} + ζ(2/3) y^{1/3} + Δ_{2,3}(y)`. `θ` is any
exponent with `Δ_{2,3}(y) ≪ y^θ`.

### Unconditional

| Result | Source | Status |
|---|---|---|
| `Q(x) = A x^{1/2} + O(x^{1/3})` | Erdős–Szekeres, Acta Sci. Math. (Szeged) 7 (1935) 95–102 | quoted by SS 1973 §1 (eq. 1.1) |
| `Δ(x) = O(x^{1/5})`, by Euler–Maclaurin | Bateman, 1954 (venue unverified) | quoted by SS 1973 (eq. 1.2) |
| `Δ(x) = O(x^{1/6} exp(−A log^{4/7}x (log log x)^{−3/7}))` | Bateman–Grosswald, Illinois J. Math. 2 (1958) 88–98, §5 | quoted by SS 1973 (eq. 1.5); paper not read directly |
| `Δ(x) = O(x^{1/6} exp(−A log^{3/5}x (log log x)^{−1/5}))` | SS 1973, Theorem 3.1 | read (PDF via archive.ymsc.tsinghua.edu.cn) |
| `θ ≤ 2/15` for `Δ_{2,3}` (van der Corput method); `θ ≥ 1/10` (Ω-result) | Richert, "Satz 2" (Math. Z., 1952, unverified); Krätzel, "Satz 7" (unverified) | quoted by SS 1973: "It is known that 1/10 ≤ θ ≤ 2/15" |
| `θ = 14/107 + ε` | Liu, Acta Arith. 64 (1993) 129–149, §4 | read (abstract and intro) |

The Bateman–Grosswald remark, as SS 1973 quotes it (I did not read BG directly): "one can
expect to get an estimate of the form `Δ(x) = O(x^α)`, `α` fixed `< 1/6` if and only if the
least upper bound of the real parts of the zeros of the Riemann Zeta function is less than
unity" (BG, p. 95, lines 30–31). The "only if" half is stated as an expectation and is not
proved there (unverified).

### Under RH

| Exponent | Authors, venue | Checked |
|---|---|---|
| `(1−θ)/(7−12θ)+ε`, so `13/81+ε ≈ 0.1605` with `θ = 2/15` | **Suryanarayana, Sitaramachandra Rao, "The distribution of square-full integers", Ark. Mat. 11 (1973) 195–201, Theorem 3.2, Cor. 3.1, 3.2** | read in full |
| `151/992+ε ≈ 0.1522` | Nowak–Schmeier, Proc. AMS 103 (1988) 713–717, §3.3, via Montgomery–Vaughan's idea and Schmidt's `θ = 27/205` | read (§3.3 text) |
| `5/33+ε ≈ 0.1515` | X. Cao, Period. Math. Hungar. 28 (1994) 43–54 | via zbMATH review of Cai |
| `9/58+ε ≈ 0.1552` | H.-Q. Liu, Ark. Mat. 32 (1994), "The distribution of square-full integers" | read (intro, Lemma 1). It is weaker than Cao's 5/33; the two were presumably independent |
| `4/27+ε ≈ 0.1481` | Y. Cai, Acta Math. Sinica (Engl.) 13 (1997) 269–280 | zbMATH review |
| `1/7+ε ≈ 0.1429` | X. Cao, Period. Math. Hungar. 34 (1997) 169–175 | zbMATH review (J. Hinz) |
| (exponent unverified) | J. Wu, Monatsh. Math. 126 (1998) 353–367; Arch. Math. 77 (2001) | titles only |
| `121/860+ε ≈ 0.1407` | H.-Q. Liu, J. Number Theory 159 (2016) 176–192 | as cited by Sankaranarayanan–Akhilesh |
| explicit zero sum + `O(x^{1/12+ε})`, assuming RH and simple zeros | Sankaranarayanan–Akhilesh, arXiv:2609.02327 (Sept 2026) | read (abstract, Thm 1.2) |

Also: Suryanarayana, Period. Math. Hungar. (1983), proves the mean `(1/x)∫|Δ| ≪ x^{1/10+ε}`
under RH and conjectures `Δ(x) ≪ x^{1/10+ε}`.

### The key question: is RH ⇒ (target) published?

**Yes, with a full proof.** SS 1973, Corollary 3.2: *"If the Riemann hypothesis is true, then
Δ(x) = O(x^{13/81+ε}), for every ε > 0."* Since `13/81 < 1/6`, this implies
`error_term_improvement` with any `δ < 1/6 − 13/81 = 1/486`. The authors call their proof
"straightforward and elementary" given `θ ≤ 2/15`.

## 3. Genuineness verdict: **(a) published conditional theorem, we would formalise it**

Label **RH-consequence**: "RH implies `error_term_improvement`, following Suryanarayana and
Sitaramachandra Rao (1973)". In `Unconditional/` it would be "`error_term_improvement`, given
the unverified Lean proof of RH in riemann-hypothesis".

A careful analytic number theorist would say that the RH result is a 1973 exercise with
seven or more published improvements, and that the unconditional question is open *because* it
needs a zero-free half-plane for ζ (the Bateman–Grosswald remark). Discharging it with
riemann-hypothesis shows only that the formal-conjectures entry is downstream of RH, which
its own docstring already says. Nothing here is new mathematics. What is new is the Lean
artefact: the first formal proofs of all three statements in the file. Two of them,
`asymptotic_erdos_szekeres` and `asymptotic_bateman_grosswald`, come out **tier D, no RH**,
as by-products of the same machinery (see §4), but they carry the label *known* and are not
targets by themselves. Also new would be the first Lean van der Corput second-derivative test
for sums (a reusable tool; Mathlib PR #39406 covers only oscillatory *integrals*).

Do not write "settles an open formal-conjectures problem" in the README without the RH caveat.
Given BG's iff remark, it is honest to add that the statement is essentially a
zero-free-half-plane statement.

## 4. Proof route

The route is SS 1973 §3, with any `θ < 1/6` and any Mertens exponent `α < 1`.

### The exponent arithmetic that decides the cost

Write `N(y) = #{(a,c) : a²c³ ≤ y}`. Every powerful `n` is uniquely `a²b³` with `b`
squarefree. Writing `μ²(b) = Σ_{d²|b} μ(d)` and `b = d²c` gives

  `Q(x) = Σ_{d ≤ x^{1/6}} μ(d) N(x/d⁶)`.

Split at `D ≤ x^{1/6}`:

- **S₁** = `Σ_{d≤D} μ(d) N(x/d⁶)`. Insert `N(y) = ζ(3/2)y^{1/2} + ζ(2/3)y^{1/3} + O(y^θ)`. The
  error is `Σ_{d≤D} (x/d⁶)^θ`.
  - If `6θ > 1`, this sum converges and the error is `≍ x^θ`. **With the elementary `θ = 1/5`
    the total error is at least `x^{1/5} > x^{1/6}` whatever the Möbius input.** The `d = 1`
    term alone is `N(x)`'s own error.
  - If `6θ < 1`, the error is `x^θ D^{1−6θ}`.
- **Main-term tails**: `x^{1/2} Σ_{d>D} μ(d)d^{−3} + x^{1/3} Σ_{d>D} μ(d)d^{−2}`. If
  `M(y) ≪ y^α`, partial summation gives `≪ x^{1/2}D^{α−3} + x^{1/3}D^{α−2}`. The first term
  dominates when `D ≤ x^{1/6}`.
- **S₂** = `Σ_{d>D} μ(d) N(x/d⁶) = Σ_{a²c³ ≤ x/D⁶} [M((x/a²c³)^{1/6}) − M(D)]`. This is
  `≪ x^{α/6} Σ_{a²c³≤Y}(a²c³)^{−α/6} + D^α N(Y)` with `Y = x/D⁶`. Both terms are
  `≪ x^{1/2} D^{α−3}`; the inner sum is `≪ Y^{1/2−α/6}` because `Σ_c c^{−3/2}` converges.

Balance `x^θ D^{1−6θ} = x^{1/2} D^{α−3}`. The total error exponent is then

  `E(θ, α) = θ + (1−6θ)(1/2−θ)/(4−α−6θ)`.

- `α = 1/2`: `E = (1−θ)/(7−12θ)`, SS's Theorem 3.2. `θ = 2/15` gives `13/81`.
- `α = 1` (the trivial `|M(y)| ≤ y`): `E = 1/6` exactly, for every `θ < 1/6`. **This is
  `asymptotic_bateman_grosswald`, unconditionally.** It needs `θ < 1/6` too, so it is no cheaper.
- `E < 1/6` ⇔ `α < 1` (with `θ < 1/6`). So a Mertens bound with *any* exponent below 1 is
  enough. That is the quantitative form of the BG remark.
- `θ = 1/6`: `E = 1/6` for every `α`. So **a nontrivial `θ < 1/6` is necessary on this route**,
  and an RH-strength Möbius bound cannot replace it.

Recommended concrete exponents. Prove `θ = 1/7`, which leaves room for logs over van der
Corput's `2/15`:

- with `α = 1/2+ε`: `E = 6/37 + O(ε)`, `δ ≈ 1/222`;
- with the weaker `α = 3/4`: `E = 11/67`, `δ = 1/402`.

### Why `θ < 1/6` needs exponential sums

The hyperbola method on `a²c³ ≤ y`, summing exactly over `c ≤ u` and over `a ≤ (y/u³)^{1/2}`,
leaves the error

  `−Σ_{c ≤ u} ψ((y/c³)^{1/2}) − Σ_{a ≤ v} ψ((y/a²)^{1/3}) + O(1)`, with `ψ(t) = {t} − 1/2`
  and `u³v² = y`.

The trivial bound is `u + v ≥ 2y^{1/5}`, at best at `u = v = y^{1/5}`. That is Bateman's `1/5`.
Getting below `y^{1/6}` requires cancellation in `Σ_{c∼C} ψ(f(c))` for `y^{1/6} ≤ C ≤ y^{1/5}`.
There `f(c) = y^{1/2}c^{−3/2}` has `f' ≍ y^{1/2}C^{−5/2} ∈ [1, y^{1/12}]`. `f'` crosses
integers, so Kusmin–Landau alone (the first-derivative test) does not apply. The cheapest
sufficient tool is:

**ψ-sum lemma.** If `λ ≤ |f''| ≤ Kλ` on `[C, 2C]` with constant sign, then
`Σ_{c∼C} ψ(f(c)) ≪_K Cλ^{1/3} + λ^{−1/2}`.

This follows from truncating `ψ` at `H = λ^{−1/3}` and applying the second-derivative test
`Σ e(hf(n)) ≪ C(hλ)^{1/2} + (hλ)^{−1/2}`. Applied to the two sums:

- b-sum: `λ = y^{1/2}C^{−7/2}` gives `min(C, y^{1/6}C^{−1/6}) + y^{−1/4}C^{7/4} ≪ y^{1/7}`, at
  the crossover `C = y^{1/7}`. The second term is `≤ y^{1/10}`.
- a-sum: `f = y^{1/3}a^{−2/3}`, `λ = y^{1/3}A^{−8/3}`, giving `y^{1/9}A^{1/9} + y^{−1/6}A^{4/3}
  ≤ y^{2/15} + y^{1/10}` for `A ≤ y^{1/5}`.

Summing dyadically gives `θ = 1/7 + ε`. This is Richert's `2/15` up to the choice of split.
**No Weyl differencing, exponent pairs or double sums are needed.** Kusmin–Landau, the
second-derivative test (Kusmin–Landau plus a partition by `‖f'‖`) and a Fourier truncation of
`ψ` are enough. An elementary Voronoi–Sierpiński lattice-point argument would avoid Fourier
analysis, but in Lean it is no shorter (unverified judgement).

### Steps for a Lean agent

1. **Statement file.** Copy `Nat.Full`/`Nat.Powerful`, `Q`, `A` and `B` verbatim, and the three
   fc statements as `Prop`s. Input: formal-conjectures `86a2f58a`. Effort S.
2. **Structure.** `n` is powerful and `n > 0` ⇔ `n = a²b³` with `b` squarefree, uniquely. So
   `Q(x) = #{(a,b) : Squarefree b, a²b³ ≤ x}`. Input: Mathlib `Nat.exists_sq_mul_squarefree`
   (`Mathlib/Data/Nat/Squarefree.lean`), `Nat.primeFactors`, factorization. Must be proved, S–M.
3. **Möbius inversion.** `μ²(b) = Σ_{d²∣b} μ(d)`, then `Q(x) = Σ_{d≤x^{1/6}} μ(d) N(x/d⁶)`.
   Must be proved, S–M (Mathlib has `ArithmeticFunction.moebius` and the `Squarefree` API, but
   not this identity as far as I found).
4. **Zeta constants.** For real `s > 1`, `Σ_{n≤w} n^{−s} = ζ(s) − w^{1−s}/(s−1) + O(w^{−s})`.
   For `0 < s < 1` the same with `ζ(s)` the continued value. Needed at `s = 3/2` and `s = 2/3`.
   - Input: Mathlib `zeta_eq_tsum_one_div_nat_cpow` for `s > 1`, and Abel summation
     (`Mathlib/NumberTheory/LSeries/SumCoeff.lean`).
   - For `s = 2/3` you need `ζ(s) = s/(s−1) − s∫₁^∞ {t} t^{−s−1} dt` on `Re s > 0`.
     riemann-hypothesis has it as `zeta_eq` (`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean:97`,
     with `fractInt` at line 13). Rule 1 forbids importing it into the main library, and there
     is no licence to copy it. Either reprove it (M, by the identity theorem on `Re s > 0`) or
     take it as a tier-H hypothesis discharged in `Unconditional/` (its proof uses no RH).
     Reproving is preferred.
   - Also `Σ μ(d)d^{−s} = 1/ζ(s)` for `s = 2, 3`: Mathlib `LSeries_one_mul_Lseries_moebius`
     (`Mathlib/NumberTheory/LSeries/Dirichlet.lean:322`). Total effort M.
5. **Hyperbola identity for `N(y)`** with the main terms `ζ(3/2)y^{1/2} + ζ(2/3)y^{1/3}` and an
   error written exactly as the two `ψ`-sums plus `O(1)`. Must be proved, M. The trivial bound
   gives `θ = 1/5`; prove that first as a checkpoint.
6. **Exponential-sum module (the cost).** Must be proved, L.
   - (6a) Kusmin–Landau: `f'` monotone with `‖f'‖ ≥ η` gives `|Σ e(f(n))| ≤ cot(πη/2)` or
     `≪ 1/η`. Abel summation with `1/(1 − e(δ_n))`. S–M.
   - (6b) Second-derivative test `≪ N λ^{1/2} + λ^{−1/2}`, by partitioning according to
     `‖f'‖ < λ^{1/2}`. M.
   - (6c) Fourier truncation of `ψ`: `Σψ(f(n)) ≪ N/H + Σ_{h≤H} h^{−1}|Σ e(hf(n))|`. Use either
     Vaaler's polynomial or a trapezoid-smoothed sawtooth with absolutely summable Fourier
     series (coefficients `≪ min(1/h, 1/(h²Δ))`) plus monotonicity of `⌊·⌋`. Mathlib has
     `fourierCoeff` on `AddCircle` and `hasSum_fourier_series_of_summable`. M–L. **This is the
     riskiest step.**
   - (6d) The ψ-sum lemma, then dyadic assembly for the two specific `f`, giving
     `Δ_{2,3}(y) ≪ y^{1/7}`. M. Bounds on `f''` of `y^{1/2}c^{−3/2}` use Mathlib `rpow`
     derivatives, which are tedious but standard.
7. **Mertens input.** `M(y) ≪ y^{1/2+ε}` under RH. It comes from sibling mertens-rh
   `Mertens.mertens_of_RH : RiemannHypothesis → MertensBound` (`Mertens/Littlewood.lean`, with
   `MertensBound` in `Mertens/Statement.lean`). That code is in **PR #1 (branch `finality`,
   OPEN, not merged)**. The PR body claims no `sorry` and standard axioms; I have not checked
   that. Only `M(y) ≪ y^{α}` for one `α < 1` is used (`α = 3/4` is enough), so a weaker
   statement may be stated as an interface `Prop` if the pin isn't ready.
8. **Partial summation for the tails** `Σ_{d>D} μ(d)d^{−s} ≪ D^{α+1−s}` (s = 2, 3) and the
   S₂ swap. Must be proved, M.
9. **Assembly** with `D = x^{(1/2−θ)/(4−α−6θ)}`, then convert to fc's `=O[atTop]` form with
   real `rpow`. M.
   - `α = 1/2+ε` (RH) gives `error_term_improvement`.
   - `α = 1` (trivial `|M| ≤ y`) gives `asymptotic_bateman_grosswald`, tier D.
   - Steps 2–5 with the trivial `θ`-free bound (`|N(y) − ζ(3/2)y^{1/2}| ≪ y^{1/3}`) give
     `asymptotic_erdos_szekeres`, tier D, at cost S on top.

No explicit constants are needed anywhere: all statements are `=O[atTop]`. No finite
computation and no `native_decide` either.

## 5. Target Lean statements

`PowerfulRH/Statement.lean`: definitions verbatim from fc (§1), plus

```lean
def ErrorTermImprovement : Prop :=
  ∃ δ > (0 : ℝ),
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 6 - δ)
```

Headline theorems:

```lean
theorem errorTermImprovement_of_RH (hRH : RiemannHypothesis) : ErrorTermImprovement
-- explicit form (choose whichever exponent the ψ-sum module actually delivers):
theorem error_le_of_RH (hRH : RiemannHypothesis) :
    ∀ ε > (0 : ℝ), (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1:ℝ)/2) - B * x ^ ((1:ℝ)/3)) =O[atTop]
      fun x => x ^ ((6 : ℝ) / 37 + ε)
-- tier D by-products (label "known"):
theorem asymptotic_bateman_grosswald : ...   -- fc statement verbatim
theorem asymptotic_erdos_szekeres : ...      -- fc statement verbatim
```

- Weaker fallback, tier C on a weaker hypothesis:
  `errorTermImprovement_of_mertens (h : ∃ α < 1, (fun y => (mertens y : ℝ)) =O[atTop] (· ^ α))`.
  It decouples the work from mertens-rh, and the RH version is then a one-liner.
- Fallback if step 6 stalls: `errorTermImprovement_of_lattice (hθ : ∃ θ < 1/6, Δ₂₃ =O[atTop] (· ^ θ))
  (hRH : RiemannHypothesis)`. That leaves the lattice bound as a tier-H hypothesis (Richert
  1952), which is **not done** by rule 6.
- `Unconditional/`: `error_term_improvement := errorTermImprovement_of_RH riemannHypothesis`.

## 6. Effort and risk

**Overall L.**

| Part | Effort |
|---|---|
| Steps 1–5 and 7–9 | M in total: elementary but `rpow`/`floor`-heavy, about 1.5–2.5k lines (unverified estimate) |
| Step 6, the exponential-sum module | L: about 1.5–3k lines (unverified estimate) |

Nothing in the workspace, Mathlib `fc4f59e5` or riemann-hypothesis provides step 6.
`docs/rh-lemmas/05-weil-etale-resolution.md:212` says "no Weil bound for curves, exponential
sums or Kloosterman sums anywhere". Mathlib PR #39406 (van der Corput for oscillatory
*integrals*, open) does not cover sums.

- **Riskiest step:** 6c, the Fourier truncation of `ψ` with uniform error control, followed by
  6b. Fallback: the elementary Farey-arc lattice-point argument (also L).
- **Secondary risk:** step 4's `ζ(2/3)` identification on `0 < s < 1`. The riemann-hypothesis
  repo shows it is doable, but the main library can't use it.
- **Dependency risk:** mertens-rh PR #1 unmerged. Mitigated by the `α < 1` interface.

**Recommendation: conditional GO, only as a labelled RH-consequence formalisation.** It
yields Lean proofs of all three statements in an fc file: one `research open` statement (tier U,
RH-consequence) and two `research solved` ones (tier D, known, one of them on fc's FC100 solved
list). It also gives the workspace a reusable second-derivative test. **NO-GO if the goal is a
genuinely new result**: the conditional theorem dates from 1973 and has been improved at
least seven times.

## 7. Open questions for the user

1. Is an RH-consequence whose RH proof dates from 1973 acceptable as a target? The fc entry is
   `research open`, but its own docstring says "Improvements are known under the Riemann
   Hypothesis".
2. Is the L-sized exponential-sum module worth building for this alone, given it would be
   reused (Dirichlet/circle-type lattice problems, Lindelöf-type convexity breaking)?
3. Target the weak `6/37` (or any `δ > 0`), or aim for SS's exact `13/81` (needs `θ = 2/15`,
   the same tools with more careful dyadic bookkeeping)? I recommend weak.
4. Wait for mertens-rh PR #1 to merge, or state the `α < 1` Mertens interface and proceed in
   parallel?
5. The `ζ(2/3)` integral identity: reprove it (preferred) or carry it as an H hypothesis
   discharged from riemann-hypothesis in `Unconditional/`?
