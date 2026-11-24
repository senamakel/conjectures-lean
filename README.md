# The least quadratic non-residue under GRH (Lamzouri–Li–Soundararajan) in Lean

Lamzouri, Li and Soundararajan (*Conditional bounds for the least quadratic non-residue and
related problems*, Math. Comp. 84 (2015) 2391–2412,
[arXiv:1309.3595](https://arxiv.org/abs/1309.3595)) proved under GRH that the least quadratic
non-residue mod a prime `q ≥ 5` is below `(log q)²` (their Corollary 1.2), and that the least
prime `ℓ ∤ q` outside a proper subgroup of `(ℤ/q)ˣ` is at most `(log q + B(q))²` (Theorem 1.1).
Unconditionally the best bounds are of Burgess type, `q^{1/(4√e)+ε}`.

This repository proves in Lean, following LLS:

- LLS Corollary 1.2 exactly as stated: for every prime `q ≥ 5` there is a quadratic non-residue
  `≤ (log q)²`.
- Bach's subgroup bound with Bach's own constant `2` (Bach, *Explicit bounds for primality
  testing and related problems*, Math. Comp. 55 (1990) 355–380): every proper subgroup of
  `(ℤ/q)ˣ` omits a unit `≤ 2 log² q`, for every modulus `q`. Consequences: the least quadratic
  non-residue mod an odd prime `p` is `≤ 2 log² p`, and Miller's deterministic primality test
  with witnesses `a ≤ 2 log² n` is correct. The earlier form with constant `11/4` remains.
- Bounds of the shape of LLS Theorem 1.5 for `L(1, χ)`, `χ` primitive mod `q ≥ 10¹⁰`:
  `|L(1,χ)| ≤ 2e^γ(log log q + 5)` (LLS: `2e^γ(log log q − log 2 + 1/2 + 1/log log q)`) and
  `1/|L(1,χ)| ≤ 2e^γ(log log q + 5)` (LLS: `(12e^γ/π²)(log log q − log 2 + 1/2 + …)`).
- With Dirichlet's class number formula, bounds of the shape of LLS Corollary 1.3 for the class
  number `h(−q)` of every imaginary quadratic field, of discriminant `−q` with `q ≥ 10¹⁰`, odd
  or even:
  `h(−q) ≤ (2e^γ/π)√q(log log q + 5)` and `h(−q) ≥ √q/(2πe^γ(log log q + 5))` (LLS:
  `(2e^γ/π)√q(log log q − log 2 + 1/2 + 1/log log q)` and
  `(π/(12e^γ))√q/(log log q − log 2 + …)`).

The main library is a complete Lean proof that GRH implies each of these. `Unconditional/`
proves all of them unconditionally in Lean, with GRH supplied by the certified proof of
L. Alpöge in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
Literature status: RH-consequence. Our constants differ from the paper's where noted above;
"Deviations from the literature" gives both numbers. Bounds `h(−q) ≪ √q log log q` and
`h(−q) ≫ √q/log log q` under GRH go back to Littlewood (*On the class-number of the corpus
P(√−k)*, Proc. London Math. Soc. (2) 27 (1928) 358–372), in asymptotic form. Unconditionally the
upper bound `h(−q) ≪ √q log q` is elementary, and the best lower bounds are Siegel's ineffective
`h(−q) ≫_ε q^{1/2−ε}` and an effective bound of order `log q` (Goldfeld, Gross–Zagier, Oesterlé).

```lean
theorem LLS.leastNonresidueBelowLogSq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBelowLogSq
theorem LLS.bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound (11 / 4)
theorem LLS.leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound (11 / 4)
theorem LLS.miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement (11 / 4)
theorem LLS.bach2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound 2
theorem LLS.leastNonresidue2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound 2
theorem LLS.miller2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement 2
theorem LLS.l1UpperBoundWith_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : L1UpperBoundWith 5
theorem LLS.l1LowerBoundWith_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : L1LowerBoundWith 5
theorem LLS.classNumberUpperBoundOddWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberUpperBoundOddWith 5
theorem LLS.classNumberLowerBoundOddWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberLowerBoundOddWith 5
theorem LLS.classNumberUpperBoundWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberUpperBoundWith 5
theorem LLS.classNumberLowerBoundWith_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : ClassNumberFormula) :
    ClassNumberLowerBoundWith 5
theorem LLS.discr_isFundamentalDiscr (K : Type*) [Field K] [NumberField K]
    (h2 : finrank ℚ K = 2) : Int.IsFundamentalDiscr (discr K)
```

where (`LLS/Statement.lean`, transcribed from the paper)

```lean
def LLS.LeastNonresidueBelowLogSq : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q →
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ log q ^ 2 ∧ ¬ IsSquare (n : ZMod q)
```

and `Ankeny.BachSubgroupBound c`, `Ankeny.LeastNonresidueBound c`, `Miller.MillerStatement c`
are the target definitions of ankeny-grh and miller-grh, used unchanged. The weaker forms of
LLS Theorem 1.5 are stated in `LLS/L1/Weak.lean` (`LLS/Statement.lean`'s `L1UpperBound`,
`L1LowerBound` are unchanged and not proved):

```lean
def LLS.L1UpperBoundWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * exp eulerMascheroniConstant * (log (log q) + C)
def LLS.L1LowerBoundWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    1 / ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * exp eulerMascheroniConstant * (log (log q) + C)
```

The class-number statements (`LLS/ClassNumber.lean`; the paper's own Corollary 1.3,
`ClassNumberUpperBound`, `ClassNumberLowerBound`, and the hypothesis `ClassNumberFormula` are in
`LLS/Statement2.lean`; "`h(−q)` for a fundamental discriminant `−q`" is stated as
`NumberField.classNumber K` for every number field `K` of degree 2 with `discr K = −q`):

```lean
def LLS.ClassNumberUpperBoundOddWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, q % 4 = 3 →
    Squarefree q → discr K = -q → (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ) ≤ 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + C)
def LLS.ClassNumberLowerBoundOddWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, q % 4 = 3 →
    Squarefree q → discr K = -q → (10 : ℝ) ^ 10 ≤ q →
      √q / (2 * π * exp eulerMascheroniConstant * (log (log q) + C)) ≤ classNumber K
def LLS.ClassNumberFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (q : ℕ) [NeZero q], finrank ℚ K = 2 →
    discr K = -q → 4 < q → ∀ χ : DirichletCharacter ℂ q,
      (∀ n : ℕ, Odd n → χ n = ((jacobiSym (-(q : ℤ)) n : ℤ) : ℂ)) →
        χ.LFunction 1 = (π * classNumber K / √q : ℝ)
```

and, for every imaginary quadratic field with no condition on `q` beyond `q ≥ 10¹⁰`
(`LLS/Statement3.lean`):

```lean
def LLS.ClassNumberUpperBoundWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ) ≤ 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + C)
def LLS.ClassNumberLowerBoundWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      √q / (2 * π * exp eulerMascheroniConstant * (log (log q) + C)) ≤ classNumber K
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `leastNonresidueBelowLogSq_of_GRH` | C (U in `Unconditional/`) | GRH |
| `bach_of_GRH`, `leastNonresidue_of_GRH`, `miller_of_GRH` | C (U in `Unconditional/`) | GRH |
| `bach2_of_GRH`, `leastNonresidue2_of_GRH`, `miller2_of_GRH` | C (U in `Unconditional/`) | GRH |
| `l1UpperBoundWith_of_GRH`, `l1LowerBoundWith_of_GRH` | C (U in `Unconditional/`) | GRH |
| `classNumberUpperBoundOddWith_of_GRH_of_formula`, `classNumberLowerBoundOddWith_of_GRH_of_formula` | C + H (U + U₀ in `Unconditional/`) | GRH, `ClassNumberFormula` |
| `classNumberUpperBoundWith_of_GRH_of_formula`, `classNumberLowerBoundWith_of_GRH_of_formula` | C + H (U + U₀ in `Unconditional/`) | GRH, `ClassNumberFormula` |
| `discr_isFundamentalDiscr`, `jacobiChar_isPrimitive`, `kroneckerChar_isPrimitive` | D | none |

GRH is `Erdos985.DirichletLNonvanishingRightOfHalf`, copied word for word in erdos-985 from
`src/Statements.lean` of [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
`ClassNumberFormula` (tier H) is Dirichlet's class number formula for imaginary quadratic
fields, `L(1, χ_{−q}) = π h(−q)/√q` for `q > 4`, in LLS's normalisation (their equation (1.3)),
with the Kronecker symbol characterised by `χ(n) = J(−q | n)` at odd `n`. It is a theorem
(Dirichlet 1839), not a conjecture; Mathlib does not have it at this pin. It is written with
Mathlib objects only, and is the conclusion of riemann-hypothesis's
`GlobalTheory.LFunction_one_and_mean_log_eta` with that repository's `IsKroneckerChar` unfolded.
No other hypothesis appears. `LLS/Statement.lean` also fixes, as targets not proved here,
Theorem 1.1 (`LeastPrimeOutsideSubgroup`, with LLS's `A(q)`, `B(q)`), Theorem 1.1 (2),
Theorem 1.4 (`LeastPrimeInCoset`) and Theorem 1.5 with the paper's constants (`L1UpperBound`,
`L1LowerBound`).

## Axioms

Real output of `lake env lean Axioms.lean` (2026-11-24, after a clean `lake build`):

```
'LLS.leastNonresidueBelowLogSq_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.bach_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LLS.chunk114_ok_0._native.native_decide.ax_1_1,
 LLS.chunk114_ok_1._native.native_decide.ax_1_1,
 LLS.chunk114_ok_10._native.native_decide.ax_1_1,
 LLS.chunk114_ok_11._native.native_decide.ax_1_1,
 LLS.chunk114_ok_12._native.native_decide.ax_1_1,
 LLS.chunk114_ok_13._native.native_decide.ax_1_1,
 LLS.chunk114_ok_14._native.native_decide.ax_1_1,
 LLS.chunk114_ok_15._native.native_decide.ax_1_1,
 LLS.chunk114_ok_2._native.native_decide.ax_1_1,
 LLS.chunk114_ok_3._native.native_decide.ax_1_1,
 LLS.chunk114_ok_4._native.native_decide.ax_1_1,
 LLS.chunk114_ok_5._native.native_decide.ax_1_1,
 LLS.chunk114_ok_6._native.native_decide.ax_1_1,
 LLS.chunk114_ok_7._native.native_decide.ax_1_1,
 LLS.chunk114_ok_8._native.native_decide.ax_1_1,
 LLS.chunk114_ok_9._native.native_decide.ax_1_1]
'LLS.leastNonresidue_of_GRH' depends on axioms: (the same nineteen as bach_of_GRH)
'LLS.miller_of_GRH' depends on axioms: (the same nineteen as bach_of_GRH)
'LLS.bach_large114' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.re_logSum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.re_cesShift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.Z2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.l1UpperBoundWith_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.l1LowerBoundWith_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.log_norm_L1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.classNumberUpperBoundOddWith_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.classNumberLowerBoundOddWith_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.jacobiChar_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Round 6 (2026-11-24, `lake build LLS.ClassNumberAll`, then `#print axioms`):

```
'LLS.classNumberUpperBoundWith_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.classNumberLowerBoundWith_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.discr_isFundamentalDiscr' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.kroneckerChar_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Round 7 (2026-11-24, `lake build`, then `lake env lean Axioms.lean`):

```
'LLS.bach2_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LLS.chunk2_ok_0._native.native_decide.ax_1_1,
 LLS.chunk2_ok_1._native.native_decide.ax_1_1,
 LLS.chunk2_ok_10._native.native_decide.ax_1_1,
 LLS.chunk2_ok_11._native.native_decide.ax_1_1,
 LLS.chunk2_ok_12._native.native_decide.ax_1_1,
 LLS.chunk2_ok_13._native.native_decide.ax_1_1,
 LLS.chunk2_ok_14._native.native_decide.ax_1_1,
 LLS.chunk2_ok_2._native.native_decide.ax_1_1,
 LLS.chunk2_ok_3._native.native_decide.ax_1_1,
 LLS.chunk2_ok_4._native.native_decide.ax_1_1,
 LLS.chunk2_ok_5._native.native_decide.ax_1_1,
 LLS.chunk2_ok_6._native.native_decide.ax_1_1,
 LLS.chunk2_ok_7._native.native_decide.ax_1_1,
 LLS.chunk2_ok_8._native.native_decide.ax_1_1,
 LLS.chunk2_ok_9._native.native_decide.ax_1_1]
'LLS.leastNonresidue2_of_GRH' depends on axioms: (the same eighteen as bach2_of_GRH)
'LLS.miller2_of_GRH' depends on axioms: (the same eighteen as bach2_of_GRH)
'LLS.Check.checkChunk_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.goodQ_tail2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The fifteen `native_decide` axioms of the constant-`2` bound evaluate `LLS.Check.checkChunk`
(`LLSCheck.lean`, core Lean only, precompiled) on fifteen ranges covering `3 ≤ q < 2^2500`;
its soundness `LLS.Check.checkChunk_sound` uses the standard three axioms only. The chunks took
between 2 s (`C2_14`, `2^100 ≤ q < 2^2500`) and 334 s (`C2_10`, `2^24 ≤ q < 2^25`); `time lake
build` reported 1342 s of user time for all fifteen (6 min wall on a loaded 95-core box). Most of
it is the generation search for the moduli the per-modulus budget misses.

Corollary 1.2 uses the standard three axioms only: its finite range `5 ≤ q < 2^12` is a list
of Euler-criterion certificates checked by `decide +kernel`. The sixteen `native_decide` axioms
of the subgroup bound evaluate ankeny-grh's generation checker (`Ankeny.Checker.checkRange 11 4`,
soundness `Ankeny.bach_of_checkRange`, proved in ankeny-grh) on `4 ≤ q < 2^18`: for each `q` a
graph search shows that the units below `⌊(11/4) (⌊log₂ q⌋ log 2)²⌋` generate `(ZMod q)ˣ`. The
sixteen chunks of `2^14` moduli took between 30 s (`C114_0`) and 1884 s (`C114_15`), growing
roughly linearly with `q`; `time lake build` reported 8235 s of user time (31 min wall on 95
cores).

## Proof outline

The full blueprint, with every step as a Lean statement, is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

1. Explicit formulas (`LLS/Analytic/`), for `χ` primitive mod `N`, under GRH, with
   `Z2 = Σ_ρ m_ρ/|ρ|²`:
   * LLS Lemma 2.2, log weight (`re_logSum_le`): `Re Σ_{n≤x} Λ(n)χ(n) log(x/n) ≤ (√x+1) Z2 +
     (log N + Re D(1,χ⁻¹)) log x − ½ log π · log x + π²/6 − (γ/2) log x`. New Perron kernel
     `x^s/s²` (`Log/Perron.lean`), exact identity `S = −Σ_ρ m_ρ(x^ρ−1)/ρ² − D(0) log x + Γ̃(x)`.
   * LLS Lemma 2.3 (`re_cesShift_le`): the Cesàro formula of erdos-985 applied to
     `χ(n)Λ(n)/n`, which isolates `D(1, χ)` with a zero sum of size `Z2/√x`.
   * `Z2_eq`: `Z2 = log N + Re D(1,χ) + Re D(1,χ⁻¹)` (Hadamard at `0` and `1`).
   * `psiLog_ge`: `Σ_{n≤x} Λ(n) log(x/n) ≥ x − (3/20)√x − 3 log x − 3`, by summation by
     parts from erdos-985's principal bound; `vonMangoldt_ces_ge`:
     `Σ_{n<x} Λ(n)/n (1 − n/x) ≥ log x − 2`, unconditional.
2. Key inequality (`LLS/Key.lean`, LLS §3): if `χ ≠ 1` mod `q` is `1` on all `n ≤ x` prime
   to `q`, symmetrising over the inducing `ψ` and `ψ⁻¹` bounds `Z2` from Lemma 2.3 (the sum
   `Σ_{n<x} Λ(n)/n (1−n/x) ≈ log x` is now large, which is LLS's `A(q)` gain) and contradicts
   Lemma 2.2 against the principal sum `≈ x`. Prime powers `p^k ≤ x` with `p ∣ q` are the
   losses (`LLS/Losses.lean`); primes dividing `q` but not the conductor are charged to
   `log f ≤ log q − Σ log p`.
3. Budget (`Numerics/Budget.lean`): the key inequality forces `Φ(x, log q) ≤ 0` for an
   explicit `Φ`; primes `p ≥ 17` dividing `q` cost at most `β log p` each,
   `β = (log x)²/(2 log 17) + K/8`, and `p < 17` are listed. For prime `q > x` the losses
   vanish and the budget is `Φ₁` (`Numerics/Prime.lean`).
4. Numerics: `Φ(⌊(11/4) log² Q_a⌋, log Q_b) > 0` on 28 certified intervals covering
   `2^18 ≤ q < 2^700` (`Numerics/Intervals114.lean`, generated by `scripts/emitfile.py`), and
   for `q ≥ 2^700` by a polynomial argument in `x^{1/8}` (`Numerics/Tail114.lean`, reusing
   `Numerics/Tail.lean`). For primes:
   `Φ₁ > 0` with `x = ⌊log² q⌋` on 153 intervals covering `2^12 ≤ q < 2^700`
   (`Numerics/IntervalsP.lean`, `scripts/emit1.py`) and `q ≥ 2^700` (`Numerics/TailP.lean`).
5. Finite ranges: primes `5 ≤ q < 2^12` by Euler-criterion certificates
   (`LLS/NonresidueCert.lean`, `scripts/emit_small.py`); `q < 2^18` for the subgroup bound by
   ankeny-grh's checker (`LLS/Finite114.lean`, `LLS/Compute/C114_*.lean`).
6. `L(1, χ)` (`LLS/L1/`), for `χ` primitive mod `q ≥ 10¹⁰`:
   * `Shift.lean`: for real `σ > 1`, the log-kernel formula with coefficients `χ(n)Λ(n)n^{−σ}`
     gives `|S_σ + (L'/L)(σ) log x + (L'/L)'(σ)| ≤ x^{1/2−σ} Z + 2x^{−σ}` (zeros at `ρ − σ`,
     gamma poles at `−(σ + m_k)`, `(L'/L)'` by termwise differentiation of the Hadamard series);
   * `Integrate.lean` (LLS Lemma 2.5): `|log |L(1,χ)| − Re Σ_{n≤x} χΛ(n)/(n log n) · log(x/n)/log x
     + Re (L'/L)(1)/log x| ≤ (Z/√x + 2/x)/log² x`, by monotonicity of
     `Re A(σ) + log x · log |L(σ)| + Re (L'/L)(σ) ± ∫ bound` on `[1, ∞)` and the limits at `∞`;
   * `CesLower.lean`: Lemma 2.3 in the other direction, and `Λ'/Λ(1) = G(1) + L'/L(1)`;
   * `Principal.lean`: `Σ Λ(n)/(n log n) · log(x/n)/log x ≤ log log x + γ − 1 + 3/log x` for
     `x ≥ 10⁵` (Mertens under RH via robin-rh), and `Σ_{n<x} Λ(n)/n (1 − n/x) ≤ log x − 1 + 1/x`;
   * `Assembly.lean`, `Weak.lean`: `log |L(1,χ)|^{±1} ≤ log log x + γ + c/log x`, with `c`
     explicit in `x` and the zero sum `Z ≤ (log q + 2 log x)/(1 − 2/√x)`;
   * `Final.lean`: `x = 10⁵` if `log² q < 10⁵`, else `x = ⌊log² q⌋`; then `c ≤ 4.11` and
     `e^γ (l + c + c²/l) ≤ 2e^γ (log log q + 5)`.
7. Class numbers (`LLS/ClassNumber.lean`), for `q ≡ 3 (mod 4)` squarefree: the Jacobi
   symbol `n ↦ J(n | q)` is a Dirichlet character mod `q` (`jacobiChar`), equal to the Kronecker
   symbol `J(−q | n)` at odd `n` by quadratic reciprocity (`jacobiChar_kronecker`), and
   primitive (`jacobiChar_isPrimitive`: if it factored through `q/p`, `p ∣ q` prime, the CRT
   lift `n ≡ 1 (mod q/p)` of a non-residue mod `p` would have `J(n | q) = −1` and `χ(n) = 1`).
   Then `‖L(1,χ)‖ = π h/√q` from `ClassNumberFormula`, and step 6 gives both bounds.
8. Every imaginary quadratic field (`LLS/ClassNumberAll.lean`):
   * `discr_isFundamentalDiscr` (`LLS/FundamentalDiscr.lean`): `discr K` is a fundamental
     discriminant. `K ≅ ℚ(√d)`, `d` squarefree (Mathlib's quadratic algebras); with `D = d` or
     `4d`, `QuadraticAlgebra ℤ (D/4) (D%4)` is the integral closure of `ℤ`
     (`QuadraticAlgebra.Int.algEquivIntegralClosure`), hence `≅ 𝓞 K`, and its basis `{1, ω}` has
     discriminant `D`. So `q ≡ 3 (mod 4)` is squarefree (step 7), or `q = 4m` with `m`
     squarefree, `m ≡ 1, 2 (mod 4)`.
   * `kroneckerChar` (`LLS/Kronecker.lean`): for `4 ∣ q`, `n ↦ J(−q | n)` is periodic mod `q`
     (`J(−4m | n) = J(−m | n)` and `jacobiSym.mod_right`), so a character mod `q`, and it is
     primitive when `−q` is fundamental (`kroneckerChar_isPrimitive`): for each prime `p ∣ q`
     some `n ≡ 1 (mod q/p)` has `J(−q | n) = −1`, namely `n = 1 + 2m` for `p = 2`
     (`χ₄(n) = −1` or `χ₈'(n) = −1`) and a CRT lift of a non-residue mod `p` for odd `p`.
   * The class number formula and step 6 give both bounds, exactly as in step 7.

9. Bach's constant `2` (`LLS/Bach2/`, `LLSCheck.lean`):
   * `keyP` is the key inequality of step 2 with any lower bound `Pc` for the Cesàro sum;
     `budgetQ_nonpos` charges each prime `p ≤ x` dividing `q` its cost `W_p(x)`,
     `budgetU_nonpos` lists the primes `p < 53` and charges the others `β log p`,
     `β = (log x)²/(2 log 53) + 2K/52`.
   * `LLSCheck.checkChunk m w lo hi` (core Lean, exact `Rat` arithmetic) splits `[lo, hi)` into
     blocks `[a, a + a/2^w)`, takes `x = ⌊2 La²⌋` with `La ≤ log a` (from `2^k ≤ a^m`), bounds
     `√x`, `log x`, `log p` and `log b`, computes `Pc` as the exact Cesàro sum with certified
     lower bounds for `Λ(n)` (for `x < 2000`; else `log x − 2`), and accepts the block if the
     uniform budget is positive; otherwise it tries each `q` with its own primes (integer form
     scaled by `2^32`), and failing that runs `Ankeny.Checker.checkGen q x`.
   * `checkChunk_sound` proves that a `true` result gives, for every `q` in the range, either
     generation of `(ZMod q)ˣ` by the units `≤ x ≤ 2 log² q` or a positive budget;
     `bach_of_good2` turns either into the bound under GRH.
   * 15 chunks cover `3 ≤ q < 2^2500` (`LLS/Compute2/`); `goodQ_tail2` covers `q ≥ 2^2500`
     with the uniform budget `Φ` of step 3 (`x = ⌊2L²⌋`, `z = x^{1/8} ≥ 7`).

## Layout

| File | Content |
|---|---|
| `LLS/Statement.lean` | Target statements (LLS Thm 1.1, 1.4, 1.5, Cor 1.2) |
| `LLS/Defs.lean` | `D`, `Z2`, `logSum`, `cesShift`, gamma-term bounds |
| `LLS/Analytic/Log/*.lean`, `LogFormula.lean` | Lemma 2.2 (log-weighted explicit formula) |
| `LLS/Analytic/Shift/*.lean`, `ShiftFormula.lean` | Lemma 2.3 (shifted Cesàro formula) |
| `LLS/Analytic/ZeroSum.lean` | `Z2 = log N + Re D(1,χ) + Re D(1,χ⁻¹)` |
| `LLS/Analytic/Principal.lean`, `Mertens.lean` | Principal sums |
| `LLS/Losses.lean`, `LLS/Key.lean` | Losses and the key inequality |
| `LLS/Numerics/Budget.lean`, `Interval.lean`, `Good.lean` | Budget `Φ`, interval evaluation |
| `LLS/Numerics/Intervals114.lean`, `Tail114.lean`, `Tail.lean` | `c = 11/4`, `q ≥ 2^18` |
| `LLS/Numerics/Prime.lean`, `IntervalsP.lean`, `TailP.lean` | Prime moduli, `c = 1`, `q ≥ 2^12` |
| `LLS/NonresidueCert.lean`, `LLS/Nonresidue.lean` | Corollary 1.2 |
| `LLS/Compute/C114_*.lean`, `LLS/Finite114.lean`, `LLS/BachCore.lean`, `LLS/Bach114.lean`, `LLS/Main.lean` | Subgroup bound with `c = 11/4` |
| `LLS/L1/Shift.lean`, `ShiftAux/*.lean` | The shifted log-kernel formula |
| `LLS/L1/Integrate.lean` | LLS Lemma 2.5 |
| `LLS/L1/CesLower.lean`, `Principal.lean`, `PrinAux/*.lean` | Lemma 2.3 (lower), principal sums |
| `LLS/L1/Assembly.lean`, `Weak.lean`, `Final.lean` | `L(1, χ)` bounds |
| `LLS/Statement2.lean` | Target statements: LLS Cor 1.3, `ClassNumberFormula` |
| `LLS/ClassNumber.lean` | Jacobi character, its primitivity, class-number bounds (odd `q`) |
| `LLS/Statement3.lean` | Target statements: class-number bounds for every imaginary quadratic field |
| `LLS/FundamentalDiscr.lean` | `discr K` of a quadratic field is a fundamental discriminant |
| `LLS/Kronecker.lean` | Kronecker character `χ_{−q}` for `4 ∣ q`, its primitivity |
| `LLS/ClassNumberAll.lean` | Class-number bounds for every imaginary quadratic field |
| `LLS/Bach2/KeyP.lean`, `Budget.lean` | Key inequality with any Cesàro lower bound; per-modulus and uniform budgets |
| `LLSCheck.lean` | Executable checker for constant `2` (core Lean, rational arithmetic, precompiled) |
| `LLS/Bach2/SoundBasic.lean`, `SoundBounds.lean`, `Sound.lean` | Its soundness proof (`checkChunk_sound`) |
| `LLS/Compute2/C2_*.lean`, `LLS/Bach2/Finite2.lean` | The 15 checked chunks, `3 ≤ q < 2^2500` |
| `LLS/Bach2/Tail2.lean`, `Core.lean`, `Main2.lean` | `q ≥ 2^2500`; assembly of `bach2_of_GRH` |
| `scripts/*.py` | Generators for the certificates and the sizing computations |

## Deviations from the literature

* Subgroup bound: Bach's constant `2` is proved (`bach2_of_GRH`). The analytic inequality
  alone does not reach `2` uniformly in `q` below about `2^27`: with the constants formalised
  here, moduli divisible by many small primes are the worst case, and the budget uniform in `q`
  (primes `p < 53` listed, `β log p` for the rest) is positive only from `q ≈ 2^27`
  (`2^38.6` with the old cut-off at `17` and the unconditional Cesàro bound `log x − 2`). Three
  changes close the gap:
  * the Cesàro sum `Σ_{n ≤ x} Λ(n)/n (1 − n/x)` is summed exactly (with certified lower bounds for
    `log p`) for every `x < 2000` instead of being bounded by `log x − 2`; its true value is
    about `log x − 1 − γ`, and the gain `0.42 · 2K ≈ 0.85 √x` is the largest single term;
  * below `2^27` the budget is evaluated for each modulus with its own prime factors
    (`costQ`, the cost `W_p` of each prime `p ≤ x` dividing `q`), and that is positive for all
    but about 7,500 moduli `q < 2^26` (their sum is about `4.4·10^9`);
  * those moduli are checked by ankeny-grh's generation search with `x = ⌊2 La²⌋`.
  The analytic part is LLS's argument with weaker constants than the paper's: the principal sum
  is bounded by summation by parts (`x − 0.15√x − 3 log x − 3` instead of LLS Lemma 2.1's
  `x − 0.046√x − 1.84 log x − 1`), and the cost of a prime factor `p ≥ 53` of `q` crudely
  (`β log p`). The paper's own Theorem 1.1 bound `(log q + B(q))²` is not proved.
* Theorem 1.1 as stated is not proved. Our constants are weaker than LLS's, so we do not
  get `ℓ ≤ (log q + B(q))²`. Also, as written, the proof of LLS Theorem 1.1 appears to bound
  `Σ Λ(n) χ̃(n)/n (1 − n/X)` as if `χ̃(p) = 1` for primes `p ∣ q`, `p ∤ q̃`; for such `p`
  `χ̃(p)` is unknown. Our `LLS.key` charges these primes twice and absorbs them through
  `log f ≤ log q − Σ log p`.
* Theorem 1.5 is proved with weaker constants. We prove LLS Lemma 2.5 (`LLS.log_norm_L1_le`, standard
  axioms only) and combine it with Lemma 2.3 in both directions, but the remaining inputs are
  cruder than the paper's:
  * the principal sum `Σ Λ(n)/(n log n) · log(x/n)/log x ≤ log log x + γ − 1 + 3/log x`
    (`LLS.l1Sum1_le`, from robin-rh's Mertens theorem under RH, for `x ≥ 10⁵`; LLS Lemma 2.6
    gives `+ γ/log x`);
  * `Σ_{n<x} Λ(n)/n (1 − n/x) ≤ log x − 1 + 1/x` unconditionally (LLS Lemma 2.4 under RH:
    `log x − 1 − γ + …`);
  * for the lower bound we use `|χ(n)| ≤ 1` instead of LLS Lemma 5.1 (the extremality of
    `χ(p) = −1`, which needs a trigonometric computation at `p = 2`), so the leading constant
    is `2e^γ` instead of `12e^γ/π² ≈ 1.216 e^γ`;
  * `x ≥ 10⁵` (LLS: `x = (log q)²/4`), so for `log² q < 10⁵` we take `x = 10⁵`, which costs most
    of the additive constant.

  The result is `|L(1,χ)|^{±1} ≤ e^γ (l + c + c²/l)` with `l = log x` and `c ≤ 4.11`, which gives
  `2e^γ(log log q + 5)` for every `q ≥ 10¹⁰`. LLS's own constants are within `0.004` of failing at
  `q = 10¹⁰` (`e^γ(log x + 1 + 3.1/log x)` against `2e^γ(log log q − log 2 + 1/2 + 1/log log q)`),
  so they need all of Lemmas 2.4, 2.6 and 5.1 at full precision.
* Corollary 1.3 (class numbers) is proved with weaker constants, for every imaginary quadratic
  field. The paper's statement (`ClassNumberUpperBound`, `ClassNumberLowerBound`) is not proved:
  it is Theorem 1.5 with the paper's constants (not proved, above) plus the class number formula.
  We prove `ClassNumberUpperBoundWith 5` and `ClassNumberLowerBoundWith 5` for every imaginary
  quadratic field of discriminant `−q`, `q ≥ 10¹⁰`, with our Theorem 1.5 constants: additive
  `5` (LLS: `−log 2 + 1/2 + 1/log log q`, and `+ 14 log log q/log q` in the lower bound) and
  lower leading constant `1/(2πe^γ)` (LLS: `π/(12e^γ)`). The hypotheses are the paper's (`−q` a
  fundamental discriminant, stated as `discr K = −q`). The round-5 forms
  `ClassNumberUpperBoundOddWith 5`, `ClassNumberLowerBoundOddWith 5` (odd `q`, with explicit
  `q % 4 = 3`, `Squarefree q`) remain.
* Theorem 1.4 (cosets) is not proved.
* Corollary 1.2 is proved exactly as stated (`LeastNonresidueBelowLogSq`).

## Building

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`; also requires ankeny-grh
`129ad57`, miller-grh `b484d44` and robin-rh `dfa8d63`). On a 95-core box with warm caches: the sixteen
`native_decide` chunks for `11/4` take about 2.3 CPU-hours (the slowest, `C114_15`, 1884 s),
the fifteen for `2` (`lake build LLS.Bach2.Main2`) about 22 CPU-minutes (the slowest, `C2_10`,
334 s); the certified
intervals take 141 s (`Intervals114`) and 77 s (`IntervalsP`); everything else is under a minute
per module.

## Unconditional version

`Unconditional/LLSUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the GRH hypothesis in one line. These are the statements above
with no hypothesis left.

| Theorem | Statement | Axioms |
|---|---|---|
| `leastNonresidueBelowLogSq_unconditional` | `LLS.LeastNonresidueBelowLogSq` | standard three |
| `bach_unconditional` | `Ankeny.BachSubgroupBound (11 / 4)` | standard three + 16 `native_decide` |
| `leastNonresidue_unconditional` | `Ankeny.LeastNonresidueBound (11 / 4)` | standard three + 16 `native_decide` |
| `miller_unconditional` | `Miller.MillerStatement (11 / 4)` | standard three + 16 `native_decide` |
| `bach2_unconditional` | `Ankeny.BachSubgroupBound 2` | standard three + 15 `native_decide` |
| `leastNonresidue2_unconditional` | `Ankeny.LeastNonresidueBound 2` | standard three + 15 `native_decide` |
| `miller2_unconditional` | `Miller.MillerStatement 2` | standard three + 15 `native_decide` |
| `l1UpperBoundWith_unconditional` | `LLS.L1UpperBoundWith 5` | standard three |
| `l1LowerBoundWith_unconditional` | `LLS.L1LowerBoundWith 5` | standard three |
| `classNumberFormula` (U₀) | `LLS.ClassNumberFormula` | standard three |
| `classNumberUpperBoundOddWith_unconditional` | `LLS.ClassNumberUpperBoundOddWith 5` | standard three |
| `classNumberLowerBoundOddWith_unconditional` | `LLS.ClassNumberLowerBoundOddWith 5` | standard three |
| `classNumberUpperBoundWith_unconditional` | `LLS.ClassNumberUpperBoundWith 5` | standard three |
| `classNumberLowerBoundWith_unconditional` | `LLS.ClassNumberLowerBoundWith 5` | standard three |

`classNumberFormula` is tier U₀: it uses no RH or GRH theorem, only riemann-hypothesis's class
number formula `GlobalTheory.LFunction_one_and_mean_log_eta`
(`Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean`),
which holds for every number field `K` of degree 2 with `discr K = −q`, `q > 4`, odd or even,
and every `χ` mod `q` with `IsKroneckerChar χ` (by definition `∀ n, Odd n → χ n = J(−q | n)`);
so the same `ClassNumberFormula` serves even discriminants, with `χ = kroneckerChar q`. The bridge is
four lines rather than one: that theorem also takes an embedding `σ : K →+* ℂ` (from Mathlib's
`Nonempty (K →+* ℂ)`) and a class representative `τ c` in the upper half-plane for each ideal
class (from the repository's `exists_isIdealClassPoint`). The class-number theorems then close
GRH and the formula in one line each.

Real output of `scripts/check-unconditional.sh /home/ubuntu/work/personal/riemann-hypothesis`
(2026-11-24, this commit, 36 min wall, most of it importing the riemann-hypothesis modules):

```
'leastNonresidueBelowLogSq_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'bach_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LLS.chunk114_ok_0._native.native_decide.ax_1_1,
 …,
 LLS.chunk114_ok_9._native.native_decide.ax_1_1]
'leastNonresidue_unconditional' depends on axioms: (the same nineteen)
'miller_unconditional' depends on axioms: (the same nineteen)
'l1UpperBoundWith_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'l1LowerBoundWith_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(The `l1` lines are from the rerun at `6f10c52`, 44 min wall on a loaded box. The rerun on
branch `round5`, 15 min wall, printed the same lines for the six theorems above and:)

```
'classNumberFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'classNumberUpperBoundOddWith_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'classNumberLowerBoundOddWith_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The rerun on branch `round6` (8 min wall) printed the same lines for all nine theorems above
and:

```
'classNumberUpperBoundWith_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'classNumberLowerBoundWith_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The sixteen elided lines are `LLS.chunk114_ok_i._native.native_decide.ax_1_1` for every
`0 ≤ i ≤ 15`, exactly as in the main-library output above.

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM; raise the open-file limit first (Linux:
`sudo prlimit --pid $$ --nofile=2000000:2000000`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* The analytic toolkit (Hadamard factorisation, Perron/Mellin kernels, the Cesàro explicit
  formula, digamma series) is the [erdos-985](https://github.com/senamakel/erdos-985) library,
  a lake dependency; several proofs here adapt its patterns.
* The generation checker and its soundness proof are ankeny-grh's (`AnkenyCheck.lean`,
  `Ankeny/Checker.lean`, `Ankeny/Finite.lean`), used as a dependency, not copied;
  `Ankeny.exists_dirichletCharacter_trivial_on` and `Ankeny.leastNonresidue_of_bach'` likewise.
* Mertens' third theorem under RH (`Robin.mertens_RH`, `Robin.psi_upper`, `Robin.psi_lower`,
  `Robin.psi1NatBound_of_bachBound`) is robin-rh's (`dfa8d63`), a lake dependency.
* GRH (`LFunction_ne_zero_of_half_lt_re`) and the class number formula
  (`GlobalTheory.LFunction_one_and_mean_log_eta`) come from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
  commit `507a75d`, imported only from `Unconditional/`. That repository has no licence file.
* No files are vendored.
