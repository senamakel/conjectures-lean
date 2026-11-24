# Primes in arithmetic progressions under GRH in Lean

**Literature status: RH-consequence.** Titchmarsh (1930) proved that GRH for the Dirichlet
L-functions modulo `q` implies, for every character `χ` mod `q` and every `x ≥ 2`,

```
ψ(x, χ) = E₀(χ) x + O(√x (log x)(log qx)),
ϑ(x, χ) = E₀(χ) x + O(√x (log x)(log qx)),
π(x, χ) = E₀(χ) li(x) + O(√x log qx),
```

and, for `(a, q) = 1`, `ψ(x; q, a) = x/φ(q) + O(√x log² x)`,
`ϑ(x; q, a) = x/φ(q) + O(√x log² x)`, `π(x; q, a) = li(x)/φ(q) + O(√x log x)`, with absolute
implied constants. We follow the statements of Montgomery–Vaughan, *Multiplicative Number
Theory I* (Cambridge 2007), Theorem 13.7 and Corollary 13.8, which attribute them to Titchmarsh
(1930); see also Davenport, *Multiplicative Number Theory*, Ch. 20. Without GRH the error terms
are open: the best unconditional results (Siegel–Walfisz) save only a power of
`exp(−c √log x)` and need `q ≤ (log x)^A`. `Unconditional/` proves all five bounds
unconditionally in Lean, uniform in `q`, with GRH supplied by the certified proof in
leanprover-community/riemann-hypothesis and the two classical inputs taken from the same
repository.

The main library is a complete Lean proof that GRH implies these bounds, following the classical
argument (truncated explicit formula at height `T = x`, zero counting in unit windows,
reduction to primitive characters), with one absolute constant for every modulus:

```lean
theorem PsiGRH.psiChar_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PsiCharStatement

theorem PsiGRH.psiCharLogSq_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PsiCharLogSqStatement

theorem PsiGRH.psiAP_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PsiAPStatement

theorem PsiGRH.thetaAP_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : ThetaAPStatement

theorem PsiGRH.piAP_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hEF : TruncatedExplicitFormula) (hZ : ZeroWindowCount) : PiAPStatement
```

The targets, fixed in `PsiGRH/Statement.lean` (abridged; every `Bound C` is `∀`-quantified over
`q ≥ 1`, characters or residues `a` coprime to `q`, and `x ≥ 2`):

```lean
noncomputable def psiChar {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ n
noncomputable def mainTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  if χ = 1 then (x : ℂ) else 0
noncomputable def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

def PsiCharBound (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
    ‖psiChar χ x - mainTerm χ x‖ ≤ C * Real.sqrt x * Real.log x * Real.log (q * x)
def PsiCharLogSqBound (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
    ‖psiChar χ x - mainTerm χ x‖ ≤ C * Real.sqrt x * Real.log (q * x) ^ 2
def PsiAPBound (C : ℝ) : Prop :=
  ∀ (q a : ℕ), 1 ≤ q → a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |psiAP q a x - x / q.totient| ≤ C * Real.sqrt x * Real.log x * Real.log (q * x)
def ThetaAPBound (C : ℝ) : Prop := -- same shape for thetaAP
def PiAPBound (C : ℝ) : Prop :=
  ∀ (q a : ℕ), 1 ≤ q → a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |(primeCountAP q a x : ℝ) - li x / q.totient| ≤ C * Real.sqrt x * Real.log (q * x)

def PsiCharStatement : Prop := ∃ C : ℝ, 0 < C ∧ PsiCharBound C      -- likewise for the others
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `PsiGRH.psiChar_of_GRH` | C + H | GRH; `TruncatedExplicitFormula`, `ZeroWindowCount` |
| `PsiGRH.psiCharLogSq_of_GRH` | C + H | same |
| `PsiGRH.psiAP_of_GRH` | C + H | same |
| `PsiGRH.thetaAP_of_GRH` | C + H | same |
| `PsiGRH.piAP_of_GRH` | C + H | same |
| `psiChar_unconditional`, `psiCharLogSq_unconditional`, `psiAP_unconditional`, `thetaAP_unconditional`, `piAP_unconditional` (`Unconditional/`) | U | none; all three supplied by riemann-hypothesis |

* GRH is `Erdos985.DirichletLNonvanishingRightOfHalf`, copied word for word in erdos-985 from
  `src/Statements.lean` of
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
* `TruncatedExplicitFormula` and `ZeroWindowCount` (`PsiGRH/Inputs.lean`) are two classical,
  **unconditional** facts about primitive Dirichlet L-functions, stated in this repository's
  own words in Mathlib terms: the truncated explicit formula for `ψ(u, χ)` with an error
  uniform in the modulus (Davenport Ch. 17 and 19; Montgomery–Vaughan Ch. 12), and the bound
  `≪ log(q(|t| + 2))` for the number of zeros with `|Im ρ − t| ≤ 1` (Davenport Ch. 16;
  Montgomery–Vaughan Theorem 10.17). Neither involves GRH. Proving them here would mean a
  uniform truncated Perron formula and contour shift for Dirichlet L-functions, which neither
  Mathlib nor erdos-985 has (erdos-985's explicit formula is the Cesàro-weighted one, which
  gives only `x^{3/4}` after unsmoothing; see "Deviations").
* No formal-conjectures statement exists for any of the targets; they are this repository's
  transcription of Montgomery–Vaughan (13.19), (13.22)–(13.24).
* The main library never imports riemann-hypothesis. `Unconditional/PsiGRHUnconditional.lean`
  discharges GRH with `LFunction_ne_zero_of_half_lt_re`, `ZeroWindowCount` with
  `GlobalTheory.ZeroWindow.count_zeros_window` (a definitional match), and
  `TruncatedExplicitFormula` with `GlobalTheory.ExplicitFormula.truncated_explicit_formula`
  through a three-line bridge (`psi0_eq`: that repository's `psi0 χ u` is
  `ψ(u, χ) − E₀(χ) u`). Nothing is copied from riemann-hypothesis, which has no licence.

**What is uniform in `q`.** Everything: each statement has one constant for all moduli `q ≥ 1`,
all characters (primitive or not, principal or not), all residues and all `x ≥ 2`. The
constants are existential, because the two cited inputs are existential. They are explicit in
terms of those: with `C₁`, `C₂` the constants of `TruncatedExplicitFormula` and
`ZeroWindowCount`, `PsiCharBound (32 C₂ + C₁ (6 + 32 C₂) + 8)`, `PsiAPBound` with the same
constant, `ThetaAPBound` with `+ 3`, and `PiAPBound (4 (C + 3) + 5)`.

## Axioms

`scripts/check-axioms.sh` (`lake env lean` on a file with `#print axioms` after
`import PsiGRH`), run 2026-11-24:

```
'PsiGRH.psiChar_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'PsiGRH.psiCharLogSq_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'PsiGRH.psiAP_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'PsiGRH.thetaAP_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'PsiGRH.piAP_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom check passed
```

No `sorry`, no `native_decide`, no `axiom` or `opaque` declarations, no finite computation.

## Proof outline

1. **Zeros on the line** (`PsiGRH/ZeroSum.lean`, `re_eq_half_of_GRH`). A zero of a primitive
   `L(s, χ)` with `0 < Re ρ < 1` is a zero of the completed L-function; GRH and the functional
   equation (erdos-985's `completedLFunction_inv_eq_zero`) force `Re ρ = 1/2`, so
   `|u^ρ/ρ| = √u/|ρ|` and `|ρ| ≥ (⌊|Im ρ|⌋ + 1)/2`.
2. **The zero sum** (`sum_stripZeros_le`). Slice the zeros with `|Im ρ| < T` by
   `k = ⌊|Im ρ|⌋`; each slice lies in the windows at `±k`, so holds `≤ 2 C₂ log(N(T + 2))`
   zeros. With the harmonic bound,
   `Σ_{|Im ρ| < T} m_ρ/|ρ| ≤ 4 C₂ log(N(T + 2)) (1 + log(T + 1))`.
3. **Primitive characters** (`PsiGRH/Primitive.lean`). `T = u` in the explicit formula:
   `|ψ(u, χ) − E₀(χ) u| ≤ 32 C₂ √u (log u)(log Nu) + C₁ (6 + 32 C₂) log²(Nu)`.
4. **All characters** (`PsiGRH/Imprimitive.lean`). `χ` and its primitive character `χ*` agree
   off the `n` sharing a factor with `q`, so `|ψ(u, χ) − ψ(u, χ*)| ≤ ω(q) log u` and
   `ω(q) log 2 ≤ log q`; `E₀(χ*) = E₀(χ)`.
5. **(13.19)** (`PsiGRH/Character.lean`). If `log qx ≤ √x log x` the term `log²(qx)` is
   `≤ √x (log x)(log qx)`; otherwise `√x < 2 log qx` and the trivial bound
   `|ψ(x, χ) − E₀(χ) x| ≤ x log x + x ≤ 6 √x (log x)(log qx)` wins.
6. **Progressions** (`PsiGRH/Progression.lean`). Orthogonality of characters and the triangle
   inequality over the `φ(q)` characters; `0 ≤ ψ(x; q, a) − ϑ(x; q, a) ≤ ψ(x) − ϑ(x) ≤ 2√x log x`
   (Mathlib's `Chebyshev.psi_sub_theta_le`).
7. **Prime counts** (`PsiGRH/PrimeCount.lean`). Abel summation (Mathlib's
   `sum_mul_eq_sub_sub_integral_mul`) gives
   `π(x; q, a) − li(x)/φ(q) = E(x)/log x + ∫₂ˣ E(t)/(t log² t) dt + 2/(φ(q) log 2)` with
   `E(t) = ϑ(t; q, a) − t/φ(q)`, and `∫₂ˣ dt/√t ≤ 2√x`.

## Layout

| File | Content |
|---|---|
| `PsiGRH/Statement.lean` | the fixed targets |
| `PsiGRH/Inputs.lean` | the two cited analytic inputs (tier H) |
| `PsiGRH/ZeroSum.lean` | `Re ρ = 1/2` under GRH; `Σ m_ρ/\|ρ\|` over `\|Im ρ\| < T` |
| `PsiGRH/Primitive.lean` | the bound for primitive characters; trivial bounds |
| `PsiGRH/Imprimitive.lean` | reduction to the primitive character |
| `PsiGRH/Character.lean` | (13.19) and the `log²(qx)` form |
| `PsiGRH/Progression.lean` | `ψ(x; q, a)` and `ϑ(x; q, a)` |
| `PsiGRH/PrimeCount.lean` | `π(x; q, a)` by Abel summation |
| `PsiGRH/Main.lean` | headline theorems |
| `Unconditional/PsiGRHUnconditional.lean` | the riemann-hypothesis discharge |

## Deviations from the literature

* **Uniform forms.** Montgomery–Vaughan's (13.22)–(13.24) have error `√x log² x` and
  `√x log x`; their proof first reduces to `q ≤ √x` using the trivial bound and a lower bound
  for `φ(q)`. We state and prove the uniform form `√x (log x)(log qx)` (and `√x log qx` for
  `π`), which is the bound their proof gives before that reduction, and implies theirs for
  `q ≤ x` because `log qx ≤ 2 log x` there.
* **`li`.** `li(x) = ∫₂ˣ dt/log t`; the principal-value integral differs by `li(2) ≈ 1.045`,
  absorbed by the error term.
* **Existential constants.** The constants depend on those of the two cited inputs, which are
  existential in riemann-hypothesis, so no numerical constant is available. This library
  therefore serves `O(·)` targets, not targets that end in a finite check.
* **Why not erdos-985's explicit formula.** erdos-985 has a weighted (Cesàro, `ψ₁`) explicit
  formula under GRH. Unsmoothing `ψ₁` by differencing over an interval of length `h` costs
  `x^{3/2}/h + h`, i.e. `x^{3/4}` at best, so `√x` needs a truncated (sharp-cutoff) explicit
  formula, which is exactly `TruncatedExplicitFormula`.

## Building

```
lake exe cache get
lake build                    # target PsiGRH
scripts/check-axioms.sh
```

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 at `9538edb`. After the Mathlib cache and the
erdos-985 modules it imports (`Erdos985.Analytic.ExplicitFormula.StepA`, about 2 minutes),
the library builds in about 30 s; no module is expensive.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `psiChar_unconditional` | `PsiGRH.PsiCharStatement` | standard three |
| `psiCharLogSq_unconditional` | `PsiGRH.PsiCharLogSqStatement` | standard three |
| `psiAP_unconditional` | `PsiGRH.PsiAPStatement` | standard three |
| `thetaAP_unconditional` | `PsiGRH.ThetaAPStatement` | standard three |
| `piAP_unconditional` | `PsiGRH.PiAPStatement` | standard three |

Each is the corresponding `_of_GRH` theorem applied to `LFunction_ne_zero_of_half_lt_re`,
`truncatedExplicitFormula` and `zeroWindowCount`, all from
leanprover-community/riemann-hypothesis at commit `507a75d91d`. These are the bounds with no
hypothesis left.

```
sudo prlimit --pid $$ --nofile=2000000:2000000   # the import opens ~900k files
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

The import needs about 93 GB of cache, about 19 GB of RAM (36 GB peak resident on this run, with
`Main` imported) and an open-file limit near 900k. Output on 2026-11-24 at this repository's
`9a50782`:

```
'truncatedExplicitFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeroWindowCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'psiChar_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'psiCharLogSq_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'psiAP_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'thetaAP_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'piAP_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

*The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.*

## Credits

No file is vendored. The repository requires
[senamakel/erdos-985](https://github.com/senamakel/erdos-985) (GRH statement, functional
equation lemmas) and imports, only in `Unconditional/`,
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
at `507a75d91d`.
