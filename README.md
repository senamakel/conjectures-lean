# The Mertens function bound under RH in Lean

Let `M(x) = ∑_{n ≤ x} μ(n)` be the Mertens function. Littlewood (C. R. Acad. Sci. Paris 154
(1912) 263–266; see Titchmarsh, *The Theory of the Riemann Zeta-Function*, ch. 14) proved that
the Riemann hypothesis implies `M(x) = O(x^{1/2+ε})` for every `ε > 0` (the converse also holds
and is not formalised here). The best unconditional bound is of the form
`M(x) ≪ x exp(-c (log x)^{3/5} (log log x)^{-1/5})` (Walfisz, via the Vinogradov–Korobov
zero-free region).

**Literature status: RH-equivalent.** Nothing here is new mathematics. The main library is a
Lean proof that RH implies these bounds, following Littlewood (1912), Riesz (1916) and
Hardy–Littlewood (1916). Each of the Mertens, Riesz and Hardy–Littlewood bounds is equivalent to
RH, so the unconditional theorems in `Unconditional/` say nothing beyond the RH claim: they are
these bounds, given the Lean proof of RH in leanprover-community/riemann-hypothesis, which has not
been independently verified. Redheffer's identity `det R_n = M(n)` is **known** (Redheffer 1977,
no hypothesis); this is a Lean formalisation of it.

The project formalises Littlewood's implication together with its standard companions:

* `1/ζ(s) ≪_{ε,δ} |t|^ε` on `Re s ≥ 1/2 + δ`, `|t| ≥ 1`, under RH (Titchmarsh §14.2);
* Riesz (Acta Math. 40 (1916)): the Riesz function `∑_{k≥1} (-1)^{k+1} x^k / ((k-1)! ζ(2k))` is
  `O(x^{1/4+ε})` under RH;
* Hardy–Littlewood (Acta Math. 41 (1916) 119–196): `∑_n μ(n)/n · e^{-x/n²}` converges and is
  `O(x^{-1/4+ε})` under RH;
* Redheffer (1977): `det R_n = M(n)` for Redheffer's matrix (no hypothesis), hence
  `det R_n = O(n^{1/2+ε})` under RH.

Only the RH ⇒ bound directions are in scope.

```lean
theorem Mertens.invZeta_bound_of_RH (hRH : RiemannHypothesis) : Mertens.InvZetaBound
theorem Mertens.mertens_of_RH (hRH : RiemannHypothesis) : Mertens.MertensBound
theorem Mertens.riesz_of_RH (hRH : RiemannHypothesis) : Mertens.RieszBound
theorem Mertens.hardyLittlewood_of_RH (hRH : RiemannHypothesis) : Mertens.HardyLittlewoodBound
theorem Mertens.det_redheffer (n : ℕ) (hn : 1 ≤ n) : (Mertens.redheffer n).det = Mertens.mertens n
theorem Mertens.redheffer_of_RH (hRH : RiemannHypothesis) : Mertens.RedhefferBound
```

The statements are fixed in [`Mertens/Statement.lean`](Mertens/Statement.lean), e.g.

```lean
noncomputable def mertens (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, μ n

def MertensBound : Prop :=
  ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε)
```

## Tier and provenance

| Theorem | Tier |
|---|---|
| `invZeta_bound_of_RH`, `mertens_of_RH`, `riesz_of_RH`, `hardyLittlewood_of_RH`, `redheffer_of_RH` | **C** (RH is an explicit argument) |
| `det_redheffer` | **D** |
| `invZeta_bound`, `mertens_bound`, `riesz_bound`, `hardyLittlewood_bound`, `redheffer_bound` in `Unconditional/` | **U** |

`RiemannHypothesis` is Mathlib's definition; the main library never imports
riemann-hypothesis. No target has a formal-conjectures counterpart (checked against
google-deepmind/formal-conjectures `86a2f58`: no Mertens, Redheffer, Riesz or Hardy–Littlewood
entry), so the targets are this project's own. There are no cited (tier H) hypotheses.

## Axioms

From `lake env lean scripts/print-axioms.lean` (commit `1191f36`):

```
'Mertens.invZeta_bound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.mertens_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.riesz_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.hardyLittlewood_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.det_redheffer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.redheffer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide`, no `sorry`, no `axiom` or `opaque` declarations.

## Proof outline

The full plan, with each step's Lean statement, is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

1. **`1/ζ ≪ |t|^ε`** (`Mertens/InvZeta.lean`). lindelof-rh supplies a holomorphic logarithm `M`
   of `ζ₁/(s+1)` on `σ > 1/2` with `‖M(σ+it)‖ ≤ C log(|t|+2)^α`, `α < 1`, on `σ ≥ 1/2 + δ`
   (Borel–Carathéodory, then three lines). Hence `‖1/ζ‖ ≤ exp ‖M‖ ≤ C_ε (|t|+2)^ε`.
2. **Line shift** (`Mertens/Shift.lean`). Cauchy's theorem on rectangles moves a vertical line
   integral across a strip when the integrand decays uniformly.
3. **Cesàro–Perron for `μ`** (`Mertens/Perron.lean`). erdos-985's `perron_weighted` at
   `Re s = 2`, moved to `σ₀ = 1/2 + ε`: `∑_{0<n<N} μ(n)(1 - n/N) = (1/2π) ∫ (1/ζ)(s) N^s/(s(s+1)) dt`.
4. **Exact differencing** (`Mertens/Littlewood.lean`). With `A(N) = ∑_{0<n<N} μ(n)(N-n)`,
   `M(N) = A(N+1) - A(N)`. The kernel difference `d = (N+1)^{s+1} - N^{s+1}` obeys
   `‖d‖ ≤ 2(N+1)^{σ+1}` and `‖d‖ ≤ ‖s+1‖(N+1)^σ`; their geometric mean with weight `θ = 2ε`
   makes the integrand `≪ (N+1)^{σ₀+θ}(1+|t|)^{-1-ε}`.
5. **Assembly** (`Mertens/Main.lean`): `|M(N)| ≤ K (N+1)^{1/2+3ε}`, so `M(x) = O(x^{1/2+ε})`.
6. **Redheffer** (`Mertens/Redheffer.lean`). The Möbius matrix `V_{ij} = μ(j/i)[i ∣ j]` is unit
   upper triangular and `V R_n` is lower triangular with diagonal `(M(n), 1, …, 1)`.
7. **Abel summation** (`Mertens/Abel.lean`, `Mertens/Weights.lean`). For a weight `w`,
   `∑ μ(n) w(n) = -∑ M(n)(w(n+1) - w(n))`. The mean value theorem gives two monomial bounds on
   `|w(n+1) - w(n)|` (`2x n^{-3}` and `32 n/x` for the Riesz weight `(x/t²)e^{-x/t²}`;
   `2 n^{-2}` and `5/x` for the Hardy–Littlewood weight `(1/t)e^{-x/t²}`), interpolated to
   `x^P n^{-1-ε}`.
8. **Hardy–Littlewood** (`Mertens/HardyLittlewood.lean`): `P = -1/4 + 2ε`.
9. **Riesz** (`Mertens/Riesz.lean`): `riesz x = ∑ μ(n)(x/n²)e^{-x/n²}` (swap of an absolutely
   convergent double series), then `P = 1/4 + 2ε`.

| File | Content |
|---|---|
| `Mertens/Statement.lean` | target definitions |
| `Mertens/InvZeta.lean` | Step 1, `invZeta_bound_of_RH` |
| `Mertens/Shift.lean` | Step 2, contour shift across a strip |
| `Mertens/Perron.lean` | Step 3, Perron integrand bounds and the shifted formula |
| `Mertens/Littlewood.lean` | Step 4, differencing and the pointwise bound |
| `Mertens/Main.lean` | Step 5, `mertens_of_RH` |
| `Mertens/Redheffer.lean` | Step 6, `det_redheffer` |
| `Mertens/RedhefferBound.lean` | `redheffer_of_RH` |
| `Mertens/Abel.lean` | Step 7, Abel summation and interpolation |
| `Mertens/Weights.lean` | Step 7, the two weights and their differences |
| `Mertens/HardyLittlewood.lean` | Step 8, `hardyLittlewood_of_RH` |
| `Mertens/Riesz.lean` | Step 9, `riesz_eq`, `riesz_of_RH` |
| `Unconditional/MertensUnconditional.lean` | one-line discharges of RH |

## Deviations from the literature

* **No sharp-cutoff Perron formula.** Littlewood's proof truncates Perron's integral. Here the
  exact identity `M(N) = A(N+1) - A(N)` and the interpolated bound on the difference kernel
  replace it (step 4), so only the absolutely convergent Cesàro kernel is used. The exponent is
  the same, `1/2 + ε`.
* **Hardy–Littlewood series.** `∑ μ(n)/n · e^{-x/n²}` converges only conditionally, so
  `hardyLittlewood` is the limit of the partial sums `hlPartial`, and `HardyLittlewoodBound`
  asserts that the limit exists for every `x > 0` as well as the bound. (A `tsum` would be
  Mathlib's junk value `0`.)
* The Riesz and Hardy–Littlewood bounds are derived from the Mertens bound by partial
  summation rather than by a Mellin–Barnes contour shift; the exponents are the classical ones.
* Franel–Landau (Farey sequences) is not formalised.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985). Dependencies: erdos-985 `9538edb` (Perron
kernel) and lindelof-rh `9165bfe` (log ζ bounds), both over HTTPS.

```
lake exe cache get
lake build
lake env lean scripts/print-axioms.lean
```

On the build box the project's own modules take about 5 minutes of wall time after the
dependencies are built; the slowest are `Mertens.Littlewood` (30–100 s), `Mertens.Statement`
(up to 65 s, mostly the Mathlib import) and `Mertens.InvZeta` (10–35 s). There is no
`native_decide`.

## Unconditional version

`Unconditional/MertensUnconditional.lean` imports both this project and
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`), which contains a Lean proof `riemannHypothesis : RiemannHypothesis`, and
closes the hypothesis in one line each. Each row is the stated bound, given that Lean proof of
RH, which has not been independently verified; since the bounds are equivalent to RH, they add
nothing beyond the RH claim.

| Theorem | Statement | Axioms |
|---|---|---|
| `invZeta_bound` | `Mertens.InvZetaBound` | `[propext, Classical.choice, Quot.sound]` |
| `mertens_bound` | `Mertens.MertensBound` | `[propext, Classical.choice, Quot.sound]` |
| `riesz_bound` | `Mertens.RieszBound` | `[propext, Classical.choice, Quot.sound]` |
| `hardyLittlewood_bound` | `Mertens.HardyLittlewoodBound` | `[propext, Classical.choice, Quot.sound]` |
| `redheffer_bound` | `Mertens.RedhefferBound` | `[propext, Classical.choice, Quot.sound]` |

```
scripts/check-unconditional.sh [RH_DIR]
```

Last run 2026-11-24 on this project's commit `1191f36` against riemann-hypothesis `507a75d91d`
(linked from the community cache, not rebuilt): exit 0, 49 min wall time (most of it waiting
for a free slot and loading the RH import), output

```
'invZeta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'mertens_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'riesz_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'hardyLittlewood_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'redheffer_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of riemann-hypothesis cache, about 19 GB of RAM and roughly 900k
open files (on Linux, `sudo prlimit --pid $$ --nofile=2000000:2000000` first).

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No files are vendored. erdos-985 and lindelof-rh are lake dependencies.
