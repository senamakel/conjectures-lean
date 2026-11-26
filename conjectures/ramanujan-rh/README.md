# Ramanujan's prime-counting inequality under RH in Lean

This project proves in Lean that the Riemann hypothesis implies Ramanujan's inequality

  `π(x)² < (e x / log x) · π(x/e)`

for every real `x ≥ e⁴⁰ ≈ 2.354·10¹⁷`, with no computation and no cited input:
`Ramanujan.ramanujan_of_RH : RiemannHypothesis → RamanujanInequalityFrom (Real.exp 40)`. With the
finite range `38,358,837,683 ≤ x ≤ e⁴⁰` as a cited hypothesis it gives the inequality for every
real `x ≥ 38,358,837,683`, the form of Dudek–Platt's Theorem 1.3. `Unconditional/` closes RH
with the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
so `ramanujan_inequality_from_exp40` is an unconditional Lean theorem.

**Literature status: RH-consequence.** Ramanujan stated the inequality for large `x` in his
notebooks (B. C. Berndt, *Ramanujan's Notebooks, Part IV*, Springer 1994, pp. 112–114).
A. W. Dudek and D. J. Platt, *On solving a curious inequality of Ramanujan*, Exp. Math. 24 (2015),
289–294, arXiv:1407.1901, prove it unconditionally for `x ≥ exp(9658)` (Theorem 1.2) and, under
RH, show that the largest integer counterexample is `38,358,837,682` (Theorem 1.3). The proof here
follows their Lemma 3.2: Schoenfeld's bound for `π − li` under RH, against the asymptotic
expansion of `li`. Unconditionally, D. R. Johnston, Ramanujan J. (2022), arXiv:2109.02249,
Theorem 5.1, proves it for `38,358,837,683 ≤ x ≤ exp(103)`, and the large-`x` range has been
lowered since Dudek–Platt (Platt–Trudgian, as cited by Johnston: `x ≥ exp(3915)`; Axler 2022,
`x ≥ e^{3158.442}`, not read here). The window between `exp(103)` and
the unconditional large-`x` threshold is open without RH; `ramanujan_of_RH` covers it. Two
unrefereed preprints claim a complete unconditional proof: S. De, arXiv:2408.02591 (2024,
claims every `x ≥ exp(43.5102147)`), and J. S. Padhi, Zenodo record 23440770 (2026). Neither has
been checked here.

```lean
-- Ramanujan/Main.lean
theorem Ramanujan.ramanujan_of_RH (hRH : RiemannHypothesis) :
    RamanujanInequalityFrom (Real.exp 40)
theorem Ramanujan.ramanujan_of_RH_of_verified (hRH : RiemannHypothesis)
    (hV : RamanujanVerifiedRange) : RamanujanStatement

-- Ramanujan/Analytic.lean: the analytic core, from Schoenfeld's bound alone
theorem Ramanujan.ramanujan_of_schoenfeldPi (hS : Schoenfeld.SchoenfeldPi) :
    RamanujanInequalityFrom (Real.exp 40)

-- Unconditional/RamanujanUnconditional.lean
theorem ramanujan_inequality_from_exp40 : Ramanujan.RamanujanInequalityFrom (Real.exp 40) :=
  Ramanujan.ramanujan_of_RH riemannHypothesis
theorem ramanujan_of_verified (hV : Ramanujan.RamanujanVerifiedRange) :
    Ramanujan.RamanujanStatement :=
  Ramanujan.ramanujan_of_RH_of_verified riemannHypothesis hV
```

The statements (`Ramanujan/Statement.lean`), with `π(y) = π(⌊y⌋)` as in `Schoenfeld.PiBound`:

```lean
def RamanujanAt (x : ℝ) : Prop :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ^ 2 <
    Real.exp 1 * x / Real.log x * (Nat.primeCounting ⌊x / Real.exp 1⌋₊ : ℝ)
def RamanujanInequalityFrom (X₀ : ℝ) : Prop := ∀ x : ℝ, X₀ ≤ x → RamanujanAt x
def RamanujanStatement : Prop := RamanujanInequalityFrom 38358837683
def RamanujanVerifiedRange : Prop :=
  ∀ x : ℝ, 38358837683 ≤ x → x ≤ Real.exp 40 → RamanujanAt x
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `ramanujan_inequality_from_exp40` (`Unconditional/`) | U | none |
| `ramanujan_of_verified` (`Unconditional/`) | U + H | `RamanujanVerifiedRange` |
| `ramanujan_of_RH` | C | RH |
| `ramanujan_of_RH_of_verified` | C + H | RH, `RamanujanVerifiedRange` |
| `ramanujan_of_schoenfeldPi` | C | `Schoenfeld.SchoenfeldPi` |

* `RiemannHypothesis` is Mathlib's, the hypothesis of schoenfeld-rh's `schoenfeldPi_of_RH`.
* `Schoenfeld.SchoenfeldPi` (`|π(x) − li(x)| < √x log x/(8π)` for real `x ≥ 2657`, with the
  principal-value `Real.logIntegral` vendored from formal-conjectures) is schoenfeld-rh's
  statement of Schoenfeld 1976, Corollary 1, proved there from RH.
* `RamanujanVerifiedRange` is the finite range `[38,358,837,683, e⁴⁰]`. It is covered in the
  literature by Johnston's Theorem 5.1 (unconditional for `38,358,837,683 ≤ x ≤ exp(103)`; its
  proof uses Axler's 2018 computation below `e⁴³` and the Platt–Trudgian verification of RH to
  height `3·10¹²`), and under RH by Dudek–Platt's Lemmas 3.2 and 3.4. It is not computed here:
  it holds about `6·10¹⁵` primes.
* No formal-conjectures statement of Ramanujan's inequality exists (searched at commit
  `9097e2f` for "Ramanujan" and for `π(x/e)`); the statements are written here. No Lean proof
  was found in formal-conjectures, 1337isnot1337/solved-conjectures or a GitHub code search
  (2026-11-26).

## Axioms

`lake env lean scripts/axioms.lean` (2026-11-26):

```
'Ramanujan.ramanujan_of_schoenfeldPi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ramanujan.ramanujan_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Ramanujan.ramanujan_of_RH_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
```

This project adds no `native_decide`. The 23 non-standard axioms are schoenfeld-rh's
proved-sound checkers behind `schoenfeldPi_of_RH`: `psiCert` (an exact segmented sieve of
`|ψ(x) − x| ≤ (4/5)√x` over `[1500, 10¹⁰]`, 20 chunks, about 14 CPU-minutes), the θ bound on
`[599, 3·10⁴]`, and the π bound on `[2657, 4·10⁵]`; see the schoenfeld-rh README.
`ramanujan_of_schoenfeldPi`, the part proved in this project, uses the standard three only.

## Proof outline

Let `x ≥ e⁴⁰`, `u = log x ≥ 40`, `y = x/e` (so `log y = u − 1`) and `ε(t) = √t log t/(8π)`.
Schoenfeld gives `π(x) < li x + ε(x)` and `π(y) > li y − ε(y)`, so it is enough that
`(li x + ε(x))² < (e x/u)(li y − ε(y))`. The main terms differ by about `x²/u⁶`; the errors are
of order `x^{3/2}`.

1. **Expansion of `li` with explicit remainder** (`Ramanujan/LiExpansion.lean`). With
   `I m a y = ∫ₐʸ dt/log^m t`, integration by parts gives
   `I m = y/log^m y − a/log^m a + m · I (m+1)`; iterated eight times,
   `li y = li a + Σ_{k<8} k!(y/log^{k+1} y − a/log^{k+1} a) + 8! · I 9 a y`. The remainder obeys
   `0 ≤ I m` and `I m · (1 − m/log a) ≤ y/log^m y` (from `I (m+1) ≤ I m/log a`). Also
   `0 ≤ li a ≤ 2a` for `a ≥ 2` (from `li 2 ≤ 2` and `1/log t ≤ 2`).
2. **Two-sided bounds** (`Ramanujan/LiBounds.lean`), base point `a = e¹⁵`, `A(ℓ) = Σ_{k<8} k!/ℓ^{k+1}`:
   `y A(log y) − e¹⁵ ≤ li y ≤ y A(log y) + 2e¹⁵ + 100800 · y/log⁹ y` for `y ≥ e¹⁵`
   (`100800 = 8! · 5/2`, since `9/log a = 3/5`).
3. **Growth** (`Analytic.growth`): `u⁷ ≤ 338 √x` for `u ≥ 40`, from
   `√x = e²⁰ e^{u/2−20} ≥ e²⁰ (u/40)⁷` and `40⁷ ≤ 338 e²⁰` (with `e > 2.7182818283`). Hence
   `x ≥ u¹⁴/338²`, and every error term becomes a power of `u` times `x`:
   `ε(x) ≤ 14x/u⁶`, `2e¹⁵ ≤ 9200x/u⁹`, `ε(y) ≤ 23y/u⁶`, `e¹⁵ ≤ 12000y/u⁹`
   (using `√e ≤ 1.6488`, `π > 3.14`, `e¹⁵ ≤ 3269018`).
4. **Bounds for `π`** (`ramanujan_of_schoenfeldPi`): `π(x) < x α(u)/u⁹` and
   `π(y) > y β(u)/(u⁹(u−1)⁸)` with
   `α(u) = Σ_{k<8} k! u^{8−k} + 110000 + 14u³` and
   `β(u) = u⁹ Σ_{k<8} k!(u−1)^{7−k} − (u−1)⁸(12000 + 23u³)`.
5. **The polynomial inequality** (`Ramanujan/Poly.lean`, `poly_ineq`):
   `α(u)² (u−1)⁸ < u⁸ β(u)` for `u ≥ 40`. Substituting `u = 40 + v`, the difference is a
   polynomial of degree 20 in `v` with all 21 coefficients positive (`ring_nf; positivity`);
   its constant term is about `9.0·10³⁰` and its leading coefficient `1`. Then
   `π(x)² < (x α/u⁹)² < (e x/u) · y β/(u⁹(u−1)⁸) < (e x/u) π(y)`.

## Layout

| File | Content |
|---|---|
| `Ramanujan/Statement.lean` | `RamanujanAt`, `RamanujanInequalityFrom`, `RamanujanStatement`, `RamanujanVerifiedRange` |
| `Ramanujan/LiExpansion.lean` | integration by parts for `∫ dt/log^m t`, remainder bounds, `li a ≤ 2a` |
| `Ramanujan/LiBounds.lean` | `li_upper`, `li_lower` with eight terms and base point `e¹⁵` |
| `Ramanujan/Poly.lean` | `alpha`, `beta`, `poly_ineq` |
| `Ramanujan/Analytic.lean` | `growth`, the error-term lemmas, `ramanujan_of_schoenfeldPi` |
| `Ramanujan/Main.lean` | `ramanujan_of_RH`, `ramanujan_of_RH_of_verified` |
| `Unconditional/RamanujanUnconditional.lean` | RH discharged with riemann-hypothesis |

## Deviations from the literature

* **Threshold `e⁴⁰` against Dudek–Platt's `1.15·10¹⁶`.** Dudek–Platt's Lemma 3.2 also uses
  Platt–Trudgian's computation `π(x) < li(x)` for `x ≤ 1.2·10¹⁷`, which removes the `+ε(x)` on
  the upper side. Without it, Schoenfeld's two-sided bound gives the inequality exactly from
  about `x = e^{39.47} ≈ 1.39·10¹⁷` (a high-precision evaluation of
  `(e x/u)(li(x/e) − ε(x/e)) − (li x + ε(x))²`). The explicit eight-term expansion, the base point
  `e¹⁵` and the integer constants above cost the rest: at `u = 40` the proved margin is `0.10`
  of `x²/u⁶`, against `0.24` for the exact functions. `e⁴⁰ ≈ 2.354·10¹⁷` is well below Johnston's
  unconditional `exp(103)`, so the two ranges overlap.
* **The range below `e⁴⁰`** is the cited hypothesis `RamanujanVerifiedRange`, not a theorem
  here.
* **Real variable.** Dudek–Platt state Theorem 1.3 for integers. `RamanujanStatement` is the
  real form `∀ x ≥ 38,358,837,683` (Johnston's Theorem 5.1 states its range this way). The two
  agree there, since `π(⌊x⌋)` is constant on `[n, n+1)` and `(e x/log x) π(x/e)` is
  non-decreasing for `x > e`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985). Requires `Erdos985` (`../erdos-985`) and
`Schoenfeld` (`../schoenfeld-rh`) by path.

```
lake build            # target `Ramanujan`
lake env lean scripts/axioms.lean
```

On top of the built dependencies the project's modules take about 2.5 minutes wall:
`Ramanujan.Poly` 41 s (`ring_nf` on the degree-20 polynomial), `Ramanujan.Analytic` 33 s,
`Ramanujan.Main` 22 s, `Ramanujan.LiExpansion` 9 s, `Ramanujan.LiBounds` 5 s. Building
schoenfeld-rh itself takes about 4.5 CPU-minutes for its analytic library and 17 CPU-minutes for
its finite checks, plus its vendored Rosser closure.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `ramanujan_inequality_from_exp40` | `π(x)² < (e x/log x) π(x/e)` for every real `x ≥ e⁴⁰` | standard three + schoenfeld-rh's 23 `native_decide` (expected) |
| `ramanujan_of_verified` | the same for every real `x ≥ 38,358,837,683`, given `RamanujanVerifiedRange` | the same (expected) |

Check against riemann-hypothesis commit `507a75d91d` with
`scripts/check-unconditional.sh /path/to/riemann-hypothesis` (needs about 93 GB of cache, about
19 GB of RAM and a limit of roughly 900k open files; on Linux run
`sudo prlimit --pid $$ --nofile=2000000:2000000` first). The check has not been run yet for this
project; the axiom column records what the main-library output above implies, and will be
replaced by the script's real output.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

Built by OpenHuman agents. No files are vendored. Schoenfeld's bound and `Real.logIntegral` (vendored
in schoenfeld-rh from formal-conjectures, Apache-2.0) come from the `schoenfeld-rh` lake
dependency.
