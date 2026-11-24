# The least quadratic non-residue under GRH (Lamzouri–Li–Soundararajan) in Lean

**Literature status: RH-consequence.** Lamzouri, Li and Soundararajan (*Conditional bounds for
the least quadratic non-residue and related problems*, Math. Comp. 84 (2015) 2391–2412,
[arXiv:1309.3595](https://arxiv.org/abs/1309.3595)) proved under GRH that the least quadratic
non-residue mod a prime `q ≥ 5` is below `(log q)²` (their Corollary 1.2), and that the least
prime `ℓ ∤ q` outside a proper subgroup of `(ℤ/q)ˣ` is at most `(log q + B(q))²` (Theorem 1.1).
Unconditionally only Burgess-type bounds `q^{1/(4√e)+ε}` are known. This repository is a Lean
proof that GRH implies LLS Corollary 1.2, following LLS, and a Lean proof that GRH implies
Bach's subgroup bound with constant `11/4` (Bach, Math. Comp. 55 (1990), proved `2`; the companion
ankeny-grh repository proves `21/5`). Our constant `11/4` is weaker than Bach's `2`. It is also a
Lean proof that GRH implies bounds of the shape of LLS Theorem 1.5 for `L(1, χ)`, `χ` primitive
mod `q ≥ 10¹⁰`, with weaker constants than the paper's: `|L(1,χ)| ≤ 2e^γ(log log q + 5)` (LLS:
`2e^γ(log log q − log 2 + 1/2 + 1/log log q)`) and `1/|L(1,χ)| ≤ 2e^γ(log log q + 5)` (LLS:
`(12e^γ/π²)(log log q − log 2 + 1/2 + …)`). See "Deviations".

```lean
theorem LLS.leastNonresidueBelowLogSq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBelowLogSq
theorem LLS.bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound (11 / 4)
theorem LLS.leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound (11 / 4)
theorem LLS.miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement (11 / 4)
theorem LLS.l1UpperBoundWith_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : L1UpperBoundWith 5
theorem LLS.l1LowerBoundWith_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : L1LowerBoundWith 5
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

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `leastNonresidueBelowLogSq_of_GRH` | C (U in `Unconditional/`) | GRH |
| `bach_of_GRH`, `leastNonresidue_of_GRH`, `miller_of_GRH` | C (U in `Unconditional/`) | GRH |
| `l1UpperBoundWith_of_GRH`, `l1LowerBoundWith_of_GRH` | C (U in `Unconditional/`) | GRH |

GRH is `Erdos985.DirichletLNonvanishingRightOfHalf`, copied word for word in erdos-985 from
`src/Statements.lean` of [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
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
```

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

1. **Explicit formulas** (`LLS/Analytic/`), for `χ` primitive mod `N`, under GRH, with
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
2. **Key inequality** (`LLS/Key.lean`, LLS §3): if `χ ≠ 1` mod `q` is `1` on all `n ≤ x` prime
   to `q`, symmetrising over the inducing `ψ` and `ψ⁻¹` bounds `Z2` from Lemma 2.3 (the sum
   `Σ_{n<x} Λ(n)/n (1−n/x) ≈ log x` is now large, which is LLS's `A(q)` gain) and contradicts
   Lemma 2.2 against the principal sum `≈ x`. Prime powers `p^k ≤ x` with `p ∣ q` are the
   losses (`LLS/Losses.lean`); primes dividing `q` but not the conductor are charged to
   `log f ≤ log q − Σ log p`.
3. **Budget** (`Numerics/Budget.lean`): the key inequality forces `Φ(x, log q) ≤ 0` for an
   explicit `Φ`; primes `p ≥ 17` dividing `q` cost at most `β log p` each,
   `β = (log x)²/(2 log 17) + K/8`, and `p < 17` are listed. For prime `q > x` the losses
   vanish and the budget is `Φ₁` (`Numerics/Prime.lean`).
4. **Numerics**: `Φ(⌊(11/4) log² Q_a⌋, log Q_b) > 0` on 28 certified intervals covering
   `2^18 ≤ q < 2^700` (`Numerics/Intervals114.lean`, generated by `scripts/emitfile.py`), and
   for `q ≥ 2^700` by a polynomial argument in `x^{1/8}` (`Numerics/Tail114.lean`, reusing
   `Numerics/Tail.lean`). For primes:
   `Φ₁ > 0` with `x = ⌊log² q⌋` on 153 intervals covering `2^12 ≤ q < 2^700`
   (`Numerics/IntervalsP.lean`, `scripts/emit1.py`) and `q ≥ 2^700` (`Numerics/TailP.lean`).
5. **Finite ranges**: primes `5 ≤ q < 2^12` by Euler-criterion certificates
   (`LLS/NonresidueCert.lean`, `scripts/emit_small.py`); `q < 2^18` for the subgroup bound by
   ankeny-grh's checker (`LLS/Finite114.lean`, `LLS/Compute/C114_*.lean`).
6. **`L(1, χ)`** (`LLS/L1/`), for `χ` primitive mod `q ≥ 10¹⁰`:
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
| `scripts/*.py` | Generators for the certificates and the sizing computations |

## Deviations from the literature

* **Subgroup bound: constant `11/4`, not LLS's `(log q + B(q))²` or Bach's `2`.** We prove the
  LLS method with somewhat weaker constants: the principal sum is bounded by summation by parts
  (`x − 0.15√x − 3 log x − 3` instead of LLS Lemma 2.1's `x − 0.046√x − 1.84 log x − 1`), the
  Mertens-type sum unconditionally (`log x − 2` instead of `log x − 1.577`), and the cost of a
  prime factor `p ≥ 17` of `q` crudely (`β log p`). Moduli with many small prime factors are
  the worst case. With exact prime-power losses the analytic argument would need `q ≥ 2^16.9`
  for `c = 5/2`, `2^21` for `9/4` and `2^28.7` for `2`; the finite check is a graph search over
  `(ℤ/q)ˣ`, about `2.3` CPU-hours up to `2^18` at `c = 11/4`, growing like `q²`. So `c = 2`
  is out of reach by this route; with the bounds formalised here `c = 5/2` needs the
  computation to about `2^20` (roughly 16 times the current one) and `c = 11/4` is what fits.
* **Theorem 1.1 as stated is not proved.** Our constants are weaker than LLS's, so we do not
  get `ℓ ≤ (log q + B(q))²`. Also, as written, the proof of LLS Theorem 1.1 appears to bound
  `Σ Λ(n) χ̃(n)/n (1 − n/X)` as if `χ̃(p) = 1` for primes `p ∣ q`, `p ∤ q̃`; for such `p`
  `χ̃(p)` is unknown. Our `LLS.key` charges these primes twice and absorbs them through
  `log f ≤ log q − Σ log p`.
* **Theorem 1.5 with weaker constants.** We prove LLS Lemma 2.5 (`LLS.log_norm_L1_le`, standard
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
* **Corollary 1.3 (class numbers) is not attempted**: it needs Dirichlet's class number formula
  for imaginary quadratic fields, which Mathlib does not have at this pin.
* **Theorem 1.4 (cosets) is not proved.**
* Corollary 1.2 is proved exactly as stated (`LeastNonresidueBelowLogSq`).

## Building

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`; also requires ankeny-grh
`129ad57`, miller-grh `b484d44` and robin-rh `dfa8d63`). On a 95-core box with warm caches: the sixteen
`native_decide` chunks take about 2.3 CPU-hours (the slowest, `C114_15`, 1884 s); the certified
intervals take 141 s (`Intervals114`) and 77 s (`IntervalsP`); everything else is under a minute
per module.

## Unconditional version

`Unconditional/LLSUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the GRH hypothesis in one line. These are the statements above,
given the Lean proof of GRH in leanprover-community/riemann-hypothesis, which has not been
independently verified.

| Theorem | Statement | Axioms |
|---|---|---|
| `leastNonresidueBelowLogSq_unconditional` | `LLS.LeastNonresidueBelowLogSq` | standard three |
| `bach_unconditional` | `Ankeny.BachSubgroupBound (11 / 4)` | standard three + 16 `native_decide` |
| `leastNonresidue_unconditional` | `Ankeny.LeastNonresidueBound (11 / 4)` | standard three + 16 `native_decide` |
| `miller_unconditional` | `Miller.MillerStatement (11 / 4)` | standard three + 16 `native_decide` |
| `l1UpperBoundWith_unconditional` | `LLS.L1UpperBoundWith 5` | see the output below |
| `l1LowerBoundWith_unconditional` | `LLS.L1LowerBoundWith 5` | see the output below |

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
```

The sixteen elided lines are `LLS.chunk114_ok_i._native.native_decide.ax_1_1` for every
`0 ≤ i ≤ 15`, exactly as in the main-library output above.

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM; raise the open-file limit first (Linux:
`sudo prlimit --pid $$ --nofile=2000000:2000000`).

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

* The analytic toolkit (Hadamard factorisation, Perron/Mellin kernels, the Cesàro explicit
  formula, digamma series) is the [erdos-985](https://github.com/senamakel/erdos-985) library,
  a lake dependency; several proofs here adapt its patterns.
* The generation checker and its soundness proof are ankeny-grh's (`AnkenyCheck.lean`,
  `Ankeny/Checker.lean`, `Ankeny/Finite.lean`), used as a dependency, not copied;
  `Ankeny.exists_dirichletCharacter_trivial_on` and `Ankeny.leastNonresidue_of_bach'` likewise.
* Mertens' third theorem under RH (`Robin.mertens_RH`, `Robin.psi_upper`, `Robin.psi_lower`,
  `Robin.psi1NatBound_of_bachBound`) is robin-rh's (`dfa8d63`), a lake dependency.
* No files are vendored.
