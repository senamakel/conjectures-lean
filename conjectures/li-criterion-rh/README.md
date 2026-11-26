# Li's criterion from RH in Lean

Li (*J. Number Theory* 65 (1997) 325–333) showed that the Riemann hypothesis is equivalent to
the positivity of the numbers `λₙ = Σ_ρ (1 − (1 − 1/ρ)ⁿ)`, `n ≥ 1`, the sum running over the
nontrivial zeros of ζ. Bombieri and Lagarias (*J. Number Theory* 77 (1999) 274–287) gave a
general form of the criterion for any multiset of complex numbers with a mild summability
condition. Before the 2026 proof of RH, `λₙ > 0` was known only for finitely many `n` (by
computation. This project is a complete Lean proof that RH implies `λₙ > 0` for every `n ≥ 1`,
and `Unconditional/` proves `λₙ > 0` for every `n ≥ 1` unconditionally in Lean, with RH supplied
by the certified proof of L. Alpöge in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
Both use the standard three axioms only. Literature status: RH-equivalent. The criterion is Li
(1997) and Bombieri–Lagarias (1999); positivity of every `λₙ` is equivalent to RH (Li), so
this theorem is RH in another form.

```lean
theorem RiemannHypothesis.li_criterion_rhs_of_RH (hRH : RiemannHypothesis) : LiCriterionRHS
-- LiCriterionRHS := ∀ {n : ℕ} (_hn : 0 < n), 0 < lambda n

theorem li_criterion_rhs {n : ℕ} (hn : 0 < n) : 0 < RiemannHypothesis.lambda n
  -- Unconditional/LiCriterionUnconditional.lean
```

## Tier and provenance

`RiemannHypothesis.li_criterion_rhs_of_RH` and its restatement
`RiemannHypothesis.li_criterion_forward : RiemannHypothesis → ∀ n > 0, 0 < lambda n` are tier C:
RH is the explicit hypothesis, Mathlib's `RiemannHypothesis`, used as is. `li_criterion_rhs` is
tier U: it closes the hypothesis with `riemannHypothesis` from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
in one line. There are no cited (tier H) hypotheses.

The target is formal-conjectures'
[`RiemannHypothesis.li_criterion_rhs`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Paper/RiemannHypothesisEquivalents.lean)
(category `research open`; it is equivalent to RH). `LiCriterion/Statement.lean` copies `nontrivialPosZeros` and
`lambda` from it word for word, at commit `86a2f58a`, and records `li_criterion_rhs` and
`li_criterion` as the `Prop`s `LiCriterionRHS` and `LiCriterion`. `li_criterion_rhs` above has
exactly formal-conjectures' signature.

### How the target is formalised

```lean
def nontrivialPosZeros : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ riemannZeta z = 0}
noncomputable def lambda (n : ℕ) : ℝ := ∑' ρ : nontrivialPosZeros, 2 * (1 - (1 - 1 / ρ.1) ^ n).re
```

Three features of this definition matter for the proof:

1. The sum is a real `tsum`, which is `0` for a non-summable family. So `0 < lambda n` also
   asserts summability, and the proof establishes it (`summable_lambda_summand_of_RH`) from
   `Σ ‖ρ‖⁻² < ∞`.
2. Zeros form a set, so multiplicities are ignored, unlike in Li's `λₙ`. Under RH every summand
   is `≥ 0`, so dropping repeated terms keeps the sum positive. The converse direction is also
   unaffected, as Bombieri–Lagarias's criterion applies to any symmetric family of zeros.
3. Only zeros with `Im ρ > 0` appear, with summand `2 Re(·)`. This is the conjugate-pair
   grouping, and it makes the unordered sum meaningful.

The project proves the forward direction of `li_criterion` (RH ⇒ positivity). The converse
(Bombieri–Lagarias) is not formalised here.

## Axioms

`#print axioms`, run with `lake env lean` on a file importing `LiCriterion` (2026-11-24):

```
'RiemannHypothesis.li_criterion_rhs_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.li_criterion_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.exists_nontrivialPosZeros_norm_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.summable_inv_sq_nontrivialPosZeros' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the standard three axioms. The project has no `sorry`, no `native_decide` and no
`axiom` or `opaque` declarations.

## Proof outline

1. `Σ_ρ ‖ρ‖⁻² < ∞` (`LiCriterion/Zeros.lean`, `summable_inv_sq_nontrivialPosZeros`,
   unconditional). Every `ρ ∈ nontrivialPosZeros` is a zero of erdos-985's entire
   `ξ(s) = s(s − 1)Λ(s)` (`xiZeta`). erdos-985's `hadamard_logDeriv` (order ≤ 1, from the
   vendored PrimeNumberTheoremAnd Hadamard factorisation) gives `Σ m_ρ ‖ρ‖^{-(1+ε)} < ∞`; take
   `ε = 1` and `m_ρ ≥ 1`.
2. ζ has infinitely many nontrivial zeros (`exists_nontrivialPosZeros_norm_gt`, unconditional):
   for every `R` there is `ρ ∈ nontrivialPosZeros` with `‖ρ‖ > R`. Otherwise every zero of `ξ` has
   norm `≤ max R 1` (zeros lie in `0 < Re < 1`; `ζ(ρ̄) = conj ζ(ρ)` handles `Im ρ < 0`), so the
   multiplicity index is finite (its terms `‖ρ‖⁻² ≥ R⁻²` are summable). The genus-1 Hadamard
   product is then a finite product of `E₁(u) = (1 − u)eᵘ`, `‖E₁(u)‖ ≤ e^{2‖u‖}`, so
   `‖ξ(z)‖ ≤ exp(A + B‖z‖)`. But `‖ξ(2n + 2)‖ ≥ n!/π^{n+1}` (from `Γℝ(2n+2) = π^{−(n+1)} n!` and
   `Re ζ(x) ≥ 1` for `x > 1`), and `cⁿ/n! → 0`.
3. Under RH each summand is `‖1 − wⁿ‖²` with `w = 1 − 1/ρ` (`LiCriterion/Main.lean`).
   `Re ρ = 1/2` gives `|ρ − 1| = |ρ|`, so `‖w‖ = 1`, and `2 Re(1 − v) = ‖1 − v‖²` on the unit
   circle.
4. Summability: `‖1 − wⁿ‖ ≤ n‖1 − w‖ = n/‖ρ‖`, so each summand lies in `[0, n²‖ρ‖⁻²]`;
   compare with step 1.
5. Strict positivity: `‖1 − wⁿ − n(1 − w)‖ ≤ n²‖1 − w‖²`, so with `δ = 1/‖ρ‖`,
   `‖1 − wⁿ‖ ≥ nδ(1 − nδ) > 0` once `‖ρ‖ > n`. Step 2 supplies such a zero, and
   `Summable.tsum_pos` gives `λₙ > 0`.

| File | Content |
|---|---|
| `LiCriterion/Statement.lean` | `nontrivialPosZeros`, `lambda` (verbatim), `LiCriterionRHS`, `LiCriterion` |
| `LiCriterion/Zeros.lean` | steps 1 and 2: `Σ‖ρ‖⁻² < ∞`, infinitely many zeros (unconditional) |
| `LiCriterion/Main.lean` | steps 3 to 5: `li_criterion_rhs_of_RH`, `li_criterion_forward` |
| `Unconditional/LiCriterionUnconditional.lean` | `li_criterion_rhs`, RH discharged |

## Deviations from the literature

The statement proved is formal-conjectures' target exactly. Li's `λₙ` counts zeros with
multiplicity; formal-conjectures' `lambda`, the target here, does not (see above). The proof
that ζ has infinitely many nontrivial zeros uses the order-1 Hadamard factorisation and
factorial growth without Stirling, because Mathlib does not have the Riemann–von Mangoldt
formula.

## Building

```bash
lake exe cache get   # Mathlib
lake build           # target LiCriterion
```

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 `9538edb` (lake dependency). With the Mathlib
cache, building the needed erdos-985 modules and this library takes about a minute of wall time;
the three `LiCriterion` modules take a few seconds each. There are no `native_decide` modules.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `RiemannHypothesis.li_criterion_rhs_of_RH` | `RiemannHypothesis → LiCriterionRHS` | standard three |
| `li_criterion_rhs` | `∀ {n : ℕ}, 0 < n → 0 < RiemannHypothesis.lambda n` | standard three |

Checked against riemann-hypothesis commit `507a75d91d`:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # clones it there if missing
```

Output for `li_criterion_rhs` (2026-11-24, li-criterion-rh `24fbe0b`, riemann-hypothesis
`507a75d91d131d627b380df4e32f6e9fb21dd067`):

```
'li_criterion_rhs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The script uses that project's community cache, about 93 GB. The import needs about 19 GB of
RAM and opens around 900,000 module files, so raise the open-file limit first (Linux:
`sudo prlimit --pid $$ --nofile=2000000:2000000`; macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`, then
`ulimit -n 1400000`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

- `LiCriterion/Statement.lean` copies `nontrivialPosZeros` and `lambda` from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  `FormalConjectures/Paper/RiemannHypothesisEquivalents.lean` at commit `86a2f58a`
  (Apache-2.0, © 2026 The Formal Conjectures Authors).
- RH (`riemannHypothesis`): from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
  checked against commit `507a75d91d`, imported only from `Unconditional/`. That repository has
  no licence file.
- No other file is vendored. The Hadamard factorisation comes through the erdos-985 dependency,
  which vendors it from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (Apache-2.0, see erdos-985's `Vendor/PNT/NOTICE.md`).
