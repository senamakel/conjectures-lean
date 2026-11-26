# Lamzouri–Li–Soundararajan's bounds and Bach's constant 2 under GRH in Lean

This repository proves in Lean every theorem of Lamzouri, Li and Soundararajan, *Conditional
bounds for the least quadratic non-residue and related problems*, Math. Comp. 84 (2015)
2391–2412 ([arXiv:1309.3595](https://arxiv.org/abs/1309.3595)), with the paper's own constants
and thresholds: Theorem 1.1 (both parts), Corollary 1.2, Corollary 1.3, Theorem 1.4 and
Theorem 1.5. It also proves Bach's subgroup bound with Bach's constant `2` (Bach, *Explicit
bounds for primality testing and related problems*, Math. Comp. 55 (1990) 355–380), and with it
the least quadratic non-residue bound `2 log² p` and the correctness of Miller's test with
witnesses `a ≤ 2 log² n`. The main library is a complete Lean proof that GRH for Dirichlet
L-functions implies each of these. `Unconditional/` proves all of them unconditionally in Lean,
with GRH supplied by the certified proof of L. Alpöge in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).

Literature status: RH-consequence. The conditional theorems are Lamzouri, Li and
Soundararajan's (Theorems 1.1, 1.4, 1.5, Corollaries 1.2, 1.3) and Bach's (the constant `2`).
Unconditionally the best bounds for the least non-residue are of Burgess type,
`q^{1/(4√e)+ε}`. Class-number bounds `h(−q) ≪ √q log log q` and `h(−q) ≫ √q/log log q` under
GRH go back to Littlewood (*On the class-number of the corpus P(√−k)*, Proc. London Math. Soc.
(2) 27 (1928) 358–372), in asymptotic form. Unconditionally the upper bound
`h(−q) ≪ √q log q` is elementary, and the best lower bounds are Siegel's ineffective
`h(−q) ≫_ε q^{1/2−ε}` and an effective bound of order `log q` (Goldfeld, Gross–Zagier, Oesterlé).

What the statements say:

- Theorem 1.1 (1), `LLS.LeastPrimeOutsideSubgroup`: for every `q ≥ 3000` and every proper
  subgroup `H` of `(ℤ/q)ˣ`, some prime `ℓ ∤ q` outside `H` has `ℓ ≤ (log q + B(q))²`, with the
  paper's `A(q)` and `B(q)`.
- Theorem 1.1 (2), `LLS.LeastPrimeOutsideSubgroupRough`: if no prime below `(log q)²` divides
  `q`, some prime `ℓ ≤ (log q)²` lies outside `H`.
- Corollary 1.2, `LLS.LeastNonresidueBelowLogSq`: for every prime `q ≥ 5` there is a quadratic
  non-residue `≤ (log q)²`.
- Corollary 1.3, `LLS.ClassNumberUpperBound` and `LLS.ClassNumberLowerBound`: for the class
  number `h(−q)` of every imaginary quadratic field of discriminant `−q`, `q ≥ 10¹⁰`,
  `h(−q) ≤ (2e^γ/π)√q(log log q − log 2 + 1/2 + 1/log log q)` and
  `h(−q) ≥ (π/(12e^γ))√q(log log q − log 2 + 1/2 + 1/log log q + 14 log log q/log q)⁻¹`.
  The main library takes Dirichlet's class number formula as a hypothesis; `Unconditional/`
  discharges it.
- Theorem 1.4, `LLS.LeastPrimeInCoset`: for every `q ≥ 20000`, every subgroup `H` of `(ℤ/q)ˣ`
  of index `h > 1` and every coset `aH`, the least prime in `aH` is `≤ 10⁹` or
  `≤ ((h − 1) log q + 3(h + 1) + (5/2)(log log q)²)²`.
- Theorem 1.5, `LLS.L1UpperBound` and `LLS.L1LowerBound`: for `χ` primitive mod `q ≥ 10¹⁰`,
  `|L(1,χ)| ≤ 2e^γ(log log q − log 2 + 1/2 + 1/log log q)` and
  `1/|L(1,χ)| ≤ (12e^γ/π²)(log log q − log 2 + 1/2 + 1/log log q + 14 log log q/log q)`.
- Bach's bound, `Ankeny.BachSubgroupBound 2`: for every modulus `q`, every proper subgroup of
  `(ℤ/q)ˣ` omits a unit `≤ 2 log² q`.

Theorems 1.1 and 1.4 need no finite computation over `q` or `h`. Corollary 1.2 checks
`5 ≤ q < 2^12` in the kernel. Bach's constant `2` uses fifteen `native_decide` chunks over
`3 ≤ q < 2^2500` with a proved-sound checker.

```lean
theorem LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    LeastPrimeOutsideSubgroup                                       -- LLS/Thm11/Main.lean
theorem LLS.Thm11.leastPrimeOutsideSubgroupRough_of_GRH
    (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) : LeastPrimeOutsideSubgroupRough
                                                                    -- LLS/Thm11/Rough.lean
theorem LLS.leastNonresidueBelowLogSq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBelowLogSq                                       -- LLS/Nonresidue.lean
theorem LLS.Sharp.classNumberUpperBound_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : LLS.ClassNumberFormula) :
    LLS.ClassNumberUpperBound                                       -- LLS/Sharp/ClassNumber.lean
theorem LLS.Sharp.classNumberLowerBound_of_GRH_of_formula
    (hGRH : DirichletLNonvanishingRightOfHalf) (hCNF : LLS.ClassNumberFormula) :
    LLS.ClassNumberLowerBound
theorem LLS.Thm14.leastPrimeInCoset_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    LeastPrimeInCoset                                               -- LLS/Thm14/Main.lean
theorem LLS.Sharp.l1UpperBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : LLS.L1UpperBound
theorem LLS.Sharp.l1LowerBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : LLS.L1LowerBound
                                                                    -- LLS/Sharp/Final.lean
theorem LLS.bach2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound 2
theorem LLS.leastNonresidue2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound 2
theorem LLS.miller2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement 2
                                                                    -- LLS/Bach2/Main2.lean
```

The targets, transcribed from the paper in `LLS/Statement.lean` (Theorems 1.1, 1.4, 1.5,
Corollary 1.2) and `LLS/Statement2.lean` (Corollary 1.3 and the class number formula):

```lean
noncomputable def LLS.A (q : ℕ) : ℝ :=
  max 0 (2 * log (log q) - 8 / 5 - ∑ p ∈ q.primeFactors, log p / ((p : ℝ) - 1))
noncomputable def LLS.B (q : ℕ) : ℝ :=
  max 0 (2 * log (log q) + 3
    + 2 * (q.primeFactors.card : ℝ) * log (log q) ^ 2 / log q - 2 * A q)
def LLS.LeastPrimeOutsideSubgroup : Prop :=
  ∀ q : ℕ, 3000 ≤ q → ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ hℓ : ℓ.Coprime q,
      ZMod.unitOfCoprime ℓ hℓ ∉ H ∧ (ℓ : ℝ) ≤ (log q + B q) ^ 2
def LLS.LeastPrimeOutsideSubgroupRough : Prop :=
  ∀ q : ℕ, 3000 ≤ q → (∀ p : ℕ, p.Prime → p ∣ q → log q ^ 2 ≤ p) →
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ hℓ : ℓ.Coprime q,
        ZMod.unitOfCoprime ℓ hℓ ∉ H ∧ (ℓ : ℝ) ≤ log q ^ 2
def LLS.LeastNonresidueBelowLogSq : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q →
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ log q ^ 2 ∧ ¬ IsSquare (n : ZMod q)
def LLS.LeastPrimeInCoset : Prop :=
  ∀ q : ℕ, 20000 ≤ q → ∀ H : Subgroup (ZMod q)ˣ, 1 < H.index → ∀ a : (ZMod q)ˣ,
    ∃ p : ℕ, p.Prime ∧ ∃ hp : p.Coprime q, a⁻¹ * ZMod.unitOfCoprime p hp ∈ H ∧
      ((p : ℝ) ≤ 10 ^ 9 ∨
        (p : ℝ) ≤ ((H.index - 1 : ℝ) * log q + 3 * (H.index + 1 : ℝ)
          + 5 / 2 * log (log q) ^ 2) ^ 2)
def LLS.L1UpperBound : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ‖DirichletCharacter.LFunction χ 1‖
      ≤ 2 * exp eulerMascheroniConstant
          * (log (log q) - log 2 + 1 / 2 + 1 / log (log q))
def LLS.L1LowerBound : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    1 / ‖DirichletCharacter.LFunction χ 1‖
      ≤ 12 * exp eulerMascheroniConstant / π ^ 2
          * (log (log q) - log 2 + 1 / 2 + 1 / log (log q) + 14 * log (log q) / log q)
def LLS.ClassNumberUpperBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ)
        ≤ 2 * exp eulerMascheroniConstant / π * √q
            * (log (log q) - log 2 + 1 / 2 + 1 / log (log q))
def LLS.ClassNumberLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      π / (12 * exp eulerMascheroniConstant) * √q
          * (log (log q) - log 2 + 1 / 2 + 1 / log (log q) + 14 * log (log q) / log q)⁻¹
        ≤ classNumber K
def LLS.ClassNumberFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (q : ℕ) [NeZero q], finrank ℚ K = 2 →
    discr K = -q → 4 < q → ∀ χ : DirichletCharacter ℂ q,
      (∀ n : ℕ, Odd n → χ n = ((jacobiSym (-(q : ℤ)) n : ℤ) : ℂ)) →
        χ.LFunction 1 = (π * classNumber K / √q : ℝ)
```

`Ankeny.BachSubgroupBound c`, `Ankeny.LeastNonresidueBound c` and `Miller.MillerStatement c`
are the target definitions of ankeny-grh and miller-grh, used unchanged. "`h(−q)` for a
fundamental discriminant `−q`" is stated as `NumberField.classNumber K` for every number field
`K` of degree 2 with `discr K = −q`, which avoids choosing a model for `ℚ(√−q)`.

### Secondary theorems

The library also proves weaker forms of some of these. The subgroup bound with constant `11/4`
has its own proof (16 `native_decide` chunks for `q < 2^18`), separate from `bach2_of_GRH`. The
`L(1, χ)` and class-number bounds with additive constant `5` (in place of the paper's
`−log 2 + 1/2 + 1/log log q`, and with `2e^γ` in place of `12e^γ/π²` in the `L(1, χ)` lower
bound) are stated in `LLS/L1/Weak.lean`, `LLS/ClassNumber.lean` (odd `q`) and
`LLS/Statement3.lean` (every imaginary quadratic field). Two facts about quadratic fields proved
along the way have no hypothesis at all.

```lean
theorem LLS.bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound (11 / 4)
theorem LLS.leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound (11 / 4)
theorem LLS.miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement (11 / 4)
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

with

```lean
def LLS.L1UpperBoundWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * exp eulerMascheroniConstant * (log (log q) + C)
def LLS.L1LowerBoundWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    1 / ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * exp eulerMascheroniConstant * (log (log q) + C)
def LLS.ClassNumberUpperBoundOddWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, q % 4 = 3 →
    Squarefree q → discr K = -q → (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ) ≤ 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + C)
def LLS.ClassNumberLowerBoundOddWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, q % 4 = 3 →
    Squarefree q → discr K = -q → (10 : ℝ) ^ 10 ≤ q →
      √q / (2 * π * exp eulerMascheroniConstant * (log (log q) + C)) ≤ classNumber K
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

| Result | Theorem | Tier | Hypotheses |
|---|---|---|---|
| Theorem 1.1 | `Thm11.leastPrimeOutsideSubgroup_of_GRH`, `Thm11.leastPrimeOutsideSubgroupRough_of_GRH` | C (U in `Unconditional/`) | GRH |
| Corollary 1.2 | `leastNonresidueBelowLogSq_of_GRH` | C (U in `Unconditional/`) | GRH |
| Corollary 1.3 | `Sharp.classNumberUpperBound_of_GRH_of_formula`, `Sharp.classNumberLowerBound_of_GRH_of_formula` | C + H (U + U₀ in `Unconditional/`) | GRH, `ClassNumberFormula` |
| Theorem 1.4 | `Thm14.leastPrimeInCoset_of_GRH` | C (U in `Unconditional/`) | GRH |
| Theorem 1.5 | `Sharp.l1UpperBound_of_GRH`, `Sharp.l1LowerBound_of_GRH` | C (U in `Unconditional/`) | GRH |
| Bach, constant `2` | `bach2_of_GRH`, `leastNonresidue2_of_GRH`, `miller2_of_GRH` | C (U in `Unconditional/`) | GRH |
| Bach, constant `11/4` | `bach_of_GRH`, `leastNonresidue_of_GRH`, `miller_of_GRH` | C (U in `Unconditional/`) | GRH |
| `L(1, χ)`, constant `5` | `l1UpperBoundWith_of_GRH`, `l1LowerBoundWith_of_GRH` | C (U in `Unconditional/`) | GRH |
| Class numbers, constant `5` | `classNumberUpperBoundOddWith_of_GRH_of_formula`, `classNumberLowerBoundOddWith_of_GRH_of_formula`, `classNumberUpperBoundWith_of_GRH_of_formula`, `classNumberLowerBoundWith_of_GRH_of_formula` | C + H (U + U₀ in `Unconditional/`) | GRH, `ClassNumberFormula` |
| Quadratic fields | `discr_isFundamentalDiscr`, `jacobiChar_isPrimitive`, `kroneckerChar_isPrimitive` | D | none |

GRH is `Erdos985.DirichletLNonvanishingRightOfHalf`, copied word for word in erdos-985 from
`src/Statements.lean` of [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
`ClassNumberFormula` (tier H) is Dirichlet's class number formula for imaginary quadratic
fields, `L(1, χ_{−q}) = π h(−q)/√q` for `q > 4`, in LLS's normalisation (their equation (1.3)),
with the Kronecker symbol characterised by `χ(n) = J(−q | n)` at odd `n`. It is a theorem
(Dirichlet 1839), and Mathlib does not have it at this pin. It is written with Mathlib objects
only, and is the conclusion of riemann-hypothesis's
`GlobalTheory.LFunction_one_and_mean_log_eta` with that repository's `IsKroneckerChar` unfolded.
No other hypothesis appears.

## Axioms

Every headline theorem uses the standard three axioms except Bach's constant `2`, which adds
fifteen `native_decide` axioms. Theorem 1.4 (2026-11-25, `lake env lean Axioms.lean` after
`lake build`):

```
'LLS.Thm14.leastPrimeInCoset_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Theorem 1.1 (2026-11-24, after `lake build LLS`):

```
'LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.Thm11.leastPrimeOutsideSubgroupRough_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Theorem 1.5 and Corollary 1.3 with the paper's constants (2026-11-24, after `lake build LLS`):

```
'LLS.Sharp.l1UpperBound_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.Sharp.l1LowerBound_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.Sharp.classNumberUpperBound_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.Sharp.classNumberLowerBound_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Corollary 1.2, the constant-`11/4` subgroup bound and the forms with constant `5`
(2026-11-24, `lake env lean Axioms.lean` after a clean `lake build`):

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

Class-number bounds for every imaginary quadratic field (2026-11-24,
`lake build LLS.ClassNumberAll`, then `#print axioms`):

```
'LLS.classNumberUpperBoundWith_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.classNumberLowerBoundWith_of_GRH_of_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.discr_isFundamentalDiscr' depends on axioms: [propext, Classical.choice, Quot.sound]
'LLS.kroneckerChar_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Bach's constant `2` (2026-11-24, `lake build`, then `lake env lean Axioms.lean`):

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
of the constant-`11/4` subgroup bound evaluate ankeny-grh's generation checker (`Ankeny.Checker.checkRange 11 4`,
soundness `Ankeny.bach_of_checkRange`, proved in ankeny-grh) on `4 ≤ q < 2^18`: for each `q` a
graph search shows that the units below `⌊(11/4) (⌊log₂ q⌋ log 2)²⌋` generate `(ZMod q)ˣ`. The
sixteen chunks of `2^14` moduli took between 30 s (`C114_0`) and 1884 s (`C114_15`), growing
roughly linearly with `q`; `time lake build` reported 8235 s of user time (31 min wall on 95
cores).

## Proof outline

The full blueprint, with every step as a Lean statement, is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

### Theorem 1.4 (`LLS/Thm14/`)

Let `q ≥ 20000`, `L = log q`, `u = h − 1 ≥ 1`,
`B = uL + 3(u + 2) + (5/2)(log L)²` (the paper's bound), `s = max(31622, ⌊B⌋)`, `X = s²`,
`l = log X`. Since `31622² < 10⁹` and `⌊B⌋² ≤ B²`, a prime `p ≤ X` in `aH` proves the theorem;
suppose there is none.

1. `Orth.lean`: `H̃` = the characters trivial on `H`, `m = |H̃| ≤ h` (they inject into the
   characters of `G/H`), and `Σ_{χ ∈ H̃} χ(a⁻¹)χ(n) = m·1[n ∈ aH]` (Mathlib's duality for finite
   abelian groups). So `m Σ_{n ≤ X, n ∈ aH} Λ(n) log(X/n) = Σ_{χ ∈ H̃} χ(a⁻¹) S(X, χ)`.
2. `Squares.lean`, `PsiUp.lean`: with no prime in `aH`, the left sum only sees `p^k`, `k ≥ 2`;
   writing `p^k = m²` or `m²p` (`m = p^{⌊k/2⌋}`) bounds it by `2ψ₁(s) + 2ψ₁(⌈s/√2⌉)`, and
   `ψ₁(y) = Σ_{n ≤ y} Λ(n) log(y/n) ≤ y + (3/20)√y + 4 log y + 2` under GRH (summation by parts
   from erdos-985's principal sum). This is about `3.42 s` (LLS: `2.2 s`).
3. `Gamma.lean`, `Prim.lean`: for `ψ` primitive mod `f`, absolute-value forms of LLS (4.4)–(4.6):
   `|S(X, ψ)| ≤ (s + 1)Z₂ + |V'| l + ½ l max(log f − 3, l + 2) + 5/4`, where
   `V' = ½ log f + D(1, ψ⁻¹)` (LLS's `ξ'/ξ(0, ψ)`) satisfies
   `max(|V|, |V'|)(1 − 1/100 − 2/10) ≤ ½ log f (0.99) + P₂(100) + 1.5` from the shifted Cesàro
   identity at `x = 100`, so `|V'| ≤ 0.627 log f + 5.93`. The gamma part is real and lies in
   `[−l²/2 − 0.861 l, … + ½]` (even) or `[−1.554 l, … + 5/4]` (odd).
4. `PerChar.lean`: for `χ ≠ 1` mod `q` induced by `ψ`, `|S(X, χ)| ≤ Pc − 2A Re S'(X, χ)` with
   `A = (s + 1)/(1 − 1/s)²` and `Pc = A((1 − 1/X)L − 1.72 + log 2 + O(1/X)) + l²
   + (0.627L + 5.93)l + ½ l max(L − 3, l + 2) + 5/4` (up to the exact `(l − ½ log p)²/2` terms). The primes `p ∣ q`, `p ∤ f` are charged at full price
   (`|ψ(p)| ≤ 1`, nothing assumed about `ψ(p)`) and paid back by `log f ≤ log q − Σ log p`; only
   `2` and `3` keep a positive cost.
5. `Assembly.lean`: `Re S(X, χ₀) ≥ X − 0.15s − 3l − 3 − Σ_{p ∣ q} llp`, and
   `Σ_{χ ∈ H̃, χ ≠ 1} Re S'(X, χ) ≥ −P₂(X)` since `Re Σ_{χ ≠ 1} χ(n) ≥ −1`. Together
   (`main_ineq`): `X − 0.15s − 3l − 3 − Σ llp ≤ m Tup + (m − 1)Pc + 2A P₂(X)`.
6. `Reduce.lean`: with `m ≤ h`, `ω(q) ≤ 10 + L/log 30`, `P₂(X) ≤ l − 1 − γ + 0.25/s + 12/X`,
   this is impossible once
   `s(s − uL) > s(3.42 + 2.391u + 3.127l) + u(1.5l² + 22.93l + 21.25) + 5l² + 9l + 3 + 0.147l²L` (★).
7. `Elim.lean`: if `B < 31622` (`s = 31622`), (★) reduces to `31622 − uL > 68.3 + 2.43u + 0.002L`,
   which follows from `B < 31622` after splitting at `L = 128, 1000, 4000`. If `B ≥ 31622`
   (`B − 1 < s ≤ B`, so `s − uL > 3u + 5 + 2.5(log L)²`), (★) follows from
   `Phi2(u, L, log B) ≤ 0.609u + 1.58 + 2.5(log L)²`: 33 boxes for `u ≤ 10⁵`, `L ≤ 10³⁰`
   (`Cells.lean`, `scripts/emit_thm14.py`, 8 of them outside `B ≥ 31622`) and two tails
   (`Tails.lean`). Smallest slack in (★), in units of `√X`: `68.9` (at `h ≈ 55`,
   `log q ≈ 600`, the smallest `√X` above `31622`); smallest certified box margin: `7.0`.

### Theorem 1.1 (`LLS/Thm11/`)

Let `q ≥ 3000`, `L = log q`,
`ω = ω(q)`, `σ = Σ_{p ∣ q} log p/(p − 1)`, `x = ⌊(L + B(q))²⌋`, `s = √x`, `l = log x`,
`K = (s + 1 + l/2)/(1 − 1/s)²`, `κ = K(1 − 1/x) + l/2`. If every prime `ℓ ≤ x` prime to `q` lay
in `H`, a character `χ ≠ 1` trivial on `H` would be `1` on every `n ≤ x` prime to `q`
(`Common.lean`).

1. `Budget.lean`: the key inequality of step 2 below, with the Cesàro lower bound
   `max(0, Pc − Σ_{p∣q} lcp) − Σ_{p∈R} lcp` (the part over `n` prime to `q` is also `≥ 0`: this
   is the `max(0, ·)` in LLS's `A(q)`), `Pc = l − 1 − γ − 1/(4s) − 12/x` (`x ≥ 100`, from the
   sharp principal sum of `LLS/Sharp/`) or `l − 2`. With `llp ≤ m = (l − ½ log 2)²/2` per prime
   and the primes `p ≥ 5` outside the conductor free (side condition `R5OK`), GRH gives
   `base0(x) + 2K max(0, Pc − σ) − κL − ω m − R(x) ≤ 0`, `R(x)` the cost of `2` and `3` outside
   the conductor.
2. `Elim.lean`: with `ν = s + 1/(2s) > L + B(q)` and `u = 2ω(log L)²/L`: if `σ ≤ 2 log L − 8/5`
   then `2σ + u < ν − L − 6.2 + 2 log L` and, as `ω m ≤ K u`, the left side is at least
   `F₁(x)`, its value at `L = ν` (it decreases in `L`); otherwise `A(q) = 0`,
   `u < ν − L − 3 − 2 log L`, and with `μ = 2mν/l² ≥ m L/(2(log L)²)` the left side is at least
   a function of `L` concave on `[8, ν − 3 − 2 log 8]`, so at least
   `min(F₂(x, 8), F₂(x, ν − 3 − 2 log 8))`. `ω m ≤ μ u` uses that `t/(log t)²` increases on
   `t ≥ 8`.
3. `NumCore.lean`: with `δ = K − s = s(s(3 + l/2) − 1)/(s − 1)²` and
   `ε = κ − s = (3s + 1)/(s − 1) + ls/(s − 1)`, `F₁ = s·Q + δ·W + V` with `Q`, `W`, `V` of size
   `O(1)`, `O(l)`, `O(l²)` (`F1_eq`), so `x − κν` cancels exactly; likewise `F₂` (`F2a_eq`,
   `F2b_eq`). On a box `X_a ≤ x ≤ X_b` every piece is bounded by monotonicity (`F1_ge`,
   `F2a_ge`, `F2b_ge`, `R5_of`).
4. `Boxes.lean` (59 boxes, `scripts/emit_thm11.py`) covers `64 ≤ x < 10^16`; `Tail.lean` covers
   `x ≥ 10^16` from `log x ≤ 8x^{1/8}`, so `l² ≤ s/100`. Smallest margins: `F₁ ≥ 0.776 s`
   (at `x = 99`), `F₂(x, 8) ≥ 0.93 s`, `F₂(x, ν − 3 − 2 log 8) ≥ 0.208 s` (at `x ≈ 15000`); on
   the boxes the smallest certified lower bound is `0.1` (`F₂`, `401 ≤ x < 501`).
5. Part 2 (`Rough.lean`): when every prime `p ∣ q` is `≥ (log q)² ≥ x`, all losses vanish
   (`llp x p = lcp x p = 0` for `p ≥ x`), and the loss-free budget `Φ₁` of the prime case
   applies. `GoodP 1 q` (some `64 ≤ x ≤ (log q)²` with `Φ₁ > 0`) holds for `3000 ≤ q < 4096`
   by four new certified intervals (`IntervalsR.lean`, `scripts/emit_rough.py`) and beyond by
   the existing ones.

### Theorem 1.5 and Corollary 1.3 (`LLS/Sharp/`)

Take `x = ⌊log² q/4⌋` (so `x ≥ 132`),
`l = log x`, `y = 1/√x`, `𝔞` the parity of `χ`.

1. `Assembly.lean`: LLS §5 exactly. `Re D(1,χ⁻¹) = Re D(1,χ)` (`AssemblyAux/Conj.lean`), so the
   zero sum is `Z = log q + 2 Re D(1,χ)`, and Lemma 2.3 becomes
   `Z(1−y)² ≤ (1−1/x) log q − 2 Re S'(χ) + 2Γ ≤ Z(1+y)²` with the gamma part `Γ` bounded per
   parity (`AssemblyAux/Gamma.lean`). Eliminating `Z` from Lemma 2.5 gives the paper's bound in
   terms of `l1Sum1 x`, `P2sum x` and (lower bound) `W(χ,x) = Σ Λ(n)χ(n)(1/(n log n) − 1/(x log x))`.
2. `Principal.lean`: `P2sum x ≤ log x − 1 − γ + 1/(4√x) + 12/x` and
   `l1Sum1 x ≤ log log x + γ − 1 + γ/log x + (0.6/√x + 29/x)/log x` (LLS Lemmas 2.4 and 2.6 in
   the form used), from `ψ₁(t) = ∫₀ᵗ ψ` with `|ψ₁(t) − t²/2| ≤ t^{3/2}/20 + 4t` under GRH. The
   constants come from `−ζ'/ζ(s) − 1/(s−1) → −γ` (Mathlib's `riemannZeta₁`) and a Mellin
   transform of `ψ₁` (`Principal/Laurent.lean`, `Mellin.lean`), and from Mertens' theorem
   (robin-rh). The representations are FTC with right derivatives (`Principal/Repr.lean`).
3. `Lemma51.lean`: a form of LLS Lemma 5.1, prime by prime with `Re log(1 − χ(p)/p)⁻¹ ≥
   −log(1 + 1/p)`: `Re W ≥ −(l1Sum1 + P2sum/l) + Σ_{p∈S} −log(1 − p⁻²) − (10/3)|S|/x` for any set
   `S` of primes `p ≤ √x`, and with all of them `≥ … + log(π²/6) − 10/(3√x) − 4/(3(√x − 1))`.
4. `NumBasic.lean`, `NumU.lean`, `NumL.lean`, `Final.lean`: both bounds reduce to
   `u + 2u² + y·Q(u,y)` with `u = 1/l` against `log(1 + V)`, `V = u + 4u²/(1 + 2u log 2)` (upper)
   and `log(1 + V + 7(1 + 2u log 2)y/(1 + y²/2))` (lower), using `log(1+w) ≥ 2w/(2+w)`. Upper:
   `Q ≤ −1/2` on one box. Lower: the primes `{2,3,5,7,11}` and ten boxes in `x` for
   `x ≤ 22100`, all primes and one box beyond. Smallest numerical margin: `0.00057`
   (`177 ≤ x ≤ 247`).
5. `ClassNumber.lean`: Corollary 1.3 from Theorem 1.5 and the class number formula, for every
   imaginary quadratic field.

### The shared analytic core, Corollary 1.2 and the secondary theorems

Steps 1 and 2 are the explicit formulas and the key inequality (LLS §3). Steps 3 to 5
prove Corollary 1.2 and the constant-`11/4` subgroup bound; steps 6 to 8 prove the forms with
constant `5`.

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
### Bach's constant `2` (`LLS/Bach2/`, `LLSCheck.lean`)

With the constants formalised here, the analytic inequality alone reaches `2` uniformly in `q`
only from about `q ≈ 2^27`: moduli divisible by many small primes are the worst case, and the
budget uniform in `q` (primes `p < 53` listed, `β log p` for the rest) turns positive there
(`2^38.6` with a cut-off at `17` and the Cesàro bound `log x − 2`). Three things close the
range below. The Cesàro sum `Σ_{n ≤ x} Λ(n)/n (1 − n/x)` is summed exactly, with certified lower
bounds for `log p`, for every `x < 2000`; its true value is about `log x − 1 − γ`, and the gain
`0.42 · 2K ≈ 0.85 √x` is the largest single term. Below `2^27` the budget is evaluated for each
modulus with its own prime factors (`costQ`, the cost `W_p` of each prime `p ≤ x` dividing `q`),
and that is positive for all but about 7,500 moduli `q < 2^26` (their sum is about `4.4·10^9`).
Those moduli are checked by ankeny-grh's generation search with `x = ⌊2 La²⌋`.

1. `keyP` is the key inequality of step 2 of the shared core with any lower bound `Pc` for the
   Cesàro sum; `budgetQ_nonpos` charges each prime `p ≤ x` dividing `q` its cost `W_p(x)`, and
   `budgetU_nonpos` lists the primes `p < 53` and charges the others `β log p`,
   `β = (log x)²/(2 log 53) + 2K/52`.
2. `LLSCheck.checkChunk m w lo hi` (core Lean, exact `Rat` arithmetic) splits `[lo, hi)` into
   blocks `[a, a + a/2^w)`, takes `x = ⌊2 La²⌋` with `La ≤ log a` (from `2^k ≤ a^m`), bounds
   `√x`, `log x`, `log p` and `log b`, computes `Pc` as the exact Cesàro sum with certified
   lower bounds for `Λ(n)` (for `x < 2000`; else `log x − 2`), and accepts the block if the
   uniform budget is positive. Otherwise it tries each `q` with its own primes (integer form
   scaled by `2^32`), and failing that runs `Ankeny.Checker.checkGen q x`.
3. `checkChunk_sound` proves that a `true` result gives, for every `q` in the range, either
   generation of `(ZMod q)ˣ` by the units `≤ x ≤ 2 log² q` or a positive budget;
   `bach_of_good2` turns either into the bound under GRH.
4. 15 chunks cover `3 ≤ q < 2^2500` (`LLS/Compute2/`); `goodQ_tail2` covers `q ≥ 2^2500`
   with the uniform budget `Φ` of step 3 of the shared core (`x = ⌊2L²⌋`, `z = x^{1/8} ≥ 7`).

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
| `LLS/Sharp/Defs.lean`, `Assembly.lean`, `AssemblyAux/*.lean` | LLS §5 assembly, `Re D(1,χ⁻¹) = Re D(1,χ)`, gamma parts per parity |
| `LLS/Sharp/Principal.lean`, `Principal/*.lean` | Sharp principal sums (Laurent expansion, Mellin transform of `ψ₁`) |
| `LLS/Sharp/Lemma51.lean`, `Lemma51Aux/*.lean` | Form of LLS Lemma 5.1 |
| `LLS/Sharp/NumBasic.lean`, `NumU.lean`, `NumL.lean` | One-variable inequalities |
| `LLS/Sharp/Final.lean`, `ClassNumber.lean` | Theorem 1.5 and Corollary 1.3 with the paper's constants |
| `LLS/Thm11/Common.lean`, `Rough.lean`, `IntervalsR.lean` | Losses at primes `p ≥ x`, the character from `H`; Theorem 1.1 (2) |
| `LLS/Thm11/Budget.lean`, `Elim.lean` | The budget with `max(0, ·)`; eliminating `ω(q)` and `σ(q)` |
| `LLS/Thm11/NumCore.lean`, `Boxes.lean`, `Tail.lean`, `Main.lean` | The one-variable bounds; Theorem 1.1 (1) |
| `LLS/Thm14/Orth.lean` | Characters trivial on `H`: `\|H̃\| ≤ [G : H]`, the coset indicator |
| `LLS/Thm14/PsiUp.lean`, `Squares.lean` | `ψ₁(y) ≤ y + (3/20)√y + 4 log y + 2`; prime powers `p^k ≤ s²`, `k ≥ 2` |
| `LLS/Thm14/Gamma.lean`, `Prim.lean` | Absolute-value bounds for a primitive character (gamma parts, `\|D(1, ψ)\|`, `\|S(X, ψ)\|`) |
| `LLS/Thm14/PerChar.lean`, `Assembly.lean` | One non-principal character; the main inequality |
| `LLS/Thm14/Reduce.lean`, `CellCore.lean`, `Cells.lean`, `Tails.lean`, `Elim.lean` | Elimination in `h`, `log q`, `X` |
| `LLS/Thm14/Main.lean` | Theorem 1.4 |
| `scripts/*.py` | Generators for the certificates and the sizing computations |

## Constants inside the proofs

The statements carry the paper's constants; some intermediate estimates in the proofs are
weaker than the paper's, and the margins absorb them.

* Theorem 1.1. The principal sum is `x − 0.15√x − 3 log x − 3` (LLS Lemma 2.1:
  `x − 0.046√x − 1.84 log x − 1`), and the gamma terms are bounded for both parities at once.
  The margin stays large because the Cesàro sum is kept as `log x − 1 − γ − O(x^{−1/2})` (LLS
  use `log X − 8/5` with `X ≥ (log q)²`, losing `2 log(√X/log q)`), the cancellation `x − κν` is
  exact, and the primes `p ≥ 5` outside the conductor cost nothing. Over all `q` the worst case
  found (in Python, prime sets of the first primes) leaves `0.99√x` at `log q ≈ 180`. As
  written, the paper's proof bounds `Σ Λ(n) χ̃(n)/n (1 − n/X)` as if `χ̃(p) = 1` for primes
  `p ∣ q`, `p ∤ q̃`, where the value of `χ̃(p)` is unknown. Here those primes are charged twice
  and absorbed through `log f ≤ log q − Σ log p`; only `2` and `3` keep a positive cost, which
  the margin covers.
* Theorem 1.4. The principal sum is `X − 0.15√X − 3 log X − 3` (LLS: `X − √X/20 − …`); the
  squares `p^{2k}` and the odd powers `p^{2k+1}` are bounded by
  `2ψ₁(s) + 2ψ₁(⌈s/√2⌉) ≈ 3.42√X` (LLS: `2.2√X`), using no Chebyshev-type input beyond GRH;
  `|ξ'/ξ(0, χ̃)| ≤ 0.627 log q̃ + 5.93` (LLS (4.6): `(2/3) log(q/π) + 4`); and
  `ω(q) ≤ 10 + log q/log 30` replaces `2^{ω(q)} ≤ q^{3/7}`. In return the cancellation of
  `(h − 1) log q · √X` is exact (LLS round `√X + 19/6`), the gamma parts are bounded per parity,
  and the per-character constant is `A(−1.72 + log 2)` with `A ≈ √X + 3`. As in Theorem 1.1,
  the paper's proof uses
  `Re Σ Λ(n)χ̃(n)/n (1 − n/X) ≥ Re Σ Λ(n)χ(n)/n (1 − n/X) − Σ_{p ∣ q/q̃} log p/(p − 1)`, which
  holds because it bounds the difference by absolute values; here every such step uses only
  `|χ̃(p)| ≤ 1` at primes `p ∣ q`, `p ∤ q̃`.
* Theorem 1.5. The paper's own chain of simplified inequalities leaves a margin of about
  `0.0006` (in `log`) at `q = 10¹⁰`. The proof here keeps the exact elimination of `|Re B(χ)|`,
  the factors `(1 ± 1/√x)^{−2}` and the gamma terms per parity, which leaves margins (in `log`,
  before the Padé bound for `log`) of `0.127`/`0.044` (upper/lower) at `q = 10¹⁰`,
  `0.121`/`0.087` at `10¹²`, `0.090`/`0.109` at `10²⁰`, `0.026`/`0.025` at `10¹⁰⁰`, and about
  `1.5/l²` (`l = 2 log log q − log 4`) as `q → ∞`. The versions of LLS Lemmas 2.4 and 2.6 here
  have error terms `1/(4√x) + 12/x` and `(0.6/√x + 29/x)/log x` (LLS: `2|B|/√x` with
  `|B| = 0.023…`), and Lemma 5.1 compares prime by prime with `−log(1 + 1/p)` instead of the
  paper's alternating extremal sum (error `10/(3x)` per prime).
* Bach's constant `2`. The analytic part is LLS's argument with weaker constants than the
  paper's: the principal sum is bounded by summation by parts (`x − 0.15√x − 3 log x − 3`
  against LLS Lemma 2.1's `x − 0.046√x − 1.84 log x − 1`), and a prime factor `p ≥ 53` of `q`
  is charged `β log p`. The finite check described under the proof outline covers the range
  where this loses.

## Deviations from the literature

None for the statements. Theorems 1.1, 1.4 and 1.5 and Corollaries 1.2 and 1.3 are proved
with the paper's constants and thresholds, and the subgroup bound with Bach's constant `2`.
Corollary 1.3 takes Dirichlet's class number formula as a hypothesis in the main library
(tier H), and `Unconditional/` discharges it.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`; also requires ankeny-grh
`129ad57`, miller-grh `b484d44` and robin-rh `dfa8d63`).

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

Theorem 1.4 alone: `lake build LLS.Thm14.Main` (from the warm cache each module of
`LLS/Thm14/` is under a minute: `Cells` about 20 s, `Reduce` 35 s, `Tails` 30 s; no
`native_decide`).

Theorem 1.1 alone: `lake build LLS.Thm11.Main` (from the warm cache: `IntervalsR` 93 s,
`NumCore` 22 s, `Boxes` 15 s, `Tail` 22 s, the rest under 30 s each; no `native_decide`).

Bach's constant `2` alone: `lake build LLS.Bach2.Main2`. Its fifteen `native_decide` chunks take
about 22 CPU-minutes on a 95-core box with warm caches (the slowest, `C2_10`, 334 s). The sixteen
chunks for `11/4` take about 2.3 CPU-hours (the slowest, `C114_15`, 1884 s). The certified
intervals take 141 s (`Intervals114`) and 77 s (`IntervalsP`); every other module builds in
under a minute.

## Unconditional version

`Unconditional/LLSUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the GRH hypothesis in one line. These are the statements above
with no hypothesis left. The first eleven rows are the headline results; the rest are the
secondary theorems and the class number formula.

| Theorem | Statement | Axioms |
|---|---|---|
| `leastPrimeOutsideSubgroup_unconditional` | `LLS.LeastPrimeOutsideSubgroup` | standard three |
| `leastPrimeOutsideSubgroupRough_unconditional` | `LLS.LeastPrimeOutsideSubgroupRough` | standard three |
| `leastNonresidueBelowLogSq_unconditional` | `LLS.LeastNonresidueBelowLogSq` | standard three |
| `classNumberUpperBound_unconditional` | `LLS.ClassNumberUpperBound` | standard three |
| `classNumberLowerBound_unconditional` | `LLS.ClassNumberLowerBound` | standard three |
| `leastPrimeInCoset_unconditional` | `LLS.LeastPrimeInCoset` | standard three |
| `l1UpperBound_unconditional` | `LLS.L1UpperBound` | standard three |
| `l1LowerBound_unconditional` | `LLS.L1LowerBound` | standard three |
| `bach2_unconditional` | `Ankeny.BachSubgroupBound 2` | standard three + 15 `native_decide` |
| `leastNonresidue2_unconditional` | `Ankeny.LeastNonresidueBound 2` | standard three + 15 `native_decide` |
| `miller2_unconditional` | `Miller.MillerStatement 2` | standard three + 15 `native_decide` |
| `classNumberFormula` (U₀) | `LLS.ClassNumberFormula` | standard three |
| `bach_unconditional` | `Ankeny.BachSubgroupBound (11 / 4)` | standard three + 16 `native_decide` |
| `leastNonresidue_unconditional` | `Ankeny.LeastNonresidueBound (11 / 4)` | standard three + 16 `native_decide` |
| `miller_unconditional` | `Miller.MillerStatement (11 / 4)` | standard three + 16 `native_decide` |
| `l1UpperBoundWith_unconditional` | `LLS.L1UpperBoundWith 5` | standard three |
| `l1LowerBoundWith_unconditional` | `LLS.L1LowerBoundWith 5` | standard three |
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
(2026-11-24, at `9e0adb8`, 36 min wall, most of it importing the riemann-hypothesis modules):

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

The rerun on branch `round7` (6 min wall) printed the same lines for all eleven theorems above
and:

```
'bach2_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LLS.chunk2_ok_0._native.native_decide.ax_1_1,
 …,
 LLS.chunk2_ok_9._native.native_decide.ax_1_1]
'leastNonresidue2_unconditional' depends on axioms: (the same eighteen)
'miller2_unconditional' depends on axioms: (the same eighteen)
```

The fifteen elided `chunk2` lines are `LLS.chunk2_ok_i._native.native_decide.ax_1_1` for every
`0 ≤ i ≤ 14`, exactly as in the main-library output above.

The rerun on branch `round9` (about 4 min wall) printed the same lines for all eighteen theorems
above and:

```
'leastPrimeOutsideSubgroup_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'leastPrimeOutsideSubgroupRough_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The rerun on branch `round10` (2026-11-25) printed the same lines for all twenty theorems above
and:

```
'leastPrimeInCoset_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM; raise the open-file limit first (Linux:
`sudo prlimit --pid $$ --nofile=2000000:2000000`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* The analytic toolkit (Hadamard factorisation, Perron/Mellin kernels, the Cesàro explicit
  formula, digamma series) is the [erdos-985](../erdos-985/) library,
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
