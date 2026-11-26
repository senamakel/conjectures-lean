# Conjecture 5.6 of Gawron–Miska–Ulas is false

Let `b_m(n)` be the coefficient of `x^n` in `∏_{i≥0} (1 − x^{2^i})^{−m}`, the number of
representations of `n` as a sum of powers of `2` in which each summand has one of `m` colours.
Gawron, Miska and Ulas (arXiv:1703.01955 v1, 2017; Monatsh. Math. 185 (2018) 307–360) conjectured
(Conjecture 5.6) that for every positive integer `m`, every `n ∈ ℕ` and every `k ≥ m + 2`,

`b_{2^m−1}(2^{k+1}n) ≡ b_{2^m−1}(2^{k−1}n) (mod 2^{4⌊(k+1)/2⌋−2})`.

This package proves in Lean that the conjecture is false: at `m = 1`, `k = 3`, `n = 1` it asks
`64 ∣ b₁(16) − b₁(4) = 36 − 4 = 32`. The headline theorem uses Lean's three standard axioms only;
the values are checked by the kernel through a checker whose soundness is proved. It also fails
at `m = 3`, `4`, `5` (kernel-checked) and `m = 6` (two `native_decide` evaluations). Literature
label: *new* (refutation lane, route **e**: a finite counterexample found by computation). The
`m = 1` failures are a corollary of Churchhouse's congruence, proved by Rødseth (1970) and Gupta
(1971–72), so only the `m ≥ 3` failures are a new observation. This is a minor correction to one
conjecture in a long paper, not a major result.

## Headline theorems

```lean
noncomputable def GMU.geomPow2 (i : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if 2 ^ i ∣ n then 1 else 0          -- ∑_j X^{2^i j} = (1 − X^{2^i})⁻¹

noncomputable def GMU.truncatedSeries (m N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, geomPow2 i ^ m

noncomputable def GMU.b (m n : ℕ) : ℤ :=
  PowerSeries.coeff n (truncatedSeries m (n + 1))

def GMU.GMUConjecture56 : Prop :=
  ∀ m : ℕ, 0 < m → ∀ n k : ℕ, m + 2 ≤ k →
    b (2 ^ m - 1) (2 ^ (k + 1) * n) ≡ b (2 ^ m - 1) (2 ^ (k - 1) * n)
      [ZMOD 2 ^ (4 * ((k + 1) / 2) - 2)]

theorem GMU.gmu_conjecture_5_6_false : ¬ GMUConjecture56

theorem GMU.gmu_conjecture_5_6_fails_at_m1_k3 :
    ¬ b (2 ^ 1 - 1) (2 ^ (3 + 1) * 1) ≡ b (2 ^ 1 - 1) (2 ^ (3 - 1) * 1)
      [ZMOD 2 ^ (4 * ((3 + 1) / 2) - 2)]
theorem GMU.gmu_conjecture_5_6_fails_at_m1_k5 :   -- b₁(64) − b₁(16) = 1792 = 2^8 · 7, mod 2^10
    ¬ b (2 ^ 1 - 1) (2 ^ (5 + 1) * 1) ≡ b (2 ^ 1 - 1) (2 ^ (5 - 1) * 1)
      [ZMOD 2 ^ (4 * ((5 + 1) / 2) - 2)]
theorem GMU.gmu_conjecture_5_6_fails_at_m3 :      -- b₇(64) − b₇(16), mod 2^10
    ¬ b (2 ^ 3 - 1) (2 ^ (5 + 1) * 1) ≡ b (2 ^ 3 - 1) (2 ^ (5 - 1) * 1)
      [ZMOD 2 ^ (4 * ((5 + 1) / 2) - 2)]
theorem GMU.gmu_conjecture_5_6_fails_at_m4 :      -- b₁₅(128) − b₁₅(32), mod 2^10
    ¬ b (2 ^ 4 - 1) (2 ^ (6 + 1) * 1) ≡ b (2 ^ 4 - 1) (2 ^ (6 - 1) * 1)
      [ZMOD 2 ^ (4 * ((6 + 1) / 2) - 2)]
theorem GMU.gmu_conjecture_5_6_fails_at_m5 :      -- b₃₁(256) − b₃₁(64), mod 2^14
    ¬ b (2 ^ 5 - 1) (2 ^ (7 + 1) * 1) ≡ b (2 ^ 5 - 1) (2 ^ (7 - 1) * 1)
      [ZMOD 2 ^ (4 * ((7 + 1) / 2) - 2)]
theorem GMU.gmu_conjecture_5_6_fails_at_m6 :      -- b₆₃(512) − b₆₃(128), mod 2^14
    ¬ b (2 ^ 6 - 1) (2 ^ (8 + 1) * 1) ≡ b (2 ^ 6 - 1) (2 ^ (8 - 1) * 1)
      [ZMOD 2 ^ (4 * ((8 + 1) / 2) - 2)]

theorem GMU.gmu_conjecture_5_6_fails_for_m_1_3_4_5 :
    ∀ m ∈ ({1, 3, 4, 5} : Finset ℕ), ∃ n k : ℕ, m + 2 ≤ k ∧
      ¬ b (2 ^ m - 1) (2 ^ (k + 1) * n) ≡ b (2 ^ m - 1) (2 ^ (k - 1) * n)
        [ZMOD 2 ^ (4 * ((k + 1) / 2) - 2)]
```

The witnesses, all at `n = 1`:

| `m` | `k` | modulus | difference | its 2-adic valuation |
| :---: | :---: | :---: | :--- | :---: |
| 1 | 3 | `2^6` | `b₁(16) − b₁(4) = 36 − 4 = 32` | 5 |
| 1 | 5 | `2^10` | `b₁(64) − b₁(16) = 1828 − 36 = 1792` | 8 |
| 3 | 5 | `2^10` | `b₇(64) − b₇(16) = 346264420529188 − 5586084 = 346264414943104` | 7 |
| 4 | 6 | `2^10` | `b₁₅(128) − b₁₅(32)` (32 digits) | 8 |
| 5 | 7 | `2^14` | `b₃₁(256) − b₃₁(64)` (67 digits) | 9 |
| 6 | 8 | `2^14` | `b₆₃(512) − b₆₃(128)` (136 digits) | 10 |

The full values are in `GMUBinaryPartitions/Values.lean` and `GMUBinaryPartitions/Native.lean`.

## Tier and provenance

All theorems are **tier D**: closed statements with no hypotheses, proved from Mathlib alone.

**Where the statement was read.** The arXiv v1 source of arXiv:1703.01955 (the only version on
arXiv; its source file is `GMU_MOFM_Revision_II.tex`), Section 5, `\begin{conj}\label{cong:powerof2-1}`:

> Let `m` be a fixed positive integer. Then for each `n∈ℕ` and `k≥m+2` the following congruence
> holds: `b_{2^m−1}(2^{k+1}n) ≡ b_{2^m−1}(2^{k−1}n) (mod 2^{4⌊(k+1)/2⌋−2})`.

The definition is in Section 4 of the same source: `b_m(n) := f_n(−m)`, where
`∏_{n≥0}(1−x^{2^n})^t = ∑ f_n(t) x^n`, that is, `H_m(x) = F(x)^{−m} = ∑ b_m(n) x^n`. In the paper
`ℕ` contains `0` (`b_m(0) = 1`; positive integers are `ℕ₊`), so `n` ranges over Lean's `ℕ`. The
journal text (Monatsh. Math. 185 (2018)) was **not** read; we have not checked that Conjecture
5.6 appears there in the same form or with the same number.

**How the statement is encoded.** No formal-conjectures statement exists, so
`GMUBinaryPartitions/Statement.lean` is ours. `⌊(k+1)/2⌋` is `(k + 1) / 2` in `ℕ`; since
`k ≥ m + 2 ≥ 3`, neither `k − 1` nor `4⌊(k+1)/2⌋ − 2` truncates. The congruence is
`Int.ModEq`. `b m n` is the coefficient of `X^n` in `∏_{i ≤ n} (∑_j X^{2^i j})^m` in `ℤ⟦X⟧`; three
lemmas in `GMUBinaryPartitions/Series.lean` tie it to the paper's object:

* `one_sub_mul_geomPow2 : (1 - X ^ 2 ^ i) * geomPow2 i = 1`;
* `coeff_truncatedSeries : n < 2 ^ N → coeff n (truncatedSeries m N) = b m n`
  (the factors with `2^i > n` do not change the coefficient);
* `b_eq_coeff_of_mul_eq_one : n < 2 ^ N → (∏ i ∈ range N, (1 - X ^ 2 ^ i) ^ m) * S = 1 →
  coeff n S = b m n`, so `b m n` is the `n`-th coefficient of the inverse of
  `∏_{i<N} (1 − X^{2^i})^m` for every large enough `N`.

## Axioms

```
'GMU.gmu_conjecture_5_6_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_at_m1_k3' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_at_m1_k5' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_at_m3' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_at_m4' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_at_m5' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_for_m_1_3_4_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.gmu_conjecture_5_6_fails_at_m6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 GMU.b_63_128._native.native_decide.ax_1_1,
 GMU.b_63_512._native.native_decide.ax_1_1]
'GMU.bList_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'GMU.b_eq_coeff_of_mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The values for `m ≤ 5` (the `2^m − 1 ≤ 31` colour counts) are checked by `decide +kernel`: the
kernel itself reduces the checker `bList` on natural-number lists, with its GMP arithmetic on
literals. There is no `native_decide` on the path to the headline or to the `m = 1, 3, 4, 5`
theorems. `gmu_conjecture_5_6_fails_at_m6` uses two `native_decide` calls, one per value
(`b₆₃(128)` and `b₆₃(512)`); each evaluates the same checker `bList` in compiled code (the whole
`Native` module builds in 12 s), and the checker's soundness is `bList_sound`, proved from the standard three. The kernel
reduction of `b₆₃(512)` ran for more than six minutes and 8 GB before we stopped it, which is why
this one theorem uses `native_decide`. Reproduce with `lake env lean scripts/Axioms.lean`.

## Proof outline

1. **Series** (`GMUBinaryPartitions/Series.lean`). `∑_j X^{2^i j}` inverts `1 − X^{2^i}`, and is
   `≡ 1 (mod X^{2^i})`, so the coefficient of `X^n` in the finite product is the same for every
   `N` with `n < 2^N` (`coeff_truncatedSeries`).
2. **Checker** (`GMUBinaryPartitions/Check.lean`). Multiplying by `∑_j X^{d j}` is the transform
   `r(n) = l(n) + r(n − d)`. `stepAux` carries it out on a list in blocks of `d` entries
   (`get0_stepAux` proves that it returns the unique solution of the recursion); `iterPow` and
   `coeffList` apply it `m` times for each `i < N`, starting from the list of `1`. `bList_sound`:
   entry `n ≤ L` of `bList m N L` is `b m n` when `L < 2^N`.
3. **Values** (`GMUBinaryPartitions/Values.lean`, `Native.lean`). The values in the table above,
   one checker run each.
4. **Assembly** (`GMUBinaryPartitions/Main.lean`). Each `…_fails_at_…` theorem reduces its
   instance to the explicit values and the residues mod `2^e` (`norm_num`). The headline applies
   the conjecture to `m = 1`, `n = 1`, `k = 3`.

## Relation to the literature

**`m = 1` is a corollary of a classical theorem.** For the binary partition function
`b = b₁`, Churchhouse conjectured (1969), and Rødseth (1970) and Gupta (1971–72) proved, that for
odd `n` and `r ≥ 1`, `b(2^{r+2}n) − b(2^r n)` is divisible by exactly `2^{⌊3r/2⌋+2}`, and by no
higher power. With `r = k − 1` the exponent `⌊3(k−1)/2⌋ + 2` is below the conjectured
`4⌊(k+1)/2⌋ − 2` for `k = 3` and every `k ≥ 5`, so Conjecture 5.6 already fails at `m = 1` on the
strength of that theorem. (The exactness statement is as cited in Ulas–Żmija, arXiv:1904.03398,
Section 6; we did not re-read Rødseth's or Gupta's papers.) In our computation `k = 4` is the only
`k ≤ 8` at which the `m = 1` instance holds for `n = 1`.

**`m ≥ 3`.** We know of no classical result covering the failures at `m = 3, 4, 5, 6`
(`b₇, b₁₅, b₃₁, b₆₃`); this is the new observation. Outside Lean (Python, exact integers), the
`n = 1` instance fails at `m = 3` for `k ∈ {5, 6, 7, 9}` and holds at `k ∈ {8, 10}`; at `m = 7`
(`b₁₂₇`) it fails for `k ∈ {9, 10, 11}`.

**`m = 2` (`b₃`) holds in our computations.** A C program computing `b₃(n) mod 2^64` for every
`n < 2^26` found no failure for any `4 ≤ k ≤ 24` and any `n` with `2^{k+1} n < 2^26` (about
4.2 million instances, `n = 0` included). Nothing about `m = 2` is proved here.

**Prior art.** Searched on 2026-11-26 for an erratum, refutation or proof of Conjecture 5.6: the
citing papers Ulas–Żmija arXiv:1809.04628 and arXiv:1904.03398, Sobolewski–Ulas arXiv:2211.16622,
Yu–Lei–Hong arXiv:2606.25825 (which proves GMU's unboundedness conjecture 3.9), Żmija
arXiv:2403.07477 and arXiv:2603.12401; a web search on the conjecture's wording; GitHub code search
for `1703.01955` and for "Gawron Miska Ulas" (the hits are 1337isnot1337/solved-conjectures entries
on GMU's Conjectures 5.2 and 5.8, and OEIS mirrors); and the 1337isnot1337/solved-conjectures
results list. None mentions Conjecture 5.6 being false. Two related items concern a different
sequence: Ulas–Żmija's Conjecture 6.1 (arXiv:1904.03398) on `ν₂(c_m(4n) − c_m(n))`, where
`∑ c_m(n) x^n = (1−x)^{−m} ∏_{i≥0} (1−x^{2^i})^{−m}`, and Myeongjin Kang's MathDB preprint 2611.00038
on that conjecture (abstract read only). Neither is about `b_{2^m−1}`. The journal version and
MathSciNet/zbMATH reviews of GMU were not checked.

## Layout

| File | Content |
|---|---|
| `GMUBinaryPartitions/Statement.lean` | `geomPow2`, `truncatedSeries`, `b`, `GMUConjecture56` |
| `GMUBinaryPartitions/Series.lean` | inverse of `1 − X^{2^i}`, truncation independence, `b` as a coefficient of the inverse |
| `GMUBinaryPartitions/Check.lean` | list checker `bList` and its soundness `bList_sound` |
| `GMUBinaryPartitions/Values.lean` | values for `m ≤ 5` by `decide +kernel` |
| `GMUBinaryPartitions/Main.lean` | the `…_fails_at_…` theorems and the headline |
| `GMUBinaryPartitions/Native.lean` | the `m = 6` witness, two `native_decide` |
| `scripts/Axioms.lean` | `#print axioms` for every headline theorem |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

```
lake build GMUBinaryPartitions
lake env lean scripts/Axioms.lean
```

A clean build of the package on top of the Mathlib cache took 3 min 50 s wall (59 s user, 76 s
system CPU) on a box with load average about 120, with a peak resident set of 9.1 GB.
`GMUBinaryPartitions.Values` (the kernel evaluations, `b₃₁(256)` the largest) took 128 s and
dominates; every other module takes under 30 s, `Native` 12 s.

## This result needs no RH

The proof imports nothing beyond Mathlib, so there is no `Unconditional/` version.

## Credits

Built by the OpenHuman agents. No files are vendored.
