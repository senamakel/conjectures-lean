# A prime between `x^α` and `(x+1)^α` for every real `α ≥ 3` under RH in Lean

This project proves in Lean that for every real exponent `α ≥ 3` and every real `x ≥ 1` there is a
prime `p` with `x^α < p < (x+1)^α`, and in particular that for every integer `m ≥ 3` and every
`n ≥ 1` there is a prime strictly between `n^m` and `(n+1)^m`. The main library proves the
implication from RH; `Unconditional/` proves both statements outright, with RH supplied by the
certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).

The statement is the exponent range `α = 2 + δ ≥ 3` of Chamberland and Straub, *Weakening the
Legendre conjecture*, arXiv:2602.22502 (2026), Theorem 1.2(a), which assumes RH and takes real
`x ≥ 1` and `δ ≥ 1/4` (numbering read from the arXiv listing, not re-checked in the full text).
The proof here is the short reduction to Caldwell–Cheng's Lemma 5, a prime between consecutive
cubes, already proved in [`mills-rh`](../mills-rh/).

**Literature status.** *RH-consequence.* Without RH, a prime between `n^m` and `(n+1)^m` for all
`n ≥ 1` is known for integer `m ≥ 90` (Cully-Hugill and Johnston, *Funct. Approx.* 73 (2025),
Theorem 1.4, read on arXiv:2402.04272), and a report of `m ≥ 86` (Lee, arXiv:2602.14340) was seen
only through a secondary page and is not verified. So the integer exponents `3 ≤ m ≤ 85` (or
`≤ 89`) were open before the proof of RH. Exponents below 3 are not covered here. The proof of RH
is L. Alpöge's (2026), certified by the Lean FRO and the Mathlib Initiative on 2026-11-21.

```lean
-- PrimePowers/Statement.lean (fixed targets)
def PrimeBetweenRealPowers : Prop :=
  ∀ α x : ℝ, 3 ≤ α → 1 ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ α < p ∧ (p : ℝ) < (x + 1) ^ α

def PrimeBetweenIntegerPowers : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ m < p ∧ p < (n + 1) ^ m

-- PrimePowers/Main.lean
theorem primeBetweenRealPowers_of_RH (hRH : RiemannHypothesis) : PrimeBetweenRealPowers
theorem primeBetweenIntegerPowers_of_RH (hRH : RiemannHypothesis) : PrimeBetweenIntegerPowers
theorem primeBetweenPowers_of_RH (hRH : RiemannHypothesis) {α x : ℝ} (hα : 3 ≤ α)
    (hx0 : 0 ≤ x) (hx : (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 < x ^ (α / 3)) :
    ∃ p : ℕ, p.Prime ∧ x ^ α < p ∧ (p : ℝ) < (x + 1) ^ α

-- Unconditional/PrimePowersUnconditional.lean
theorem prime_between_real_powers_unconditional : PrimePowers.PrimeBetweenRealPowers
theorem prime_between_integer_powers_unconditional : PrimePowers.PrimeBetweenIntegerPowers
```

The third theorem is the sharp form: it allows any `x ≥ 0` with `x^{α/3} > 2^{1/3} − 1`, which is
Caldwell–Cheng's threshold `x > 0.26` transported to the exponent `α`; for `α = 3` it is exactly
mills-rh's range.

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `prime_between_real_powers_unconditional`, `prime_between_integer_powers_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `PrimePowers.primeBetweenRealPowers_of_RH`, `primeBetweenIntegerPowers_of_RH`, `primeBetweenPowers_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |

The premise is `Mills.primeStrictlyBetweenCubes_of_RH` (mills-rh, Caldwell–Cheng 2005 Lemma 5,
proved there from Schoenfeld's θ bound with his constant `1/(8π)`). The main library does not
import riemann-hypothesis. The two target statements are this project's own transcriptions of the
paper's theorem (formal-conjectures has no entry).

## Axioms

`lake env lean scripts/axioms.lean`, 2026-11-26:

```
'PrimePowers.primeBetweenPowers_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound,
  Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
  Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
  Schoenfeld.PsiCert.chunk00 … chunk19 ._native.native_decide.ax_1_1]
```

`primeBetweenRealPowers_of_RH` and `primeBetweenIntegerPowers_of_RH` print the same list: the
three standard axioms and 22 `native_decide` axioms, all inherited from schoenfeld-rh (its
proved-sound ψ and θ certificate checkers; see that README for what they compute and their
timings). This project adds no `native_decide`, `sorry`, `axiom` or `opaque` of its own.

## Proof outline

1. Put `y = x^{α/3}`. Then `y³ = x^α` (`PrimePowers.rpow_third_cube`).
2. For `r = α/3 ≥ 1`, `t ↦ t^r` is superadditive on `[0, ∞)` (Mathlib
   `Real.add_rpow_le_rpow_add`), so `y + 1 = x^r + 1^r ≤ (x+1)^r`, hence `(y+1)³ ≤ (x+1)^α`.
3. Mills' `primeStrictlyBetweenCubes_of_RH` gives a prime in `(y³, (y+1)³) ⊆ (x^α, (x+1)^α)`
   whenever `y > 2^{1/3} − 1`. For `x ≥ 1` and `α ≥ 3`, `y ≥ 1`.
4. For integer `m`, `n`: take `α = m`, `x = n` and `Real.rpow_natCast`.

## Layout

| File | Content |
|---|---|
| `PrimePowers/Statement.lean` | the two target statements |
| `PrimePowers/Main.lean` | the reduction and the three theorems above |
| `Unconditional/PrimePowersUnconditional.lean` | RH discharged in one line |
| `scripts/check-unconditional.sh` | links with riemann-hypothesis and prints the axioms |
| `scripts/axioms.lean` | `#print axioms` for the main library |

## Deviations from the literature

The exponent range is `α ≥ 3`, with a strict interval, where Chamberland–Straub's Theorem 1.2(a)
covers `α ≥ 9/4` with a closed interval. Between `9/4` and `3` they combine the same RH bound
with a computation of prime gaps (Sorenson–Webster) for small `x`; that range needs a finite
check far beyond what this project's proof-sound checkers do, and is not proved here.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build PrimePowers` takes about 20 s here once
`mills-rh`, `schoenfeld-rh` and `erdos-985` are built. Building mills-rh from scratch against a
stale schoenfeld-rh cache rebuilt about 19,000 modules (13 min wall on 16 cores, about 3 CPU-hours
in total); with warm sibling builds it is seconds.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `prime_between_real_powers_unconditional` | `PrimeBetweenRealPowers` | as above (3 standard + 22 `native_decide`) |
| `prime_between_integer_powers_unconditional` | `PrimeBetweenIntegerPowers` | as above |

`scripts/check-unconditional.sh` links against riemann-hypothesis commit `507a75d91d`; it needs
about 93 GB of cache, 19 GB of RAM and an open-file limit of about 900k (run
`sudo prlimit --pid $$ --nofile=2000000:2000000` first). The axiom output for the unconditional
file has not been produced yet.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh).
This check links against the community build cache and does not repeat those kernel checks.

## Credits

No vendored files. Depends on [`mills-rh`](../mills-rh/) and, through it,
[`schoenfeld-rh`](../schoenfeld-rh/) and [`erdos-985`](../erdos-985/). Built by OpenHuman agents.
Licence: GPLv3 (`LICENSE`).
