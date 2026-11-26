# Blueprint: the least prime in a residue class under GRH

Target (`BachSorenson/Statement.lean`, fixed):

```lean
def BachSorensonBound (c : ℝ) : Prop :=
  ∀ q a : ℕ, 2 ≤ q → a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * ((q : ℝ) * Real.log q) ^ 2
```

Bach–Sorenson (Math. Comp. 65 (1996)) state it with `c = 2`. Proved here: `c = 7/2`.

Notation: `w(n) = 1 − n/x`, `bachSum χ x = Σ_{n<x} Λ(n) χ(n) w(n)` (erdos-985),
`T(a, x) = Σ_{n<x, n ≡ a} Λ(n) w(n)`, `B(q, x) = (√x + 2 + 3/x)(2/3)(log q + 5/3) + log x + 1.6`.

## Steps

1. **Primitive characters** (ankeny-grh `Ankeny.norm_bachSum_le`, reused). For `ψ` primitive
   non-trivial mod `f`, under GRH, `‖bachSum ψ x‖ ≤ (√x + 2 + 3/x)(2/3)(log f + 5/3) + log x + 1.6`.

2. **Any non-principal character** (`BachSorenson/Character.lean`).
   ```lean
   theorem norm_bachSum_le_charBound (hGRH) {q} [NeZero q] (χ : DirichletCharacter ℂ q)
       (hχ : χ ≠ 1) (x : ℕ) (hx : 144 ≤ x) : ‖bachSum χ x‖ ≤ charBound q x
   ```
   `bachSum χ − bachSum ψ` lives on prime powers `p^k`, `p | q`, `p ∤ f`: at most
   `(2/3)√x Σ_{p∈R} log p` (`Nat.log p x ≤ (2/3)√x` for `x ≥ 144`), absorbed by
   `log f + Σ_{p∈R} log p ≤ log q`.

3. **Orthogonality** (`BachSorenson/Orthogonality.lean`).
   ```lean
   lemma classSum_orthogonality (ha : IsUnit a) (x) :
       (q.totient : ℂ) * classSum q a x = ∑ χ, χ a⁻¹ * bachSum χ x
   theorem totient_mul_classSum_ge (hGRH) (ha : IsUnit a) (x) (hx : 144 ≤ x) :
       x/2 − √x/20 − 3 − ω(q) log x − (φ(q) − 1) B(q, x) ≤ φ(q) T(a, x)
   ```
   Principal character: erdos-985 `bach_principal_of_GRH`
   (`|Σ_{n<x} Λ(n) w(n) − x/2| ≤ √x/20 + 3`) minus the `n` not coprime to `q` (`≤ ω(q) log x`).

4. **Prime powers that are not primes** (`BachSorenson/PrimePowers.lean`).
   ```lean
   theorem ppSum_le (x) (hx : 2 ≤ x) : ppSum x ≤ ppBound x
   -- ppBound x = log 4 · (√x + x^{1/3} + x^{1/4} log x / log 2)
   ```
   `ψ − θ = Σ_{2≤k≤log₂ x} θ(x^{1/k})` (Mathlib `psi_eq_theta_add_sum_theta`) and
   `θ(y) ≤ y log 4` (Mathlib `theta_le_log4_mul_x`).

5. **One modulus** (`BachSorenson/Large.lean`). With `x = ⌊c (q log q)²⌋`, if no prime `p < x` is
   `≡ a`, then `T(a, x) ≤ ppSum x`, and with `φ(q) ≤ q`:
   `x/2 − √x/20 − 3 − ω log x ≤ q (B(q, x) + ppBound x)`. `NumericOK c q` is the negation.
   ```lean
   theorem bachSorenson_of_numericOK (hGRH) (hc : 0 ≤ c) (hq : 2 ≤ q) (hnum : NumericOK c q)
       (ha : a.Coprime q) : ∃ p, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * (q * log q) ^ 2
   ```

6. **Numerics** (`BachSorenson/Numerics.lean`): `numericOK_of_ge : 2^15 ≤ q → NumericOK (7/2) q`.
   Bounds used: `s = √x ≥ 637000`, `1.8708 q log q < s + 1`, `L + 5/3 ≤ 1.1604 L`,
   `x^{1/3} ≤ s/86`, `x^{1/4} log x ≤ 0.03434 s` (tangent of `log` at `512`), `ω(q) ≤ q`. The
   result is a quadratic in `s` with leading coefficient `0.4892 < 1/2`.

7. **Checker soundness** (`BachSorensonCheck.lean`, `BachSorenson/Checker.lean`).
   ```lean
   theorem exists_prime_of_checkRange (h : checkRange N lo n = true) (hq1 : lo ≤ q)
       (hq2 : q < lo + n) (hq : 2 ≤ q) (ha : a.Coprime q) :
       ∃ p, p.Prime ∧ p ≡ a [MOD q] ∧ p < bound q
   lemma bound_le (q) (hq : q ≠ 0) : (bound q : ℝ) ≤ 7/2 * (q * log q) ^ 2
   ```
   Prime table by trial division (sound: a `true` entry is prime, via `Nat.minFac_sq_le_self`);
   for each `a < q` coprime to `q` the walk `a, a + q, …` below `bound q` hits a table prime.
   `bound q = ⌊(7/2) q² (⌊log₂ q⁸⌋ · 0.6931471803 / 8)²⌋`.

8. **Finite range** (`BachSorenson/Compute.lean`): 16 `native_decide` chunks of 2048 moduli
   cover `q < 2^15`, prime table of size `8·10^6` (the largest least prime needed is below it).

9. **Assembly** (`BachSorenson/Main.lean`): `bachSorenson_of_GRH : BachSorensonBound (7/2)`.

## Sizing (outside Lean, `exact` real arithmetic)

Smallest `q` beyond which the inequality of step 5 holds for every larger `q`, with the bounds of
steps 2–4 and exact `ω(q)`:

| c   | 8  | 6   | 5   | 4    | 3.8  | 3.6   | 3.5   | 3.4   | 3.2   | 3      | 2         |
|-----|----|-----|-----|------|------|-------|-------|-------|-------|--------|-------------|
| q₀  | 143| 464 | 670 | 3477 | 5884 | 11251 | 16518 | 25560 | 74761 | 321956 | ~10^28    |

The finite check costs about `Σ_{q<Q₀} φ(q) · (steps per class)`: `1.2·10^8` table lookups for
`Q₀ = 2^13`, about `2·10^9` for `2^15`. At `2^15` the Lean-provable margin (uniform constants
for all `q ≥ Q₀`) is comfortable for `c = 7/2` (leading coefficient `0.489`).

Asymptotically the argument compares `x/(2φ)` with `(2/3)√x log q + log 4 · √x` per unit, so it
needs `√c > (4/3)(1 + O(1/log q))`: `c > 16/9` in the limit, and `c = 2` only once
`log q ≳ 64` (`q ≳ 10^28`). Reaching Bach–Sorenson's `2` for all `q` would need their sharper explicit
formula; see the README.

# Part 2: the constant `2` (`BachSorenson/Two/`)

Target: the same `BachSorensonBound c` with Bach–Sorenson's `c = 2`
(`bachSorenson_two_of_GRH : DirichletLNonvanishingRightOfHalf → BachSorensonBound 2`).

The Cesàro weight of Part 1 caps the method at `c > 16/9`. Bach and Sorenson (Math. Comp. 65,
§§3–4) use the weight `(n/x)^a log(x/n)` (Mellin kernel `x^s/(s + a)²`) and sum the zero sums
over all characters at once, so that `Σ_χ L'/L(1 + a, χ)` has a sign. Here the kernel is
`x^s/s²` (the log weight `log(x/n)`, for which lls-grh already proves the explicit formula), and
the shift `a` enters only in the zero-sum bound. Write `S(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) log(x/n)`,
`Z₂(ψ) = Σ_ρ m_ρ/|ρ|²`, `σ = 1 + a`, `a = 1/20`.

1. **Explicit formula** (lls-grh `LLS.LogAux.log_explicit_formula`, reused): for `ψ` primitive,
   `S(x, ψ) = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0, ψ) log x + Γ̃(x)`, `D = Λ'/Λ`.
2. **Zero sums** (`Two/ZeroSum.lean`). Under GRH, on `Re ρ = 1/2`,
   `Re(1/(σ − ρ) − 1/(1 − ρ)) ≥ −(a/(1 + 2a))/|ρ|²`, so `Re D(1) ≤ Re D(σ) + (a/(1+2a)) Z₂`
   (`re_D_one_le`). With `Z₂ = log f + Re D(1, ψ) + Re D(1, ψ⁻¹)` (`LLS.Z2_eq`) and
   `Z₂(ψ⁻¹) = Z₂(ψ)`: `Z₂ ≤ (1 + 2a)(log f + Re D(σ, ψ) + Re D(σ, ψ⁻¹))` (`Z2_le`).
   Also `‖D(0)‖ ≤ log f + Z₂ + 2.52` (`norm_D_zero_le`: functional equation,
   `‖D(1) − D(2)‖ ≤ Z₂`, `‖L'/L(2)‖ ≤ Σ Λ(n) n^{-3/2} ≤ 1.52`).
3. **`L'/L` at `σ`** (`Two/LogDeriv.lean`). `Σ_{χ mod q} Re L'/L(σ, χ) ≤ 0`
   (`−Σ_χ L'/L = φ(q) Σ_{n ≡ 1} Λ(n) n^{-σ}`), `−Re L'/L(σ, χ) ≤ Σ Λ(n) n^{-σ} ≤ (2/a)(1 + 2/a)
   = 1640` (`Λ(n) ≤ log n ≤ (2/a) n^{a/2}` and `Σ n^{-1-b} ≤ 1 + 1/b`), so
   `Σ_{χ ≠ 1}(Re L'/L(σ, χ) + Re L'/L(σ, χ⁻¹)) ≤ 3280`. The primitive `ψ` and the lifted `χ`
   differ by `Σ_{p | q, p ∤ f} log p/(p − 1)` (`re_ld_le_changeLevel`), and
   `log f + 2 Σ_{p | q, p ∤ f} log p/(p − 1) ≤ log q + log 2`. The gamma factor gives
   `Re Γ'/Γ-part(21/20) ≤ −0.7` (`re_gammaLogDeriv_le`).
4. **Per character** (`Two/Character.lean`): `Z₂(ψ_χ) ≤ (11/10)(log q + log 2 − 7/5
   + Re L'/L(σ, χ) + Re L'/L(σ, χ⁻¹))`, `‖S(x, ψ)‖ ≤ (√x + 1 + log x) Z₂ + (log f + 2.52) log x
   + log² x/2 + 5 log x + 2`, and lifting to `q` costs at most `ω(q) log² x`.
5. **Prime powers** (`Two/PrimePowers.lean`): `Σ_{n ≤ x, n not prime} Λ(n) log(x/n) ≤
   log 4 (2x^{1/2} + 3x^{1/3} + 60x^{1/4} + (log₂ x)² x^{1/12})`, grouping `n = p^k` by `k` and
   `Σ_{p ≤ y} log p · log(y/p) ≤ y log 4` (summation by parts on Chebyshev's `θ`).
6. **One modulus** (`Two/Large.lean`): orthogonality, the principal character from
   `LLS.psiLog_ge` (`Σ_{n ≤ x} Λ(n) log(x/n) ≥ x − (3/20)√x − 3 log x − 3`), and
   `NumericOK2 q` (the resulting inequality at `x = ⌊2(q log q)²⌋`) give a prime `p < x`.
7. **Numerics** (`Two/Numerics.lean`): `NumericOK2 q` for `q ≥ 2^15`. With `s = √x`, `U = q log q`:
   `s ≥ 1.41421 U`, the leading terms give `s(s − 1.1U − 1.9951q) ≥ 1.27 q s`, and the rest is
   at most `0.41 q s` (`u = x^{1/12} ≥ 8.8`, `log u ≤ 0.248 u`).
8. **Finite range** (`BachSorensonCheck2.lean`, `Checker2.lean`, `Compute2*.lean`): 16
   `native_decide` chunks, every class for `2 ≤ q < 2^15` below
   `bound2 q = ⌊2 q² (⌊log₂ q⁸⌋ · 0.6931471803/8)²⌋ ≤ 2 (q log q)²`.

## Sizing for constant `2` (outside Lean)

Margin of the Lean inequality per unit `q√x` (positive means `NumericOK2 q` holds), with the
constants above (`a = 1/20`, crude `Σ Λ(n) n^{-σ} ≤ 1640`):

| q      | 2^13  | 2^14 | 2^15 | 2^16 | 10^6 | 10^12 |
|--------|-------|------|------|------|------|-------|
| margin | 0.08  | 0.64 | 1.04 | 1.36 | 2.34 | 6.71  |

The smallest `q₀` for which the inequality holds from then on, for other `c` (same bounds):
`c = 2`: `≈ 7300`; `c = 5/2`: `≈ 2800`; `c = 3`: `≈ 1800`. The finite check below `2^15`
costs about `1.9·10^9` progression steps (a C sieve does it in 28 s); the largest least prime is
`6188401`, and the largest `p/(2(q log q)²)` is `0.78`, at `q = 2`.
