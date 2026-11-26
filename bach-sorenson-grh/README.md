# Bach–Sorenson's least prime in a residue class under GRH in Lean

This repository proves Bach and Sorenson's theorem in Lean with their constant `2`: for every
modulus `q ≥ 2` and every `a` coprime to `q` there is a prime `p ≡ a (mod q)` with
`p < 2 (q log q)²`. The main library is a complete Lean proof that GRH for Dirichlet
L-functions implies the bound, and `Unconditional/` proves it unconditionally in Lean with the
certified proof of GRH by L. Alpöge in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
The theorem is E. Bach and J. Sorenson, *Explicit bounds for primes in residue classes*,
Math. Comp. 65 (1996), 1717–1735 (abstract and §5: "the least prime `p ≡ m (mod q)` is less
than `2(q log q)²`"), who also prove `p ≤ (1 + o(1)) (φ(q) log q)²`. Without GRH the known
bounds are of Linnik type, `p ≪ q^L` (Xylouris: `L = 5`).

Literature status: RH-consequence. The proof follows Bach and Sorenson's method of summing the
zero sums over all characters at `s = 1 + a`. A proved-sound checker covers every class for
`q < 2^15`, and the analytic argument covers `q ≥ 2^15`. There is no `sorry`.

GRH enters as `Erdos985.DirichletLNonvanishingRightOfHalf`, copied verbatim from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
`src/Statements.lean`:

```lean
def BachSorenson.BachSorensonBound (c : ℝ) : Prop :=   -- BachSorenson/Statement.lean
  ∀ q a : ℕ, 2 ≤ q → a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * ((q : ℝ) * Real.log q) ^ 2

theorem BachSorenson.bachSorenson_two_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    BachSorensonBound 2                                -- BachSorenson/Two/Main.lean

theorem bachSorenson_two_unconditional : BachSorenson.BachSorensonBound 2
  -- Unconditional/BachSorensonUnconditional.lean
```

`BachSorensonBound 2` is the paper's statement, strict inequality included. The library also
keeps an earlier, weaker theorem with constant `7/2`, which `BachSorensonBound 2` implies:

```lean
theorem BachSorenson.bachSorenson_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    BachSorensonBound (7 / 2)                          -- BachSorenson/Main.lean
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `BachSorenson.bachSorenson_two_of_GRH` | C | `DirichletLNonvanishingRightOfHalf` (erdos-985, copied verbatim from riemann-hypothesis) |
| `bachSorenson_two_unconditional` (`Unconditional/`) | U | none |
| `BachSorenson.bachSorenson_of_GRH` (constant `7/2`) | C | as above |
| `bachSorenson_unconditional` (`Unconditional/`, constant `7/2`) | U | none |

`BachSorenson/Statement.lean` holds the target `BachSorensonBound c`; `c = 2` is the paper's
constant. The requirement `2 ≤ q` is there because for `q = 1` the right-hand side is
`c (1 · log 1)² = 0`. formal-conjectures has no statement of this theorem.

## Axioms

Real output of `#print axioms` (`lake env lean`, 2026-11-24, after `lake build`):

```
'BachSorenson.bachSorenson_two_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 BachSorenson.chunk2_ok_0._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_1._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_10._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_11._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_12._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_13._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_14._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_15._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_2._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_3._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_4._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_5._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_6._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_7._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_8._native.native_decide.ax_1_1,
 BachSorenson.chunk2_ok_9._native.native_decide.ax_1_1]
'BachSorenson.Two.exists_prime_of_numericOK2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BachSorenson.Two.numericOK2_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'BachSorenson.bachSorenson_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 BachSorenson.chunk_ok_0._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_1._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_10._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_11._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_12._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_13._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_14._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_15._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_2._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_3._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_4._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_5._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_6._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_7._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_8._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_9._native.native_decide.ax_1_1]
```

`bachSorenson_two_of_GRH` uses 16 `native_decide` axioms from the finite computation for
`2 ≤ q < 2^15`. Each asserts that the compiled evaluation of the core-Lean checker
`checkRange2` on one chunk of 2048 moduli agrees with its definition. The checker builds a table
of the primes below `8·10^6` by trial division and then, for every `a < q` coprime to `q`, walks
`a, a + q, a + 2q, …` until it hits a table prime `p ≤ bound2 q = ⌊2 q² (⌊log₂ q⁸⌋ log 2/8)²⌋`
(with `log 2` replaced by `0.6931471803`), a number strictly below `2 (q log q)²`. Its soundness
(`BachSorenson.Checker.exists_prime_of_checkRange2`, `Checker.bound2_lt`) is proved in Lean.
The chunks take 9 to 30 s each, about 5 CPU-minutes in total. The analytic half (`q ≥ 2^15`,
`exists_prime_of_numericOK2`, `numericOK2_of_ge`) uses only the standard three axioms.

The constant-`7/2` theorem `bachSorenson_of_GRH` uses the 16 chunks `chunk_ok_N` of the first checker
(`checkRange`, bound `(7/2)(q log q)²`, about 6.5 CPU-minutes). ankeny-grh's and lls-grh's own
`native_decide` axioms do not appear: only their analytic modules are imported.

## Proof outline

### Constant `2` (`BachSorenson/Two/`)

The full blueprint is [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md), Part 2. Write
`S(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) log(x/n)` (the weight `log(x/n)`, Mellin kernel `x^s/s²`),
`Z₂(ψ) = Σ_ρ m_ρ/|ρ|²`, and `σ = 1 + a` with `a = 1/20`.

1. `LLS.LogAux.log_explicit_formula` (lls-grh): for primitive `ψ`,
   `S(x, ψ) = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0, ψ) log x + Γ̃(x)`, `D = Λ'/Λ`.
2. `Two/ZeroSum.lean`: under GRH `Z₂ ≤ (1 + 2a)(log f + Re D(σ, ψ) + Re D(σ, ψ⁻¹))`, from
   `Re(1/(σ − ρ) − 1/(1 − ρ)) ≥ −(a/(1 + 2a))/|ρ|²` on `Re ρ = 1/2` and
   `Z₂ = log f + Re D(1, ψ) + Re D(1, ψ⁻¹)`; and `‖D(0)‖ ≤ log f + Z₂ + 2.52`.
3. `Two/LogDeriv.lean`: `Σ_{χ mod q} Re L'/L(σ, χ) ≤ 0` (the Dirichlet coefficients of
   `−Σ_χ L'/L` are `φ(q) Λ(n) [n ≡ 1]`; Bach–Sorenson use `ζ_E'/ζ_E(1 + a) ≤ 0` the same way),
   `Σ_n Λ(n) n^{-σ} ≤ 1640`, the imprimitive correction `Σ_{p | q, p ∤ f} log p/(p − 1)` and
   `Re Γ'/Γ`-part `≤ −0.7` at `σ = 21/20`. Together, per non-principal `χ` on average,
   `Z₂(ψ_χ) ≲ (11/10)(log q + log 2 − 7/5)`.
4. `Two/Character.lean`: `‖S(x, χ)‖ ≤ (√x + 1 + log x) Z₂(ψ_χ) + (log q + 2.52) log x
   + log² x/2 + 5 log x + 2 + ω(q) log² x` for every non-principal `χ` mod `q`.
5. `Two/PrimePowers.lean`: `Σ_{n ≤ x, n not prime} Λ(n) log(x/n) ≤ log 4 (2√x + 3x^{1/3}
   + 60 x^{1/4} + (log₂ x)² x^{1/12})` (Chebyshev's `θ(y) ≤ y log 4`, summation by parts).
6. `Two/Large.lean`: orthogonality and `LLS.psiLog_ge` (`Σ_{n ≤ x} Λ(n) log(x/n) ≥
   x − (3/20)√x − 3 log x − 3` under RH). With `x = ⌊2 (q log q)²⌋`, if no prime `p < x` is
   `≡ a`, then `NumericOK2 q` fails. The leading terms compare `x` with
   `1.1 √x q log q + 2 log 4 · q √x`; since `√x ≈ √2 q log q`, the margin is
   `(√2 − 1.1) log q − 1.995 > 0` per unit `q √x` once `log q ≥ 6.4`.
7. `Two/Numerics.lean`: `NumericOK2 q` for every `q ≥ 2^15`, standard axioms only.
8. `BachSorensonCheck2.lean`, `BachSorenson/Checker2.lean`, `BachSorenson/Compute2*.lean`: every
   `2 ≤ q < 2^15` by the verified computation. The largest least prime that occurs is
   `6188401`; the largest ratio `p/(2 (q log q)²)` is `0.78`, at `q = 2`.
9. `BachSorenson/Two/Main.lean`: `bachSorenson_two_of_GRH`.

### Constant `7/2` (`BachSorenson/`)

This is the earlier, weaker theorem. It uses the Cesàro weight `1 − n/x` with erdos-985's
zero-sum bound `Σ_ρ 1/|ρ(ρ+1)| ≤ (2/3)(log f + 5/3)` per character. That needs
`√c > (4/3)(1 + O(1/log q))`, so `c > 16/9` in the limit and `c = 2` only for `q ≳ 10^28`;
the per-character bound stops this route at `7/2`. Summing the zero sums over all characters
at `s = 1 + a`, as Bach and Sorenson do, removes that barrier and gives the constant `2` above.

The analytic toolkit (weighted explicit formula, zero-sum bound under GRH, principal-character
bound) is [erdos-985](https://github.com/senamakel/erdos-985); the primitive-character bound and
the prime-power lemmas come from [ankeny-grh](https://github.com/senamakel/ankeny-grh). Both are
lake dependencies. The full blueprint, with each step's Lean statement, is
[`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). Write `w(n) = 1 − n/x`.

1. `BachSorenson/Character.lean`: for any non-trivial `χ` mod `q` and `x ≥ 144`,
   `‖Σ_{n<x} Λ(n) χ(n) w(n)‖ ≤ B(q, x) = (√x + 2 + 3/x)(2/3)(log q + 5/3) + log x + 1.6`.
   This is `Ankeny.norm_bachSum_le` for the inducing primitive character plus the prime powers
   of primes dividing `q` but not the conductor, absorbed as in `Ankeny.key_inequality`.
2. `BachSorenson/Orthogonality.lean`: with `T(a, x) = Σ_{n<x, n≡a} Λ(n) w(n)`,
   `φ(q) T(a, x) = Σ_χ χ(a⁻¹) Σ_{n<x} Λ(n) χ(n) w(n)`, hence
   `φ(q) T(a, x) ≥ x/2 − √x/20 − 3 − ω(q) log x − (φ(q) − 1) B(q, x)`.
3. `BachSorenson/PrimePowers.lean`: prime powers that are not primes contribute at most
   `ψ(x) − θ(x) ≤ log 4 · (√x + x^{1/3} + x^{1/4} log x / log 2)` (Mathlib's Chebyshev bounds).
4. `BachSorenson/Large.lean`: with `x = ⌊c (q log q)²⌋`, if no prime below `x` is `≡ a`, then
   `x/2 − √x/20 − 3 − ω(q) log x ≤ q (B(q, x) + log 4 · (…))`.
5. `BachSorenson/Numerics.lean`: for `c = 7/2` and `q ≥ 2^15` that inequality fails (a quadratic
   in `s = √x` with leading coefficient `0.4892 < 1/2`).
6. `BachSorensonCheck.lean`, `BachSorenson/Checker.lean`, `BachSorenson/Compute*.lean`: every
   `2 ≤ q < 2^15` by the verified computation.
7. `BachSorenson/Main.lean`: assembly.

## Layout

| File | Content |
|---|---|
| `BachSorenson/Statement.lean` | target `BachSorensonBound c` (fixed) |
| `BachSorenson/Character.lean` | bound for a non-principal character of any modulus |
| `BachSorenson/Orthogonality.lean` | the class sum via orthogonality, lower bound under GRH |
| `BachSorenson/PrimePowers.lean` | `ψ(x) − θ(x)` bound |
| `BachSorenson/Large.lean` | `NumericOK c q` implies the bound at `q` |
| `BachSorenson/Numerics.lean` | `NumericOK (7/2) q` for `q ≥ 2^15` |
| `BachSorensonCheck.lean` | executable checker (core Lean, precompiled) |
| `BachSorenson/Checker.lean` | checker soundness, `bound q ≤ (7/2)(q log q)²` |
| `BachSorenson/Compute.lean`, `Compute/Chunk*.lean` | the 16 `native_decide` chunks |
| `BachSorenson/Main.lean` | `bachSorenson_of_GRH` |
| `BachSorenson/Two/ZeroSum.lean` | zero sums at `1`, `1 + a`, `2` for a primitive character |
| `BachSorenson/Two/LogDeriv.lean` | `L'/L(21/20)` summed over characters, `p`-series bound, gamma factor |
| `BachSorenson/Two/Character.lean` | log-weighted sum of a non-principal character |
| `BachSorenson/Two/PrimePowers.lean` | log-weighted prime powers that are not primes |
| `BachSorenson/Two/Large.lean` | `NumericOK2 q` implies the bound at `q` |
| `BachSorenson/Two/Numerics.lean` | `NumericOK2 q` for `q ≥ 2^15` |
| `BachSorensonCheck2.lean`, `BachSorenson/Checker2.lean` | checker for `2`, soundness, `bound2 q < 2(q log q)²` |
| `BachSorenson/Compute2.lean`, `Compute2/Chunk*.lean` | the 16 `native_decide` chunks for `2` |
| `BachSorenson/Two/Main.lean` | `bachSorenson_two_of_GRH` |
| `Unconditional/BachSorensonUnconditional.lean` | GRH discharged by riemann-hypothesis |

## Differences in the proof

The statement is the paper's. The route to it differs from Bach and Sorenson's in three places.

* Bach and Sorenson use the weight `(n/x)^a log(x/n)` (kernel `x^s/(s + a)²`) and optimise `a`
  numerically for each range of `q`. Here the weight is `log(x/n)` (`a = 0` in the explicit
  formula, which lls-grh already proves), and the shift `a = 1/20` is used only to bound the
  zero sum, through `|ρ + a|² ≤ (1 + 2a)²|ρ|²`. This costs the factor `1 + 2a = 1.1` on the
  leading term: the method needs `√c > 1.1`, against Bach and Sorenson's `√c > 1 + o(1)`.
* Prime powers use Chebyshev's `θ(y) ≤ y log 4` (Mathlib) where Bach and Sorenson use Costa
  Pereira's `ψ − θ < 1.001√t + (4/3)t^{1/3}`, and `Σ Λ(n) n^{-21/20} ≤ 1640` is a crude bound
  (`−ζ'/ζ(21/20) ≈ 19.4`). These raise the modulus from which the analytic argument works.
* Bach and Sorenson's analytic bound holds for `q ≥ 1000`, and they check `q ≤ 1000` by
  computer (largest ratio `1.56`). Here the analytic part needs `q ≥ 2^15`, and the
  proved-sound checker covers every class for `q < 2^15` (largest ratio `0.78`, at `q = 2`).

Sizing for this method, outside Lean: the inequality of `NumericOK2` holds from about `q = 7300`
on for `c = 2` (margin `0.64` per unit `q√x` at `2^14`, `1.04` at `2^15`); for `c = 5/2` from
about `2800`, for `c = 3` from about `1800`. See [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

## Deviations from the literature

None. The constant is Bach and Sorenson's `2` and the inequality is strict, as in the paper.
The only added hypothesis is `2 ≤ q`, which the paper leaves implicit (for `q = 1` its bound is
`0`).

## Building

```
lake exe cache get
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`, ankeny-grh `129ad57` and lls-grh
`b8c5afa`). Measured 2026-11-24 on a shared 95-core box (load about 90): the 16 `native_decide`
chunks for `2` took 9, 9, 10, 11, 13, 16, 17, 19, 21, 22, 23, 24, 28, 28, 28 and 30 s (about
5 CPU-minutes, 56 s wall for the whole rebuild); the analytic modules `BachSorenson.Two.ZeroSum`,
`LogDeriv`, `Character`, `PrimePowers`, `Numerics` take 25 to 45 s each. The 16 chunks for
`7/2` took 8 to 40 s each (about 6.5 CPU-minutes).

## Unconditional version

`Unconditional/BachSorensonUnconditional.lean` imports [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the hypothesis with its theorem `LFunction_ne_zero_of_half_lt_re`:

| Theorem | Statement | Axioms |
|---|---|---|
| `bachSorenson_two_unconditional` | `BachSorenson.BachSorensonBound 2` | standard three + 16 `native_decide` (`chunk2_ok_N`) |
| `bachSorenson_unconditional` | `BachSorenson.BachSorensonBound (7 / 2)` | standard three + 16 `native_decide` (`chunk_ok_N`) |

Checked 2026-11-24 with `scripts/check-unconditional.sh` against riemann-hypothesis `507a75d91d`: the build succeeded, `#print axioms bachSorenson_two_unconditional` printed exactly `propext`, `Classical.choice`, `Quot.sound` and the 16 `BachSorenson.chunk2_ok_N._native.native_decide.ax_1_1` axioms, and `#print axioms bachSorenson_unconditional` the standard three and the 16 `BachSorenson.chunk_ok_N._native.native_decide.ax_1_1` axioms (no `sorryAx`). The run took 6 min wall, dominated by importing riemann-hypothesis.

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first: on Linux,
`sudo prlimit --pid $$ --nofile=2000000:2000000`; on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. The analytic layer is used as lake dependencies:
[senamakel/erdos-985](https://github.com/senamakel/erdos-985) at `9538edb`,
[senamakel/ankeny-grh](https://github.com/senamakel/ankeny-grh) at `129ad57` and
[senamakel/lls-grh](https://github.com/senamakel/lls-grh) at `b8c5afa` (the log-weighted
explicit formula `LLS.LogAux.log_explicit_formula`, `LLS.Z2_eq`, `LLS.psiLog_ge`, the
prime-power fibres of `LLS/Losses.lean`). `BachSorenson/Character.lean` follows
`Ankeny.key_inequality` (ankeny-grh, `Ankeny/Split.lean`) closely, adapted from a lower bound on
the real part to a norm bound. The strategy for the constant `2` (zero sums at `1 + a` summed over
all characters) is Bach and Sorenson's.
