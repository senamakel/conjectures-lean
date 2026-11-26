# Blueprint: Bach's explicit Ankeny theorem under GRH

Targets (`Ankeny/Statement.lean`, definitions frozen): `BachSubgroupBound c` and
`LeastNonresidueBound c`, conditional on `Erdos985.DirichletLNonvanishingRightOfHalf`.

## Strategy

Fix `q`, a proper subgroup `H < (ℤ/q)ˣ`, and suppose every unit of residue `≤ c log² q` lies in
`H`. Put `L = log q` and `x = ⌊c L²⌋ ∈ ℕ`.

1. **Character** (`Ankeny/Character.lean`). `G/H` is a non-trivial finite abelian group, so it
   has a character `ψ ≠ 1` (Mathlib `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`).
   `χ = ψ ∘ (G → G/H)` as a `DirichletCharacter ℂ q` (`MulChar.ofUnitHom`): `χ ≠ 1`, `χ|_H = 1`.
2. **Values below x.** For `n ≤ c L²` coprime to `q`, the unit `n mod q` has residue `≤ n`, so it
   is in `H` and `χ(n) = 1`. With `χ*` the primitive character (conductor `f ∣ q`, `f ≥ 2`),
   `χ*(n) = χ(n) = 1` for those `n`.
3. **Splitting the sum** (`Ankeny/Split.lean`). With `w(n) = 1 − n/x`,
   `Re bachSum χ* x = S₀ − E + Re Σ_{n<x, (n,q)>1} Λ(n) χ*(n) w(n)`, where
   `S₀ = Σ_{n<x} Λ(n) w(n)` and `E = Σ_{n<x,(n,q)>1} Λ(n) w(n)`. The last sum only sees prime
   powers `p^k` with `p ∣ q`, `p ∤ f` (else `χ*(p) = 0`); call that set of primes `R`.
4. **Prime-power counting** (`Ankeny/PrimePowers.lean`).
   `Σ_{n<x, n = p^k} Λ(n) ≤ log p · Nat.log p x ≤ log x`, so `E ≤ ω(q) log x`; and for `x ≥ 144`,
   `Nat.log p x ≤ Nat.log 2 x ≤ (2/3)√x`, so the `R`-part is `≤ (2/3)√x · Σ_{p∈R} log p`.
   Since `f · ∏_{p∈R} p ∣ q`, `log f + Σ_{p∈R} log p ≤ L`: the `R`-part is absorbed by the
   zero-sum term, which is `(2/3) A (log f + 5/3)` with `A = √x + 2 + 3/x`.
5. **Analytic input** (Erdos985): `explicit_formula` + `zeroSum_le` + bounds for `χ*` give
   `‖bachSum χ* x‖ ≤ (2/3) A (log f + 5/3) + log x + 1.6` (re-assembled for arbitrary modulus
   `f`), and `bach_principal_of_GRH` gives `S₀ ≥ x/2 − √x/20 − 3`.
6. **Contradiction** (`Ankeny/Numerics.lean`):
   `x/2 − √x/20 − 3 − ω(q) log x > (2/3) A (L + 5/3) + log x + 1.6` once `q ≥ Q₀(c)`.
   `ω(q)` is bounded by `16^ω · 30030 ≤ q · 16^6` (`Erdos985.pow_card_primeFactors_mul_le`).
7. **Finite range** `q < Q₀` (`Ankeny/Compute*.lean`): a verified checker shows that the units
   `≤ y_q` generate `(ℤ/q)ˣ`, with `y_q ≤ c log² q` certified by `log q ≥ ⌊log₂ q⌋ log 2`.
   The checker marks only `1` and `r·g mod q` for marked `r` and generators `g ≤ y_q` coprime
   to `q`, so every marked residue lies in the subgroup they generate.
8. **Least non-residue**: `H = ` squares, proper for odd `p` since `x ↦ x²` is not injective.

## Constant

The zero-sum coefficient `2/3` forces `c > 16/9` asymptotically, and the lower-order terms push
the threshold `Q₀(c)` up fast: numerically `Q₀(5) ≈ 8·10³`, `Q₀(4.5) ≈ 3·10⁴`,
`Q₀(4) ≈ 2·10⁵`, `Q₀(3) ≈ 10⁹`, `Q₀(2) ≈ e^{750}`. Bach's `c = 2` needs a sharper explicit
formula (different weight, sharper zero sum) plus a large computation; out of reach here.
Target: the smallest `c` whose `Q₀` a verified checker can cover.

## Status

All steps done; no `sorry`. Constant achieved: `21/5` (analytic for `q ≥ 2^17`, verified
computation below). The finite range uses `native_decide` in eight chunks
(`Ankeny/Compute/Chunk*.lean`) on a core-Lean checker precompiled to native code; its soundness
is proved in `Ankeny/Checker.lean`. Bach's `2` is not reached (see README).

- [x] 1 Character (`Character.lean`)  - [x] 2-3 Split (`Split.lean`)
- [x] 4 Prime powers (`PrimePowers.lean`)  - [x] 5 Analytic bound (`Analytic.lean`)
- [x] 6 Numerics (`Numerics.lean`, `c = 21/5`, `Q₀ = 2^17`)
- [x] 7 Finite check (`AnkenyCheck.lean`, `Checker.lean`, `Finite.lean`, `Compute*.lean`)
- [x] 8 Least non-residue (`LeastNonresidue.lean`)  - [x] README / axioms
