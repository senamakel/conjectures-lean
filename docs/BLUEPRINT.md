# Blueprint

Every step is a Lean statement in the repo; all of them are proved (no `sorry`). Thresholds are
the ones the Lean proofs use. The scoping that led to this route is in `SCOPING.md`.

## Part A: idoneal numbers

Target (`Weinberger/Statement.lean`, copied from formal-conjectures):
`Idoneal.IdonealCompletenessStatement : ∀ n, IsIdoneal n → n ∈ knownIdonealNumbers`.

1. **Elementary reduction** (`Weinberger/Elementary.lean`).
   `not_isIdoneal_of_witness : 0 < a → 2a < u → u ∣ n + a² → u² < n + a² → ¬ IsIdoneal n`
   (take `b = u − a`, `c = (n + a²)/u − a`; then `n + a² = (a + b)(a + c)`).
   `not_isSquare_of_isIdoneal : IsIdoneal n → p.Prime → p ≠ 2 → ¬ p ∣ n → p * p < n →
   ¬ IsSquare (-(n : ZMod p))` (`a = |valMinAbs r|`, `u = p`).
2. **The character** (`Weinberger/Character.lean`).
   `kroneckerChar n : DirichletCharacter ℂ (4 * n)`, `u ↦ J(−n | u.val)`, well defined by
   `jacobiSym.mod_right`; `kroneckerChar_prime : kroneckerChar n p = legendreSym p (−n)` for odd
   primes `p ∤ n`. The proof uses its primitive character `ψ = (kroneckerChar n).primitiveCharacter`
   (conductor `N ≤ 4n`), which agrees with it on primes `p ∤ 2n`.
3. **GRH bound for any primitive character** (`Weinberger/GRH.lean`).
   `bach_primitive_of_GRH : χ.IsPrimitive → χ ≠ 1 →
   ‖Σ_{m<x} Λ(m) χ(m)(1 − m/x)‖ ≤ (√x + 2 + 3/x)(2/3)(log N + 5/3) + (log x + 1) + 0.6`,
   reassembled from erdos-985's `explicit_formula`, `zeroSum_le`, `norm_gammaPart_le` and
   `norm_logDeriv_LFunction_two_le` (erdos-985 states it only for prime modulus).
   Principal part: erdos-985's `bach_principal_of_GRH : |S₀(x) − x/2| ≤ √x/20 + 3`.
4. **Sieve upper bound** (`Weinberger/Sieve.lean`).
   `splitSum_le : (P ∋ every prime p < x with p² < x) → (ψ p = −1 for primes p < x outside P) →
   Σ_{m<x} Λ(m)(1 − m/x)(1 + Re ψ(m)) ≤ 2 #P log x`. Powers of one prime below `x` weigh at most
   `log x` (`sum_vonMangoldt_dvd_le`, via `Σ_{d ∣ p^K} Λ(d) = K log p`).
   `two_pow_card_primeFactors_le : 2^{ω(m)} ≤ m`.
5. **Numerics** (`Weinberger/Numerics.lean`). For `x ≥ 10^4`, `N ≤ 4n`, `n < (x + 1)²`,
   `ω log 2 ≤ log 2n`:
   `2(√x + 1 + ω) log x < x/2 − √x/20 − 3 − B`. Uses `log s ≤ s/100 + 3.8521`,
   `log 2 ∈ (0.6931471803, 0.6931471808)`. Margin at `x = 10^4`: about 856 out of 5000.
6. **GRH step** (`Weinberger/Large.lean`). With `x = ⌊√n⌋`, `P = {p < x prime : p² < x ∨ p ∣ 2n}`,
   `#P ≤ √x + 1 + ω(2n)`:
   `exists_split_prime_of_GRH : 10^8 ≤ n → ∃ p, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ n ∧ p * p < n ∧
   IsSquare (-(n : ZMod p))`. If some prime `p < x` lies outside `P`, then `ψ(p) = −1`, `ψ ≠ 1`,
   and steps 3–5 contradict. Otherwise all primes below `x` are in `P` and the trivial character
   gives `2 S₀ ≤ 2 #P log x`, again contradicting step 5.
   `not_isIdoneal_of_GRH : 10^8 ≤ n → ¬ IsIdoneal n`.
7. **Finite range** (`Weinberger/Compute*.lean`). `okN n` searches `u ∈ [3, 403)`,
   `a ∈ [1, (u−1)/2]`; `okN_sound` via step 1. Ten `native_decide` chunks of `10^7` cover `n < 10^8`.
   `repB` searches every `(a, b)` with `a ≤ n`, `b ≤ n/a`; one `native_decide` (`known_noRep`)
   shows the 65 numbers have no representation.
8. **Assembly** (`Weinberger/Main.lean`). `idoneal_completeness_of_GRH`, `isIdoneal_iff_of_GRH`.

## Part B: class number one (known, via GRH here; not a target, no further work planned)

Target: `ClassNumberProblem.StarkHeegnerStatement` (formal-conjectures). Cited inputs
(`Weinberger/ClassNumber/Hypotheses.lean`, tier H): `ClassNumberOneNorms` (class number one ⇒
a prime with an ideal of norm `p` is the norm of an integer) and `HeegnerClassNumberOne`.

1. `Weinberger/ClassNumber/Elementary.lean`: with `d = −n`,
   `false_of_two` (`n ≥ 3`, `n ≡ 1, 2 mod 4`: `u² + n v² = 2` is impossible) and
   `false_of_split3` (`n ≡ 3 mod 4`, prime `p`, `4p < n`, `p ∣ t² + t + (n+1)/4`: then
   `(2u + v)² + n v² = 4p` forces `v = 0`); `not_squarefree_of_four_dvd`.
2. GRH step: the same `exists_split_prime_of_GRH`, plus `exists_t_of_isSquare` (a root of
   `−n` mod `p` gives `t`) and `4p < n` from `p² < n`, `n ≥ 16`.
3. Finite range `n < 10^8`: `okB` (primes below 2000, `t < p`), ten `native_decide` chunks.
   The C prototype finds that exactly `n = 3, 7, 11, 19, 43, 67, 163` among `n ≡ 3 (mod 4)` lack
   a witness; the largest witness prime needed is 83.
4. `Weinberger/ClassNumber/Main.lean`: `starkHeegner_of_GRH`.

### What closing part B needs (Mathlib-side work, not started)

- `ClassNumberOneNorms`: identify `𝓞 (AdjoinRoot (X² − C d))` with `ℤ[ω]` (from
  `QuadraticAlgebra.Int.isIntegralClosure_iff` and an `AdjoinRoot ≃ₐ QuadraticAlgebra`
  isomorphism), compute `absNorm (p, t + ω) = p`, and use `Ideal.absNorm_span_singleton` and the
  norm formula on `QuadraticAlgebra`. Estimated 600–1100 lines.
- `HeegnerClassNumberOne`: Minkowski bound `(2/π)√|D| ≤ 8.13` for `D = −163`, so the primes
  2, 3, 5, 7 must be shown inert (or principal) in each of the nine fields, through the criteria
  in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`. Estimated 800–1500 lines, by
  comparison with `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`.

Neither needs any analytic input, so once both are proved part B becomes tier U.
