# Plan: the unconditional reduction Bach ⇒ Miller

Goal: prove, with no extra hypotheses beyond `BachSubgroupBound c`,

* `Miller.miller_of_bach : BachSubgroupBound c → MillerStatement c`
* `Miller.prime_iff_of_bach : BachSubgroupBound c → Odd n → 1 < n → (n.Prime ↔ ∀ a, 0 < a → a < n → a ≤ c log² n → IsStrongProbablePrime n a)`
* an executable `Miller.millerTest : ℕ → Bool` with `millerTest n = true ↔ n.Prime` for odd `n > 1`
  under `BachSubgroupBound 2`.

`Miller/Statement.lean` keeps its definitions unchanged. The two theorem proofs move to
`Miller/Reduction.lean`; `Statement.lean` only fixes the definitions.

## Notation

For `n` odd, `n - 1 = 2^s d` with `s = (n-1).factorization 2 ≥ 1` and `d = (n-1)/2^s` odd.
A unit `u ∈ (ℤ/n)ˣ` is a *strong liar* if `u^d = 1` or `u^(2^r d) = -1` for some `r < s`.

## Files

1. `Miller/Basic.lean`
   * `sd` facts: `2^s * d = n - 1`, `Odd d`, `0 < s` for odd `n > 1`.
   * `isStrongProbablePrime_val_iff`: for a unit `u`, `IsStrongProbablePrime n u.val` is the liar
     condition on `u` in the unit group.
   * `pow_two_pow_eq_one`: in a ring without zero divisors, `x^(2^s) = 1 → x = 1 ∨ ∃ r < s, x^(2^r) = -1`.
   * `isStrongProbablePrime_of_prime`: a prime `p` is a strong probable prime to every base
     `0 < a < p` (Fermat + the square roots of 1 in a field are ±1).
2. `Miller/Liars.lean` — the key lemma
   `exists_proper_subgroup_liars : Odd n → 1 < n → ¬ n.Prime → ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ u, liar u → u ∈ H`.
   Split on `k = n.factorization p`, `p = n.minFac`:
   * (a) `k ≥ 2`, so `p² ∣ n`: `H = ker (u ↦ u^(n-1))`. The unit `1 + n/p` satisfies
     `(1 + n/p)^p = 1 + n = 1` because `(n/p)^2 = 0` in `ℤ/n`, and is `≠ 1`; since
     `gcd(p, n-1) = 1` it is not in `H`.
   * (b) `k = 1`: `n = p · m` with `gcd(p, m) = 1`, `p, m ≥ 3`. Let `r₀` be the greatest
     `r ≤ s - 1` with some unit `w`, `w^(2^r d) = -1` (`r = 0`, `w = -1` qualifies). Then
     `J = {u : u^(2^{r₀} d) = ±1}` is a subgroup containing every liar. Via
     `ZMod.chineseRemainder`, the unit `v ↔ (w mod p, 1 mod m)` has `v^(2^{r₀}d) ↔ (-1, 1)`,
     which is neither `1 ↔ (1,1)` nor `-1 ↔ (-1,-1)`. So `J ≠ ⊤`.
3. `Miller/Reduction.lean`
   * `miller_of_bach`: apply Bach to the subgroup from the key lemma; the unit `a ∉ H` gives the
     witness `a.val` (nonzero since `a` is a unit and `n > 1`).
   * `prime_iff_of_bach`: forward from `isStrongProbablePrime_of_prime`; backward by Bach applied
     to the same subgroup, which yields a unit with `1 ≤ val < n`.
4. `Miller/Test.lean`
   * `powMod` (binary exponentiation) with `(powMod b e m : ZMod m) = b^e`.
   * `sppBool n a` decides `IsStrongProbablePrime n a` (`s` computed with `Nat.maxPowDiv`).
   * `millerBound n = (Nat.log 2 n + 1)^2`, proved `≥ 2 log² n` using `log 2 < 0.7`.
   * `millerTest n = ∀ a ∈ [1, min(n-1, millerBound n)], sppBool n a`.
   * `millerTest_iff_prime : BachSubgroupBound 2 → Odd n → 1 < n → (millerTest n = true ↔ n.Prime)`.
   * `#guard` sanity checks: Carmichael numbers 561, 1105, 3215031751 rejected; primes accepted.
5. `Miller/Unconditional/README.md`: how to combine with `Ankeny.bach_of_GRH`.

## Rules

No new axioms, no `sorry` at the end, never edit the definitions in `Statement.lean`.
