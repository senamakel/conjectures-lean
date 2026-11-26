# Status (2026-11-26, paused on the owner's instruction)

## Proved
- `SunA243164.sunA243164_of_GRH_of_numerics (hGRH) (hnum : SieveNumerics 100000000)` (from before).
- `SunA243164.Numerics.sieveNumerics_10_8 : SieveNumerics 100000000` in `SunA243164/Numerics.lean`.
  It built with no errors and no `sorry`. After that build, four cosmetic edits were made to clear
  warnings: `push_neg` became `push Not`, `if_pos`/`if_neg` became `simp [h3F]`, and two unused
  arguments were dropped from `sieve_data`. The rebuild that would check those edits was stopped
  by the pause, so they are **not yet verified**.
- The fallback (finite range up to `2·10^8`) is **not needed**.

## Method (see the module docstring)
Choose `S = {ℓ ∣ P-1 : ℓ ≥ 5}` for `ω ≤ 14` and `S = ∅` for `ω ≥ 15`. Use
`x = π(P) ≥ P log 2 / log P` (Mathlib). The worst case is handled by an exchange lemma for
`Σ 1/ℓ` (no ordering of the prime factors is needed). Lower bounds for `P` come from `ω`
(erdos-985 `pow_card_primeFactors_mul_le`). In the no-sieve case, `(2^ω/θ_F)^4 ≤ 517576 (P-1)`.
The final polynomial inequality in `log P` against `P = P₀ e^u` is closed factor by factor with
`1 + t ≤ e^t`. Ratio `4U₀B²/(P₀ log 2)`, which must be `< 1`:

| case | P₀ | e | \|S\| ≤ | ratio |
|---|---|---|---|---|
| ω ≤ 8 | 10^8 | 1 | 7 | 0.322 |
| ω ≤ 8 | 10^8 | 2 | 6 | 0.754 (tightest: about 13% margin in √x) |
| ω = 9 | 223092871 | 1 / 2 | 8 / 7 | 0.259 / 0.643 |
| 10 ≤ ω ≤ 14 | 6469693231 | 1 / 2 | 13 / 12 | 0.112 / 0.300 |
| ω ≥ 15, no sieve | 614889782588491411 | – | – | 0.039 |

The parameter generator is in this session's scratchpad (`params.py`, `params2.py`). It is not
committed, but every constant is written in `Numerics.lean`.

## Next steps
1. `lake build SunA243164.Numerics` to confirm the cosmetic edits (about 1 minute). Revert them if they fail.
2. In `Main.lean`, add `import SunA243164.Numerics` and
   `theorem sunA243164_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) : SunA243164Statement :=
   sunA243164_of_GRH_of_numerics hGRH Numerics.sieveNumerics_10_8`, then run `#print axioms` (expected:
   the standard three plus `Compute.chunk_ok_*`). Add the module to `SunA243164.lean`.
3. In `Unconditional/SunA243164Unconditional.lean`, drop `hnum` and use `sunA243164_of_GRH LFunction_ne_zero_of_half_lt_re`.
   Update the comments in `scripts/check-unconditional.sh`.
4. README: final house shape (threshold table above, literature section, rule-10 caveat), and update `docs/PLAN.md`.

## Dead ends
None. One problem along the way: `nlinarith` with large contexts timed out, so those steps were
replaced by explicit `linarith` steps.
