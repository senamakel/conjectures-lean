# Status of branch `bach-sharp-gap` (paused 2026-11-26)

Goal: `SharpGap` (the sharp bound for `2^17 ≤ q < 5·2^49`) under GRH, and then
`sharp_of_GRH : DirichletLNonvanishingRightOfHalf → SharpSubgroupBound ∧ SharpGeneratorBound`.

## Done
- **Phase A** (`docs/GAP.md`, programs in `scripts/gap/`). An independent recount, written from
  the Lean budget definitions, finds **1,018,780** moduli in the gap that fail the c = 1.657 budget
  with blocks of relative width 2^-10. Computing each q's own x instead gives 1,015,321. The
  earlier estimate was about 1.25·10^6. Σq = 5.16·10^15. The largest failing modulus is
  9,814,524,629,910 = 2·3·5·…·29·37·41 ≈ 2^43.16. Every failing modulus is 44587-smooth.
- **Exhaustive check.** The sharp bound holds on all 1,018,780 failing moduli, with **no
  counterexample**. The worst ratio is g(q)/log² q = 0.4923 (q = 164220), and g(q) ≤ 113
  throughout. The Frattini test used for this agrees with BFS for every q < 1500.
- **`BachSharpGapCheck.lean`** (core Lean, precompiled; it builds):
  - `genCert q x` is the Frattini certificate. It does a trial-division factorisation, then for
    each prime ℓ | φ(Q_j) it finds echelon words and verifies them. It agrees with ankeny's BFS
    g(q) for every q < 1500.
  - `checkChunkG` is the kernel-enumeration block checker (the DFS described in GAP.md).
    `#eval` returns `true` on samples.
- **Measured timings** (compiled, `#eval`), each including about 0.8 s of startup:

  | range | time |
  |---|---|
  | [2^17, 2^18) | 9.8 s |
  | [2^24, 1.25·2^24) | 20.6 s |
  | [2^30, 2^30+2^24) | 3.0 s |
  | [2^36, 1.125·2^36) | 7.6 s |
  | [2^43, 2^43+2^37) | 1.3 s |
  | [2^49, 2^49+2^43) | 0.9 s |

  Costs: about 0.8 ms per failing modulus, and about 50 ms per block (mostly the exact rational
  Cesàro sum in `mkBDC`). The whole gap is estimated at 0.5 to 1 CPU-hour.

## Not done (no Lean proofs written yet)
Nothing new on the proof side. `SharpGap` is still open, and the README title and the
`Statement.lean` docstring fixes have not been made.

## Next steps (the order planned)
1. `BachSharp/Frattini.lean`:
   - DONE: Frattini lemma `BachSharp.frattini_top` (`H ⊔ (powMonoidHom ℓ).range = ⊤` for every
     prime ℓ implies `H = ⊤`; standard three axioms only).
   - OPEN: echelon lemma: kernels `K_i ⊇ G^ℓ`, words `h_i ∉ K_i` with `h_i ∈ K_k` for `k < i`, and
     `|G[ℓ]| ≤ ℓ^r`. The map `(Fin r → Fin ℓ) → G ⧸ G^ℓ` is injective (prime-order Bezout step),
     so it is bijective. Use `Subgroup.index_ker`, `card_mul_index` and `Subgroup.mem_sup`.
2. Torsion count (`BachSharp/Frattini.lean` and `BachSharp/Torsion.lean`, standard three axioms
   only, all DONE):
   - CRT injectivity: `BachSharp.card_torsion_units_mul_le`,
     `|(ℤ/mn)ˣ[ℓ]| ≤ |(ℤ/m)ˣ[ℓ]|·|(ℤ/n)ˣ[ℓ]|` for coprime `m n`.
   - Odd `p^e`: `BachSharp.card_torsion_units_odd_prime_pow_le` (at most `ℓ`, via
     `IsCyclic.card_pow_eq_one_le`; helper `torsion_card_cyclic_le`).
   - `2^e`: `BachSharp.card_torsion_units_two_pow_le` (the bounds 1, 2, 4; helper
     `torsion_card_sq_le_four`) and `BachSharp.card_torsion_units_two_pow_odd` (exactly 1 for odd ℓ).
3. Soundness of `powMod`, `isPrimeS`, `factOK`, `evalW` and `psiW`, giving
   `closure_eq_top_of_genCert : genCert q x = true → closure (smallUnits q x) = ⊤`.
4. `dfs_sound` with these invariants: rest primes are coprime to P, `rhoOK` gives sorted lists
   and ρ bounds, `lam8` is superadditive. Then `blockOKG_sound` (copy `blockOKC_sound`, change
   the per-modulus branch) and `checkChunkG_sound → GoodC (1657/1000) q`.
5. Chunks `BachSharp/Compute/G*.lean`, each under 5 min. Possibly use w = 6 above 2^44 to cut
   the block count; that still needs checking. Then `sharpGap_of_GRH` and `sharp_of_GRH`,
   `#print axioms`, and the README and docstring fixes.

## Constants and parameters
c = 1657/1000, m = 1024, w = 10, T = 4 (the cap on the number of multiples before direct
enumeration), λ(n) = ⌊log₂ n^8⌋, the bound `8·log₂R + 8`, SC = 2^32. x < 2000 holds throughout
the gap, so the prime table NP = 2000 is enough.

## Dead ends
- Factorisation-free CRT words (single powers s^{λ(R)}) fail: φ(Q) and λ(R) always share the
  prime 2.
- Certificate data emitted from C would be about 10^8 numbers, too large for Lean source. The
  checker searches for its certificates itself instead.

## Worktree note
`.lake/build` was copied from the old `worktrees/bach-sharp-grh` build, which has identical
sources, so `lake build BachSharp` only replays.
