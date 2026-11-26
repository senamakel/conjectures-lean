# External Lean 4 formalisations: reusable intermediate lemmas (inventory, 2026-11-26)

Method: `gh api` repo metadata, recursive tree listings, raw fetches of selected files, and
`gh search repos`. Code search was rate-limited to zero during this run, so nothing here comes from
`gh search code`. Statements below are quoted from the files with `path:line` on each repo's
default branch as fetched today. "file sorry-free" means `grep -w sorry` found nothing in that one
file. **No `#print axioms` was run**, so transitive sorry-freeness is unverified unless the repo's
README claims completion; such items carry the tag (transitive: unverified). Nothing was built.

Workspace pin for comparison: Lean `v4.36.0`, Mathlib `fc4f59e5`.

---

## 1. PrimeNumberTheoremAnd (PNT+)

- Repo: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd (branch `main`, pushed 2026-11-24)
- Toolchain `leanprover/lean4:v4.36.0`, Mathlib `fc4f59e577`: **the same pin as this workspace**,
  so it could be a direct lake dependency with no port.
- Licence Apache-2.0. Other deps: `Architect` (blueprint), `LeanCert` (used by the Ramanujan files).
- README (2026-08): the IEANTN material under `PrimeNumberTheoremAnd/IEANTN/` is being moved to
  `teorth/IEANTN` (section 1b) and will be trimmed here.
- Status: `MediumPNT`, `StrongPNT`, `Consequences`, `BrunTitchmarsh`, `IEANTN/Mertens`,
  `IEANTN/Erdos392`, the Selberg sieve and the Hadamard files are file sorry-free. The
  explicit-estimate summaries are **not**: `IEANTN/SecondarySummary.lean` has 7 `sorry`
  (e.g. `theorem_1_theta`, `theorem_1_psi`, `has_prime_in_interval`, `theorem_1_4`),
  `IEANTN/Dusart.lean` has 33, `IEANTN/Buthe.lean` 8, `IEANTN/ZetaSummary.lean` 9, `FKS2.lean` 2,
  `Goldbach.lean` 2 (`richstein_goldbach`, `e_silva_herzog_piranian_goldbach`).

Reusable lemmas:

1. `StrongPNT` (`PrimeNumberTheoremAnd/StrongPNT.lean:2922`), file sorry-free (transitive: unverified)
   ```lean
   theorem StrongPNT : ∃ c > 0,
       (ψ - id) =O[atTop]
         fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
   ```
   Feeds: any unconditional input that needs PNT with de la Vallée Poussin error, but with a
   non-explicit `c`.
2. `ZeroInequality` (`StrongPNT.lean:2235`): the classical zero-free region, constant existential
   ```lean
   theorem ZeroInequality : ∃ (E : ℝ), E ∈ Ioo (0 : ℝ) (1 / 14 : ℝ) ∧
       ∀ (ρ : ℂ), ζ ρ = 0 →
         ∀ (σ : ℝ), σ = ρ.re →
           ∀ (t : ℝ), t = ρ.im → |t| ≥ 2 →
             σ ≤ 1 - E / log |t| := by
   ```
   Feeds: the unconditional side of zero-density or short-interval arguments. It is not explicit,
   so it cannot replace a Mossinghoff–Trudgian constant.
3. `LogDerivZetaUniformLogSquaredBound` (`StrongPNT.lean:2847`)
   ```lean
   theorem LogDerivZetaUniformLogSquaredBound : ∃ (C : ℝ) (_ : 0 < C),
       ∀ (σ t : ℝ), 3 < |t| → σ ∈ Set.Ici (1 - F / Real.log |t|) →
         ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ (2 : ℝ) := by
   ```
   Feeds: contour-shift (Perron) arguments near `Re s = 1`.
5. `prime_between` (`Consequences.lean:1559`)
   `∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x` for each `ε > 0`.
6. `chebyshev_asymptotic_pnt` (`Consequences.lean:2453`): PNT in arithmetic progressions
   ```lean
   theorem chebyshev_asymptotic_pnt
       {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
       (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
         fun x ↦ x / q.totient := by
   ```
   Also `mu_pnt` (:1958, `∑ μ(n) = o(x)`), `lambda_pnt` (:2222, Liouville), `mu_pnt_alt` (:2403,
   `∑ μ(n)/n = o(1)`), `sum_mobius_div_self_le` (:1594, `|∑_{n<N} μ n / n| ≤ 1`).
7. `primesBetween_le` (`BrunTitchmarsh.lean:250`): an explicit Brun–Titchmarsh via the Selberg sieve
   ```lean
   theorem primesBetween_le (hz : 1 < z) :
       primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 := by
   ```
   Feeds: upper bounds for primes in short intervals or progressions (Erdős gap problems, the
   counting step in Linnik-type arguments). Generic sieve: `selberg_bound_simple`
   (`Mathlib/NumberTheory/Sieve/Selberg.lean:437`, quoted below) and `rem_sum_le_of_const`
   (`Sieve/SelbergBounds.lean:513`).
   ```lean
   theorem selberg_bound_simple :
       siftedSum (s := s.toBoundingSieve) ≤
         X / S +
           ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
   ```
8. Mertens (`IEANTN/Mertens.lean`, file sorry-free): `sum_prime_div_eq_log_log` (:2133)
   ```lean
   theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
       |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
   ```
   and `E₃.bound''` (:2424), Mertens' third theorem:
   ```lean
   theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   ```
   Also `M.eq` (:2259), the Meissel–Mertens constant as `γ + ∑' p, (log(1-1/p) + 1/p)`.
   Feeds: Robin/Nicolas-type and sieve-density arguments. robin-rh and nicolas-rh already carry
   their own Mertens estimates.
9. `zetaCounting_crude_majorant` (`Backlund/ZeroCountCrude.lean:1105`), file sorry-free
   ```lean
   theorem zetaCounting_crude_majorant :
       ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T →
         |riemannZeta.N T| ≤ A * T ^ (3/2 : ℝ) := by
   ```
   Crude and non-explicit. It is not the Backlund `N(T)` that schoenfeld-rh needs.
10. Hadamard factorisation of ξ (`Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean:482`)
    ```lean
    theorem completedRiemannZeta₀_hadamard_factorization_sequence
        (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
        ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
            Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
          Complex.canonicalProduct 1
            (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
    ```
    The general Hadamard theory sits in `Mathlib/Analysis/Complex/HadamardFactorization*.lean`.
    erdos-985 has its own. This is an alternative, on the same pin.
11. `borelCaratheodory_zero_closedBall` (`Mathlib/Analysis/Complex/BorelCaratheodory.lean:19`)
    ```lean
    public theorem borelCaratheodory_zero_closedBall {f : ℂ → ℂ} {M r R : ℝ}
        (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
        (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0 = 0)
        (hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
        ‖f z‖ ≤ 2 * M * r / (R - r) := by
    ```
12. Argument principle on rectangles (`RectangleArgumentPrinciple.lean:278`)
    ```lean
    theorem rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
        {f : ℂ → ℂ} {z w : ℂ}
        (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
        (hf : MeromorphicOn f (Rectangle z w))
        (hlog : MeromorphicOn (logDeriv f) (Rectangle z w))
        (hfinite_order : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
        (hno_boundary :
          Disjoint (RectangleBorder z w) (MeromorphicOn.divisor f (Rectangle z w)).support) :
        RectangleIntegral' (logDeriv f) z w =
          ∑ p ∈
            ((divisor_support_rectangle_finite f z w).toFinset),
              ((MeromorphicOn.divisor f (Rectangle z w)) p : ℂ) := by
    ```
    Feeds: an explicit `N(T)` (Backlund/Rosser) via the argument principle. That is the missing
    input schoenfeld-rh lists for Schoenfeld's `1/(8π)`.
13. Prime-in-interval bridge (`IEANTN/PrimeInInterval.lean:170`), file sorry-free
    ```lean
    lemma Eθ.numericalBound.hasPrimeInInterval {x₀ x h : ℝ} {ε : ℝ → ℝ}
        (hEθ : Eθ.numericalBound x₀ ε) (hh : 0 < h) (hx₀ : x₀ ≤ x) (hx : 0 < x)
        (hε : (2 * x + h) * ε x₀ < h) :
        HasPrimeInInterval x h := by
    ```
    Turns any `θ` error bound into a short-interval prime.
14. Erdős #392 (`IEANTN/Erdos392.lean:3021, 3137`), file sorry-free; imports `Consequences` only
    ```lean
    theorem Solution_2 (ε : ℝ) (hε : ε > 0) :
        ∀ᶠ n in .atTop, ∃ (t : ℕ) (a : Fin t → ℕ),
          ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n ^ 2 ∧
            t ≤ (n / 2) - n / (2 * Real.log n) + ε * n / Real.log n := by
    ```
15. Results that depend on sorried explicit tables (do not reuse as unconditional):
    `ramanujan_final` (`IEANTN/Ramanujan/Ramanujan.lean:2460`, `pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1)`
    for `x > exₐ`) uses `PT.corollary_1`, which rests on the sorried `PT.theorem_1`.
    `L_not_HA_of_ge` (`IEANTN/Lcm.lean:1668`, `¬HighlyAbundant (L n)` for `n ≥ 89693 ^ 2`) uses
    `Dusart.proposition_5_4a`; Dusart.lean has 33 sorries, and this dependency was not traced.
    `ramare_saouter_odd_goldbach` (`Goldbach.lean:166`) sits beside the sorried
    `richstein_goldbach` (:155). The reduction `even_to_odd_goldbach` (:106) is clean:
    ```lean
    theorem even_to_odd_goldbach (x₀ H Δ : ℕ)
        (hprime : ∀ x ≥ x₀, HasPrimeInInterval (x * (1 - 1 / Δ)) (x / Δ))
        (heven : even_conjecture H) (hodd : odd_conjecture (x₀ + 4)) :
        odd_conjecture ((H - 4) * Δ + 4) := by
    ```

## 1b. teorth/IEANTN (explicit-ANT dependency network; new canonical home)

- Repo: https://github.com/teorth/IEANTN (`main`, pushed 2026-11-23), Apache-2.0.
  Toolchain `v4.34.0-rc2`, Mathlib `71a80585ee`. 1073 Lean files.
- Model: each node states its conclusions as `def … : Prop` in `IEANTN/Nodes/<F>/<v>/Conclusions.lean`.
  Proofs live in separate lake projects under `Solutions/`, checked by Comparator. `STATE.md`
  (generated) lists 197 conclusions: 63 `lean-comparator`, 62 `literature`, 32 `numerical`,
  35 `none-yet`. A `lean-comparator` conclusion with 0 imports is an unconditional Lean theorem.
  With imports, it is a Lean proof of "imports ⇒ conclusion".
- Lean-verified with **0 imports** (per `STATE.md`): `Chebyshev.v1` (`psi_lower`, `psi_upper`,
  `psi_le_small`, `constant_bounds`), `FKS2.v2` (`proposition_13`, `theorem_3`), `CH2.v2`/`CH2.v3`,
  `PrimeInterval.v1`, `RosserSchoenfeld1962.v1/v7/v8`, `ZeroFreeHeight.v1`, `ZetaZeroes.v1`,
  `Lcm.v2`, `Erdos392.v1`, `Goldbach.v1` (the reductions).

Reusable statements (quoted from `Conclusions.lean`):

1. `Chebyshev.v1.psi_lower` / `psi_upper` (`IEANTN/Nodes/Chebyshev/v1/Conclusions.lean:72, 85`)
   ```lean
   def psi_lower : Prop :=
     ∀ x : ℝ, 30 ≤ x → a * x - 5 * log x + 5 ≤ Chebyshev.psi x
   def psi_upper : Prop :=
     ∀ x : ℝ, 30 ≤ x →
       Chebyshev.psi x ≤ 6 * a * x / 5 + (log (x / 5) / log 6) * (5 * log x - 5)
   ```
   with `a = (7/15) log 2 + (3/10) log 3 + (1/6) log 5`, `0.92129 ≤ a ≤ 0.92130`. These are
   unconditional explicit Chebyshev bounds, which `ψ ≤ 1.11x` users need.
   (`psi_upper_clean : ∀ x, 0 < x → ψ x ≤ 1.11 * x` has 1 import, a finite check below 11723.)
2. `FKS2.v2.theorem_3` (`FKS2/v2/Conclusions.lean:112`): the θ → π transfer for any admissible bound
   ```lean
   def theorem_3 : Prop :=
     ∀ Aθ B C R x₀ x₁ : ℝ, 0 < R → max (3 / 2) (1 + C ^ 2 / (16 * R)) ≤ B → 2 ≤ x₀ → 0 < Aθ →
       0 < C → C / (2 * Real.sqrt R) ≤ Real.sqrt (Real.log x₀) →
       max x₀ (Real.exp ((1 + C / (2 * Real.sqrt R)) ^ 2)) ≤ x₁ →
       HasClassicalBound Eθ Aθ B C R x₀ →
       HasClassicalBound Eπ ((1 + muAsymp Aθ B C R x₀ x₁) * Aθ) B C R x₁
   ```
   `proposition_13` (:96) is the ψ → θ transfer, taking a `ψ − θ ≤ a₁√x + a₂x^{1/3}`
   hypothesis. Feeds: turning any ψ bound (e.g. schoenfeld-rh's) into θ and π bounds.
3. `CH2.v1.corollary_1_2_psi` (`CH2/v1/Conclusions.lean:96`), from Chirre–Helfgott,
   arXiv:2512.15709. Lean-verified, 13 imports
   ```lean
   def corollary_1_2_psi : Prop :=
     ∀ T x : ℝ, (10 : ℝ) ^ (7 : ℕ) ≤ T → RiemannHypothesisUpTo T →
       max T ((10 : ℝ) ^ (9 : ℕ)) < x →
         |Chebyshev.psi x - x * mainFactor T| ≤ Real.pi / (T - 1) * x + CT T * Real.sqrt x
   ```
   and `corollary_1_3_psi` (:126): `|ψ x − x| ≤ π/(3·10^12)·x + 113.67·√x` for all `x ≥ 1`
   (3 imports). It is conditional on RH up to a height, so it fits the workspace's "verified-zeros"
   gap. Whether `CT T` grows slowly enough to recover Schoenfeld's `1/(8π)` under full RH is
   (unverified).
4. `CH2.v3.extremal_majorant` / `extremal_minorant` (`CH2/v3/Conclusions.lean:97, 119`),
   0 imports, Lean-verified. These are Graham–Vaaler / Beurling–Selberg band-limited extremal
   functions for the truncated exponential.
   ```lean
   def extremal_majorant : Prop :=
     ∀ lambda β : ℝ, lambda ≠ 0 → 1 < β → β ≤ 2 →
       ∃ φ : ℝ → ℂ,
         CH2.v2.IsBandLimited φ β ∧
         (∀ y : ℝ, CH2.v2.truncExp lambda y ≤ (𝓕 φ y).re) ∧
         φ 0 = ((1 / (1 - Real.exp (-|lambda|)) : ℝ) : ℂ) ∧
         ∫ y : ℝ, ((𝓕 φ y).re - CH2.v2.truncExp lambda y)
           = 1 / (1 - Real.exp (-|lambda|)) - 1 / |lambda|
   ```
   Feeds: the test-function half of a Guinand–Weil explicit formula. cramer-rh (`22/25`,
   Carneiro–Milinovich–Soundararajan) and ankeny-grh/lls-grh (Bach's `2`) both name this as
   their missing piece. The fit to those proofs is (unverified).
5. `ZeroFreeHeight.v1.classical_region_descends` (`ZeroFreeHeight/v1/Conclusions.lean:69`)
   ```lean
   def classical_region_descends : Prop :=
     ∀ R t₀ t₁ T : ℝ, 0 < R → Real.exp (2 / R) < t₀ → t₀ ≤ t₁ → t₁ ≤ T →
       RiemannHypothesisUpTo T → ClassicalZeroFreeRegion R t₁ → ClassicalZeroFreeRegion R t₀
   ```
6. `RosserSchoenfeld.v2.psi_error_b23` (`RosserSchoenfeld/v2/Conclusions.lean:33`): `RiemannHypothesisUpTo 1894438.5122 → ∀ x ≥ e^23, |ψ x − x| < 0.00020211 x`.
   `RosserSchoenfeld1962.v6.theorem_25`: `θ x ≤ ψ x < 1.2 a x + (3 log x + 5)(log x + 1)` for `x ≥ 1` (1 import).

## 2. Fermat's Last Theorem (ImperialCollegeLondon/FLT)

- Repo: https://github.com/ImperialCollegeLondon/FLT (`main`, pushed 2026-11-18), Apache-2.0.
  Toolchain `v4.35.0`, Mathlib `56a005855e`.
- Status: **FLT is not proved.** `FLT/Proof.lean:98` is `theorem B4_proof : B4 := sorry` (B4: the
  mod-p Galois representation of the Frey curve is reducible), and `flt` is derived from it.
  `FLT/Assumptions/` holds `axiom Mazur_statement` (`Mazur.lean:105`, torsion of `E(ℚ)` has
  `ncard ≤ 16`) and `axiom Odlyzko_statement` (`Odlyzko.lean:58`). `KnownIn1980s.lean:79` declares
  `axiom knownin1980s {P : Prop} : P`. Nothing that touches these is reusable as unconditional.
- What is genuinely proved (file sorry-free):
  1. Reductions: `B2_implies_B1`, `B3_implies_B2`, `B4_implies_B3` (`FLT/Proof.lean`).
     `B4_implies_B3` uses `P.mazur`, i.e. the Mazur axiom. `FermatLastTheorem.of_p_ge_5`
     (`FLT/Basic/Lemmas.lean:38`):
     ```lean
     lemma FermatLastTheorem.of_p_ge_5 (H : ∀ p ≥ 5, p.Prime → FermatLastTheoremFor p) :
         FermatLastTheorem := by
     ```
  2. Frey curve invariants (`FLT/FreyCurve/Basic.lean:104`), e.g.
     `lemma Δ (P : FreyPackage) : P.freyCurve.Δ = (P.a*P.b*P.c)^(2*P.p) / 2 ^ 8`.
  3. Dickson's classification (`FLT/Slop/PGL2/FiniteSubgroups/DicksonClassification.lean:54`),
     file sorry-free, ported from a separate project ("Slop" directory) (transitive: unverified)
     ```lean
     theorem dickson_classification (G : Subgroup (PGLOf (K p))) [Finite G] :
         (IsCyclic G) ∨
         (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
         (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
         (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
         (Nonempty (G ≃* alternatingGroup (Fin 5))) ∨
         (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
           (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
           Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
         (∃ m : ℕ, m ≥ 1 ∧
           Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨ …
     ```
     (`p` odd prime, `K p` = `𝔽̄_p`.) Feeds: image-of-Galois arguments, Serre-type open-image
     questions, and the "large image" step in Artin-type problems.
  4. Haar characters on adeles (`FLT/HaarMeasure/HaarChar/AdeleRing.lean:70, 221`), e.g.
     `MeasureTheory.ringHaarChar_adeles_rat`, `NumberField.AdeleRing.units_mem_ringHaarCharacter_ker`
     (the product formula in Haar form). Feeds: adelic volume and Tate-thesis style inputs.

## 3. Carleson (fpvandoorn/carleson)

- Repo: https://github.com/fpvandoorn/carleson (`master`, pushed 2026-11-24), Apache-2.0.
  Toolchain `v4.36.0-rc1`, Mathlib `d88814353f`.
- Status (README): `classical_carleson` (continuous `2π`-periodic `f`) is complete and checked by
  `#print axioms`. The `Lᵖ` version `carleson_hunt` still depends on `sorry`. `Challenge.lean` has
  3 intentional `sorry`s (comparator challenge).

Reusable lemmas (all file sorry-free):

1. `classical_carleson` (`Carleson/Classical/ClassicalCarleson.lean:131`)
   ```lean
   theorem classical_carleson {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)) :
       ∀ᵐ x, Tendsto (S_ · f x) atTop (𝓝 (f x)) := by
   ```
2. `exists_hasStrongType_real_interpolation` (`Carleson/ToMathlib/RealInterpolation/Main.lean:1433`):
   Marcinkiewicz interpolation, including the off-diagonal case
   ```lean
   theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
       [TopologicalSpace E₁] [ESeminormedAddMonoid E₁]
       [TopologicalSpace E₂] [ContinuousENorm E₂]
       (hp₀ : p₀ ∈ Ioc 0 q₀) (hp₁ : p₁ ∈ Ioc 0 q₁) (hq₀q₁ : q₀ ≠ q₁)
       {C₀ C₁ A : ℝ≥0} (hA : 1 ≤ A) (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
       (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
       (hmT : ∀ f, MemLp f p μ → AEStronglyMeasurable (T f) ν)
       (hT : AESubadditiveOn T (fun f ↦ MemLp f p₀ μ ∨ MemLp f p₁ μ) A ν)
       (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁) :
       HasStrongType T p q μ ν (C_realInterpolation p₀ p₁ q₀ q₁ q C₀ C₁ A t) := by
   ```
3. Hardy–Littlewood maximal weak (1,1) on doubling spaces (`Carleson/ToMathlib/HardyLittlewood.lean:206`)
   ```lean
   theorem hasWeakType_maximalFunction_one [TopologicalSpace ε] [BorelSpace X] [SeparableSpace X] :
       HasWeakType (maximalFunction (ε := ε) μ 𝓑 c r 1) 1 1 μ μ (A ^ 2) := by
   ```
   and `hasWeakType_maximalFunction_equal_exponents` (:324).
4. Calderón–Zygmund weak (1,1) from an L² bound (`Carleson/TwoSidedCarleson/WeakCalderonZygmund.lean:1794`)
   ```lean
   theorem czOperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
       (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
       HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := fun f hf ↦ by
   ```
5. Truncated Hilbert transform L² bound (`Carleson/Classical/HilbertStrongType.lean:988`)
   ```lean
   lemma Hilbert_strong_2_2 ⦃r : ℝ⦄ (hr : 0 < r) :
       HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts 4) := by
   ```
6. Van der Corput, first-derivative form with Lipschitz amplitude (`Carleson/Classical/VanDerCorput.lean:53`)
   ```lean
   lemma van_der_Corput {a b : ℝ} (hab : a ≤ b) {n : ℤ} {φ : ℝ → ℂ} {B K : ℝ≥0}
       (h1 : LipschitzOnWith K φ (Ioo a b)) (h2 : ∀ x ∈ Ioo a b, ‖φ x‖ ≤ B) :
       ‖∫ x in a..b, exp (I * n * x) * φ x‖ ≤
        2 * π * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
   ```
   Feeds: oscillatory-integral bounds, a weak relative of exponential-sum estimates.
   `holder_van_der_corput` (`Carleson/HolderVanDerCorput.lean:508`) is the metric-space version.

## 4. PFR (teorth/pfr)

- Repo: https://github.com/teorth/pfr (`master`, pushed 2026-11-23), Apache-2.0.
  Toolchain `v4.37.0-rc1`, Mathlib `c47f9ad906`.
- Status: headline files sorry-free. The README says the 6 `sorry`s in `PFRPalomar/Challenge.lean`
  are deliberate. The README also says a Liao refinement (exponent 9) is in progress; the repo
  has exponent 11 (`PFR_conjecture_improv`).

1. `PFR_conjecture` (`PFR/Main.lean:261`), with `K^12`. `PFR_conjecture_improv` (`PFR/ImprovedPFR.lean:953`):
   ```lean
   theorem PFR_conjecture_improv {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
       {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
       (hA : Nat.card (A + A) ≤ K * A.ncard) :
       ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
         Nat.card c < 2 * K ^ 11 ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
   ```
2. `torsion_PFR` (`PFR/TorsionEndgame.lean:974`): bounded torsion
   ```lean
   theorem torsion_PFR {G : Type*} [AddCommGroup G] {m : ℕ} (hm : m ≥ 2)
       (htorsion : ∀ x : G, m • x = 0) {A : Set G} (Afin : A.Finite) {K : ℝ} (h₀A : A.Nonempty)
       (hA : Nat.card (A + A) ≤ K * A.ncard) :
       ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
         Nat.card c < m * K ^ (256 * m ^ 3 + 1) ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
   ```
3. `weak_PFR_int_sumset` (`PFR/WeakPFR.lean:1055`): torsion-free `ℤ^d`
   ```lean
   theorem weak_PFR_int_sumset
       {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
       {A : Set G} (hA : A.Finite) (hnA : A.Nonempty) {K : ℝ}
       (hAK : Nat.card (A + A) ≤ K * Nat.card A) :
       ∃ A' ⊆ A, Nat.card A' ≥ K ^ (-34 : ℝ) * Nat.card A ∧
         AffineSpace.finrank ℤ A' ≤ (80 / log 2) * log K := by
   ```
   (`weak_PFR_int` :1025 is the difference-set version with `K^(-17)` and `40/log 2`.)
   Feeds: problems needing "small doubling ⇒ dense in a low-dimensional piece" over ℤ
   (sum-product, Erdős–Szemerédi-type, structure of sets with few sums).
4. `homomorphism_pfr` (`PFR/HomPFR.lean:75`) and `approx_hom_pfr` (`PFR/ApproxHomPFR.lean:37`)
   ```lean
   theorem homomorphism_pfr (f : G → G') (S : Set G') (hS : ∀ x y : G, f (x+y) - (f x) - (f y) ∈ S) :
       ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ Nat.card S ^ 10 ∧ ∀ x : G, (f x) - (φ x) ∈ T := by
   theorem approx_hom_pfr (f : G → G') (K : ℝ) (hK : K > 0)
       (hf : K⁻¹ ≤ Finset.dens {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}) :
       ∃ (φ : G →+ G') (c : G'), Nat.card {x | f x = φ x + c} ≥ Nat.card G / (2 ^ 144 * K ^ 122) := by
   ```
   (`G`, `G'` are elementary abelian 2-groups.) Feeds: polynomial-Bogolyubov and inverse-`U³`
   arguments over `𝔽₂ⁿ`, and quasi-homomorphism rigidity.
5. Entropy toolkit (`PFR/ForMathlib/Entropy/RuzsaDist.lean`): `rdist_triangle` (:443),
   `kaimanovich_vershik` (:1105), `ent_bsg` (:1157, entropic Balog–Szemerédi–Gowers):
   ```lean
   lemma kaimanovich_vershik {X Y Z : Ω → G} (h : iIndepFun ![X, Y, Z] μ)
       (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
       [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
       H[X + Y + Z ; μ] - H[X + Y ; μ] ≤ H[Y + Z ; μ] - H[Y ; μ] := by
   lemma ent_bsg [IsProbabilityMeasure μ] {A B : Ω → G} (hA : Measurable A) (hB : Measurable B)
       [Finite G] :
       (μ.map (A + B))[fun z ↦ d[A ; μ[|(A + B) ⁻¹' {z}] # B ; μ[|(A + B) ⁻¹' {z}]]]
         ≤ 3 * I[A : B; μ] + 2 * H[A + B ; μ] - H[A ; μ] - H[B ; μ] := by
   ```
   Multi-distance (`PFR/MoreRuzsaDist.lean`): `kvm_ineq_I/II/III`, `multiDist_nonneg`,
   `ent_of_sum_le_ent_of_sum`. Also `exists_isUniform_of_rdist_self_eq_zero`
   (`PFR/HundredPercent.lean:142`), the "100% inverse theorem".

## 5. Equational theories (teorth/equational_theories)

- Repo: https://github.com/teorth/equational_theories (`main`, pushed 2026-11-23), Apache-2.0.
  Toolchain `v4.29.1`, Mathlib `5e932f97dd`. 2512 files, 1232 of them under `Generated/`.
- Status: the general files read were sorry-free. `Conjectures.lean` is empty.
- Reusable general results (universal algebra for one binary operation):
  1. Birkhoff completeness and soundness (`equational_theories/Completeness.lean:160, 35`)
     ```lean
     theorem Completeness {α} {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊧ E) : Nonempty (Γ ⊢ E) :=
     theorem Soundness {α : Type*} {Γ : Ctx α} {E} (h : Γ ⊢ E) : Γ ⊧ E :=
     ```
     `FreeMagma.EvalFreeMagmaWithLawsUniversalProperty` (:204) gives the relatively free magma.
  2. Compactness: `derive.getAxiomsEnough` (`Compactness.lean`), a derivation uses finitely many axioms.
  3. `Sheffer_Equation345169` (`Sheffer.lean:37`) with `Equation345169_implies_Axiom1..3`
     (:44–159): a Boolean algebra under NAND satisfies law 345169, and that law implies the Sheffer
     axioms (single-axiom Boolean algebra).
- Feeds: other equational/implication problems (e.g. single-axiom questions for groups or
  lattices). Little connection to number theory.

## 6. Sphere packing (dims 8, 24) and kissing numbers

**6a. math-inc/Sphere-Packing-Lean**: https://github.com/math-inc/Sphere-Packing-Lean
(`main`, pushed 2026-04-07), Apache-2.0, `v4.28.0`, Mathlib `8f9d9cff6b`, 830 Lean files. The
README claims dimension 8 optimality, dimension 24 optimality, and uniqueness among periodic
packings in dimension 24, all complete. Headline files are sorry-free (transitive: unverified;
README claims complete). The upstream `thefundamentaltheor3m/Sphere-Packing-Lean`
(`v4.37.0-rc1`, Mathlib `31ce06eaad`) still has `SpherePacking.MainTheorem … := sorry` and
5 sorries in `CohnElkies/LPBound.lean` on its `main`.

1. `MainTheorem` (`SpherePacking/Dim24/MainTheorem.lean:35`)
   ```lean
   public theorem MainTheorem :
       SpherePackingConstant 24 = Dim24.LeechPacking.density ∧
         ∀ S : PeriodicSpherePacking 24,
           S.density = Dim24.LeechPacking.density → Dim24.IsometricToScaledLeech S := by
   ```
   Dim 8: `MainTheorem : SpherePackingConstant 8 = E8Packing.density` (`Dim8/MainTheorem.lean:27`).
2. Cohn–Elkies LP bound in **every dimension `d`** (`SpherePacking/CohnElkies/LPBound.lean:586`)
   ```lean
   public theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
     (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
       volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
   ```
   under section variables (:49–56) `f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)`, `f ≠ 0`, `f` and `𝓕 f`
   real, `hCohnElkies₁ : ∀ x, ‖x‖ ≥ 1 → (f x).re ≤ 0`, `hCohnElkies₂ : ∀ x, (𝓕 f x).re ≥ 0`.
   Feeds: any new sphere-packing upper bound in another dimension. Its single missing input is an
   admissible auxiliary function, which nobody can supply in closed form except in dims 1, 8, 24.
3. Poisson summation over a general lattice (`SpherePacking/CohnElkies/PoissonSummationGeneral.lean:293`)
   ```lean
   public theorem poissonSummation_lattice (f : SchwartzMap E ℂ) (v : E) :
       (∑' ℓ : L, f (v + (ℓ : E))) =
         (1 / ZLattice.covolume L) *
           ∑' m : dualLattice (d := d) L, …
   ```
   Feeds: theta-function and lattice-point counting (Gauss circle, Epstein zeta), and the Hecke
   continuation that artin-grh lists as optional.
4. Kissing configuration uniqueness in dim 24 (`SpherePacking/Dim24/Uniqueness/BS81/KissingUniqueness.lean:29`)
   ```lean
   public theorem kissing_configuration_unique_24_bs81
       (X : Set ℝ²⁴) :
       Uniqueness.RigidityClassify.CE.IsKissingConfiguration X →
         Set.ncard X = 196560 →
           ∃ e : ℝ²⁴ ≃ᵢ ℝ²⁴, e '' X = Uniqueness.RigidityClassify.CE.leechKissingVectors := by
   ```

**6b. Pendzoncymisio/kissing-number-lean**: https://github.com/Pendzoncymisio/kissing-number-lean,
Apache-2.0, `v4.35.0-rc2`, Mathlib `065356127b`. `Axioms.lean` requires the standard three.
`kissingNumber_three : IsGreatest kissingCounts 12` (`Solution.lean:26`) and
`neighbors_le_twelve (X : Finset E3) (hX : HardCore X) (z : E3) : (neighbors X z).card ≤ 12`
(:40), via Musin's inequalities (`KissingNumber/Musin.lean:853,856`: `musinH3_holds`, `musinH4_holds`).
Feeds: 3D contact-number and packing bounds, and Tammes-type problems (unverified fit).

## 7. Additive combinatorics: Kelley–Meka, cap set, Kakeya, unit fractions, Ramsey, regularity

**7a. LeanAPAP**: canonical repo is https://github.com/YaelDillies/apap (`YaelDillies/LeanAPAP`
redirects there), `master`, pushed 2026-11-23, Apache-2.0, `v4.37.0-rc1`, Mathlib `c47f9ad906`.
- Status: the finite-field case is proved. **The integer case is a `sorry`**:
  `APAP/Integer.lean:10`:
  ```lean
  theorem int :
      ∃ c > 0, ∃ C > 0, ∀ ⦃A : Finset ℕ⦄ ⦃N : ℕ⦄, A ⊆ range N → ThreeAPFree (α := ℕ) A →
        #A ≤ N / exp (c * log N ^ (12⁻¹ : ℝ)) := sorry
  ```
1. `ff` (`APAP/FiniteField.lean:511`), the Kelley–Meka finite-field bound
   ```lean
   public theorem ff (hq₃ : 3 ≤ q) (hq : q.Prime) (hA₀ : A.Nonempty) (hA : ThreeAPFree (α := G) A) :
       finrank (ZMod q) G ≤ 2 ^ 148 * 𝓛 A.dens ^ 9 := by
   ```
2. `chang` (`APAP/Prereqs/Chang.lean:177`), Chang's lemma
   ```lean
   lemma chang (hf : f ≠ 0) (hη : 0 < η) :
       ∃ Δ, Δ ⊆ largeSpec f η ∧
         #Δ ≤ ⌈changConst * exp 1 * ⌈𝓛 ↑(‖f‖_[1] ^ 2 / ‖f‖_[2] ^ 2 / card G)⌉₊ / η ^ 2⌉₊ ∧
         largeSpec f η ⊆ Δ.addSpan := by
   ```
3. `rudin_ineq` (`APAP/Prereqs/Rudin.lean:100`)
   ```lean
   lemma rudin_ineq (hp : 2 ≤ p) (f : G → ℂ) (hf : AddDissociated <| support <| cft f) :
       ‖f‖ₙ_[p] ≤ 4 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
   ```
4. `drc` (`APAP/Physics/DRC.lean:97`, dependent random choice), `sifting` (:199),
   `unbalancing` (`APAP/Physics/Unbalancing.lean:247`), and almost periodicity
   (`APAP/Physics/AlmostPeriodicity.lean`; lemma names like `lemma28_part_two`, the main
   statement not quoted: unverified).
5. `ap_in_ff'` (`APAP/FiniteField.lean:322`): density increment onto a subspace of codimension
   `≤ 2^32 𝓛α² 𝓛(εα)² ε⁻²`.
   Feeds: the integer Kelley–Meka bound itself (needs Bohr-set versions of 4–5), and Freiman-type
   bounds through almost periodicity, which the README names as a side goal.

**7b. Cap set.** There is no Ellenberg–Gijswijt file in Mathlib today (checked the recursive tree:
no `CapSet`/`cap_set`). The README cites the Lean 3 formalisation by Dahmen–Hölzl–Lewis. Kakeya over
finite fields: https://github.com/math-inc/KakeyaFiniteFields (no licence file, `v4.26.0-rc2`,
Mathlib `f9a332347e`), file sorry-free, `KakeyaFiniteFields/Main.lean:292`:
```lean
theorem kakeya_set_bound (n : ℕ) :
  ∃ C : ℝ, 0 < C ∧
    ∀ (F : Type*) [Field F] [Fintype F] (K : Set (Fin n → F)),
      IsKakeyaSet K → Nat.card K ≥ C * Fintype.card F ^ n :=
```
Steps `step1`–`step4` (:56–232) are the polynomial-method lemmas: `finrank_restrictTotalDegree_choose`
(:27) gives the dimension count of polynomials of bounded total degree. Feeds: polynomial-method
problems (joints, Nikodym, finite-field Kakeya-type questions).

**7c. Unit fractions (Bloom; Bloom–Mehta)**: https://github.com/b-mehta/unit-fractions is **Lean 3**
(`leanpkg.toml`: `lean_version = "leanprover-community/lean:3.42.1"`). No Lean 4 port found by repo
search. Skipped.

**7d. Exponential Ramsey**: the Lean 3 repo `b-mehta/exponential-ramsey` has a Lean 4 successor,
https://github.com/b-mehta/ExponentialRamsey (`master`, pushed 2026-08-12, no licence,
`v4.29.0-rc6`, Mathlib `ce78b47018`). File sorry-free, `ExponentialRamsey/MainResults.lean:88`:
```lean
theorem exponential_ramsey_improvement : ∃ ε > 0, ∀ k, (ramseyNumber ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
```
Also `ramseyNumber_binomial_bound` (:58), `ramseyNumber_power_bound` (:61), `ramseyNumber_lower_bound`
(:80, `√2^k ≤ R(k,k)` for `k ≥ 2`), and the book-algorithm lemmas `four_one'`, `four_three`,
`four_four_red/blue_density/degree` (`Section4.lean:795–992`). Feeds: off-diagonal `R(k, l)` bounds
and other book-algorithm applications.

**7e. Szemerédi regularity and friends in Mathlib** (`master`, file sorry-free):
`szemeredi_regularity` (`Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean:76`),
`triangle_removal` (`…/Triangle/Removal.lean:162`), `corners_theorem` and `roth_3ap_theorem_nat`
(`Mathlib/Combinatorics/Additive/Corner/Roth.lean:79, 158`), `rothNumberNat_isLittleO_id` (:189):
```lean
theorem szemeredi_regularity (hε : 0 < ε) (hl : l ≤ card α) :
    ∃ P : Finpartition univ,
      P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ bound ε l ∧ P.IsUniform G ε := by
```
Also in the Mathlib tree: `CauchyDavenport.lean`, `ErdosGinzburgZiv.lean`, `PluenneckeRuzsa.lean`,
`RuzsaCovering.lean`, `Extremal/RuzsaSzemeredi.lean`, `SetFamily/KruskalKatona.lean`,
`SimpleGraph/Extremal/Turan*.lean`, `NumberTheory/SelbergSieve.lean`,
`NumberTheory/LSeries/PrimesInAP.lean` (Dirichlet's theorem; declaration name not checked),
`NumberTheory/Bertrand.lean`, `NumberTheory/Chebyshev.lean`.

## 8. Probability and analysis collections

**8a. Brownian motion**: https://github.com/RemyDegenne/brownian-motion (`master`, pushed 2026-11-10),
Apache-2.0, `v4.36.0-rc2`, Mathlib `6135ffb78e`.
- Status: construction and Hölder continuity are file sorry-free. The law of the iterated logarithm
  (`Gaussian/IteratedLogarithm.lean:346`, `IsBrownianReal.ae_limsup_div_sqrt_log_log_eq_one`)
  rests on two sorries: `IsBrownianReal.reflection` (:34, "needs strong Markov property") and
  `IsStandardGaussian.tail` (:39, Gaussian tail asymptotics). `DoobMeyer.lean` has 1 sorry and
  `Komlos.lean` 2.
1. `memHolder_brownian` (`Gaussian/BrownianMotion.lean:436`)
   ```lean
   lemma memHolder_brownian (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
       ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (brownian · ω) U :=
   ```
2. `covariance_brownian` (:479, `cov[brownian s, brownian t; gaussianLimit] = min s t`),
   `hasIndepIncrements_brownian` (:482).
3. Kolmogorov–Chentsov (`Continuity/KolmogorovChentsov.lean`): `modification_holderModification`
   (:1129), `exists_modification_of_edist_modification` (:167). Chaining: `edist_chainingSeq_le`,
   `iSup_edist_rpow_le_iSup_edist_chainingSeq` (`Continuity/Chaining.lean:218, 301`).
   Feeds: generic chaining or Dudley bounds for random processes, and continuity of random
   multiplicative-function models (unverified fit).

**8b. teorth/analysis**: https://github.com/teorth/analysis, Apache-2.0, "A Lean companion to
Analysis I". These are textbook exercises, partly sorried by design. Nothing reusable here (not inspected further).

**8c. Other analytic-NT collection found**: https://github.com/math-inc/RiemannHypothesisCurves
(no licence, `v4.26.0-rc2`), file sorry-free, generated by an autoformalisation agent.
`RiemannHypothesisCurves/RiemannHypothesisHEC.lean:573`:
```lean
theorem riemann_hypothesis_hec
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) :
    |((q : ℝ) - (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ))|
      < (5 : ℝ) * (f.natDegree : ℝ) * Real.sqrt (q : ℝ) :=
```
This is equivalent to a Weil bound `|∑_x χ₂(f(x))| < 5m√q` for the quadratic character
(Stepanov's method). Feeds: Burgess-type bounds for the least quadratic non-residue, runs of
consecutive quadratic residues, Paley-graph clique and independence bounds, and character-sum
inputs for Erdős problems on residues. In the workspace it is a candidate route to an
**unconditional** least-non-residue bound, as a companion to ankeny-grh/lls-grh (unverified fit).
`math-inc/strongpnt` (`v4.21.0`) is an older StrongPNT snapshot, superseded by PNT+.

## 9. Other: empty hexagon, Keller, Schur, Erdős-problem collections

- **Empty hexagon** (Heule–Scheucher `h(6) = 30`): https://github.com/bsubercaseaux/EmptyHexagonLean
  (`main`, no licence, `lean-toolchain` lives under `Lean/`, not read). `Lean/Geo/Hexagon/TheMainTheorem.lean:11`
  is proved **from a hypothesis** `variable (unsat_6hole_cnf : (Geo.hexagonCNF (rlen := 30-1) (holes := true)).isUnsat)`,
  i.e. the SAT result is an assumption, discharged outside Lean by a verified DRAT checker:
  ```lean
  theorem hole_6_theorem : ∀ (pts : Finset Point),
      Point.SetInGenPos pts → pts.card = 30 → HasEmptyKGon 6 pts := by
  ```
  `gon_theorem (unsat : (Geo.gonCNF k (r+2)).isUnsat) : gonNumber k ≤ r + 3`
  (`Lean/Geo/Gon/TheMainTheorem.lean:9`) is the convex-k-gon (Erdős–Szekeres) version, again
  conditional on a CNF being unsat. The symmetry breaking (`Geo.Canonicalization.SymmetryBreaking`)
  and `σHasEmptyKGon_iff_HasEmptyKGon` are reusable for other point-set Ramsey encodings.
  Related: `CuteSurtr/erdos-szekeres-lean` (not inspected).
- **Keller dimension 7**: no Lean repo found (repo search "keller lean", "keller graph").
- **Schur number 5**: no Lean proof found. `BigO-Hunter/schur-number-8-lean` claims a kernel-checked
  lower bound `S(8) ≥ 5372` (README only: unverified). `jeffchen006/Schur-Number-6` has no description.
- **Erdős-problem proof collections (2026)**:
  - https://github.com/math-inc/Erdos1196 (Apache-2.0, `v4.30.0-rc1`), file sorry-free,
    `PrimitiveSetsAboveX/Main.lean:53`:
    ```lean
    theorem mainTheorem :
        ∃ C : ℝ, ∃ x₀ : ℕ,
          ∀ ⦃x : ℕ⦄, x₀ ≤ x →
            ∀ {A : Set ℕ}, PrimitiveSet A → A ⊆ Set.Ici x →
              Summable (A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ)))) ∧
                (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
                  1 + C / Real.log (x : ℝ) := by
    ```
    `erdos_1196` (`FormalConjecturesErdos1196.lean:69`) is the formal-conjectures statement. Its
    `PreliminariesMertens.lean` is another Mertens source. Feeds: other primitive-set problems
    (Erdős primitive-set conjecture variants, translated primitive sets).
  - https://github.com/cadamcat/hypercube-ramsey-lean4 (Apache-2.0, `v4.34.1`, 752 Lean files):
    README states `theorem erdos_181 : ∃ C > (0 : ℝ), ∀ n : ℕ, (diagonalGraphRamsey (hypercube n) : ℝ) ≤ C * 2 ^ n`
    against formal-conjectures `9d259649` (name from README only: unverified).
  - https://github.com/davidturturean/erdos-870 (Apache-2.0, `v4.30.0-rc2`): a negative answer to
    Erdős 870 (additive bases with no minimal subbasis). README says sorry-free and axiom-clean
    (unverified here).
  - https://github.com/BruceLoveLee000/erdos-lean-proofs (Apache-2.0, `v4.33.1`): Erdős 881
    (case `k = 2`) and 1139 (README only: unverified).
  - https://github.com/math-inc/FrontierMathOpen-Hypergraphs (Apache-2.0, `v4.28.0`):
    `H(n) ≥ (26/25) k_n` for `n ≥ 15` (README only).
  - https://github.com/google-deepmind/formal-conjectures (2199 Lean files): statements, with
    `formal_proof` attributes. These could not be counted because code search was rate-limited.

---

## Cross-cutting notes for this workspace

- **Same pin**: PNT+ uses Lean `v4.36.0` and Mathlib `fc4f59e5`, exactly the workspace pin. Its
  Brun–Titchmarsh, Selberg sieve, Mertens, PNT-in-AP, Hadamard, Borel–Carathéodory and
  rectangle argument principle can be required directly. Everything else needs a port.
- **Explicit-estimate trust**: PNT+'s `IEANTN/*Summary*`, `Dusart`, `Buthe`, `FKS2` files contain
  sorries. Use IEANTN's 0-import `lean-comparator` nodes, or state the input as a tier-H
  hypothesis, as the workspace rules require.
- **Not new mathematics**: every headline above is a published theorem. Using any of them as an
  input does not change a repo's literature label.
