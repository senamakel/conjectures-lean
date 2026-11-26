# Local lemma inventory: solved-conjectures (A) and formal-conjectures (B)

Read-only survey, 2026-11-26. Nothing was built and nothing was executed from the sources.

- A = `src/solved-conjectures` at `43152d52` (HEAD = `origin/main`), Lean `v4.35.0`, 6178 files under `lean/Conjectures/`.
- B = `src/formal-conjectures` at `9097e2f`, Lean `v4.33.1`.

The two toolchains differ, so moving any lemma across means a port.

## Checks done on the sources (grep only)

- A, `lean/`: no `sorry` in any `.lean` file, and no `axiom` or `opaque` declarations.
- A, the families cited below (Loneliness Four/Five/Small/Renault, FranklHighGirth/Large/Lopsided,
  HadamardLegendre, PomeranceSarkozyMertens, BabaiPath, ErdosGyarfasUniversal): no `native_decide`.
  Some finite certificates use `decide +kernel`.
- A's docs (`docs/lean-checkpoints-{1,2}.md`) report hosted `#print axioms` audits that allow only
  `propext`, `Classical.choice` and `Quot.sound`. I did **not** rerun them.
- A, remote branches `origin/lean/*`: every file they touch under `lean/Conjectures/` already exists
  on `origin/main`. The branches add nothing new.
- B, `FormalConjecturesForMathlib/`: 266 files, 870 theorems and lemmas, no `sorry`, no
  `axiom`/`opaque`. PROOFS.md forbids `native_decide` there.
- "proof has no sorry" below means the declaration's source has no `sorry`. It does not mean I
  printed its axioms.

---

# Part A: solved-conjectures, grouped by family

## A1. Lonely runner (Loneliness*, about 2,500 files)

**Headline** (CONTENTS.md and lean-status). The lonely-runner bound `1/(m+1)` is fully
Lean-proved for **every nonempty list of at most m = 5 distinct positive integer speeds**, so up to 6
runners including the stationary one.

- m ≤ 3 and m = 4 are proved by a gap theorem: below `2/9` the only four-speed sets are the
  multiples of `[1,2,3,4]` and `[1,3,4,7]`.
- m = 5 has two independent proofs: a Renault-style proof, and a finite modular proof that also
  classifies the tight cases `[1..5]` and `[1,3,4,5,9]`.
- Six speeds and more (m ≥ 6) are **not proved unconditionally**. The 6–8 speed spectra and
  classifications are conditional on explicit premises (`PrimitiveSixClassification`,
  `SporadicExhaustion`, `BoundedRootReduction`, `CanonicalPlaneCoverage`).
- **Only integer speeds are covered.** There is no real-speed or irrational-speed version and no
  real-to-integer reduction anywhere in A.

The common definitions are in `Loneliness.lean`. `distance x = |x - round x|`, and
`value ds = sSup (clearance ds '' Icc 0 1)`. `LonelyRunnerBound m` is defined at
`LonelinessCoalescenceValue.lean:103`:

```lean
def LonelyRunnerBound (m : ℕ) : Prop :=
  ∀ ds : List ℕ, ds ≠ [] → ds.Nodup →
    ds.length ≤ m → (∀ a ∈ ds, 0 < a) → (1 : ℝ) / (m + 1) ≤ value ds
```

Lemmas (all proofs free of `sorry`):

1. `Loneliness.Renault.five_speed_common_time`, `LonelinessFiveSpeedBound.lean:15`. Repeated speeds
   are allowed, and the proof discharges the four-speed input itself.
   ```lean
   theorem five_speed_common_time (v : Fin 5 → ℕ) (hpositive : ∀ i, 0 < v i) :
       ∃ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, (1 / 6 : ℝ) ≤ distance ((v i : ℝ) * t)
   ```
2. `Loneliness.Renault.five_speed_lonelyRunnerBound`, `LonelinessFiveSpeedBound.lean:19`, and
   `Loneliness.Modular.FiveRunner.five_runner_bound`, `LonelinessFiveRunnerTheorem.lean:40`.
   Two independent proofs of the same statement:
   `theorem ... : CoordinateSubspace.LonelyRunnerBound 5`.
3. `Loneliness.CoordinateSubspace.four_speed_gap` (`LonelinessFourSpeedGap.lean:11`, `: FourSpeedGap`)
   and `four_speed_below_gap_value` (line 15). `FourSpeedGap` is defined at `LonelinessPlaneGap.lean:10`:
   ```lean
   def FourSpeedGap : Prop :=
     ∀ ds : List ℕ, ds.length = 4 → ds.Nodup → (∀ a ∈ ds, 0 < a) →
       value ds < (2 / 9 : ℝ) →
       ∃ d : ℕ, 1 ≤ d ∧
         (ds.Perm ([1,2,3,4].map (fun a => d * a)) ∨
           ds.Perm ([1,3,4,7].map (fun a => d * a)))
   ```
4. `Loneliness.SmallRunner.lonelyRunnerBound`, `LonelinessSmallRunner.lean:89`:
   `theorem lonelyRunnerBound (m : ℕ) (hm : m ≤ 3) : CoordinateSubspace.LonelyRunnerBound m`.
5. `Loneliness.PairSum.exists_pair_sum_maximum`, `LonelinessMax.lean:166`. The maximum is attained
   at a time `k/(a+b)`:
   ```lean
   theorem exists_pair_sum_maximum (D : Finset ℕ) (hD : D.Nonempty)
       (hcard : 1 < D.card) (hpos : ∀ d ∈ D, 0 < d) :
       ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ ∃ k : ℕ, k ≤ a+b ∧
         ∀ u : ℝ, score D hD u ≤ score D hD ((k : ℝ)/(a+b : ℕ))
   ```
6. `Loneliness.Normalization.primitive_representative`, `LonelinessNormalization.lean:113`.
   Dividing by the gcd keeps the value:
   ```lean
   theorem primitive_representative (ds : List ℕ) (hne : ds ≠ [])
       (hpos : ∀ a ∈ ds, 0 < a) (hdistinct : ds.Nodup) :
       ∃ ns : List ℕ, ns.length = ds.length ∧ ns.Nodup ∧
         (∀ a ∈ ns, 0 < a) ∧ ns.foldr Nat.gcd 0 = 1 ∧ value ns = value ds
   ```
   Related: `Loneliness.CoordinateSubspace.lonelyRunnerBound_of_exact_length_primitive_lower`
   (`LonelinessRunnerBoundPadding.lean:65`, padding from exact length k to length ≤ k), and
   `value_le_of_list_subset` (line 52): `(hsub : ds ⊆ es) : value es ≤ value ds`.
7. `Loneliness.PrimeFiltering.prime_filtering`, `LonelinessPrimeFiltering.lean:28`. This is
   Barajas–Serra Lemma 2, and it is general (any index type, any prime):
   ```lean
   theorem prime_filtering {ι : Type*} {p m : ℕ} [Fact p.Prime]
       (s : Finset ι) (v level : ι → ℕ) (F : ι → Finset (ZMod p))
       (hlevel : ∀ i ∈ s, level i ≤ m)
       (hdiv : ∀ i ∈ s, p ^ level i ∣ v i)
       (hnext : ∀ i ∈ s, ¬ p ^ (level i + 1) ∣ v i)
       (hbudget : ∀ j ≤ m,
         (if j = m then 1 else 0) +
           ∑ i ∈ s.filter (fun i => level i = j), (F i).card < p) :
       ∃ a : ℕ, (a : ZMod p) ≠ 0 ∧
         ∀ i ∈ s, digit p m (a * v i) ∉ F i
   ```
   Consequences in `LonelinessPrimeFilteringCases.lean`:
   - `uniform_level_value` (:132): every speed has exact p-adic valuation j, so `1/p ≤ value ds`,
     for any number of speeds.
   - `one_seventh_of_three_below_max_valuation` (:201): at most 3 speeds per 7-adic level below
     the top level gives `1/7 ≤ value ds`.
8. `Loneliness.TwoInsertions.two_speed_interval_of_length`, `LonelinessTwoInsertionsMeasure.lean:147`.
   A measure argument for **real** speeds:
   ```lean
   theorem two_speed_interval_of_length (v w δ a b : ℝ)
       (hv : 0 < v) (hw : 0 < w) (hδ : 0 ≤ δ) (hhalf : δ < 1/2)
       (hab : a ≤ b) (hbound : 4*δ*(b-a)+2*δ/v+2*δ/w < b-a) :
       ∃ t ∈ Icc a b, δ ≤ distance (v*t) ∧ δ ≤ distance (w*t)
   ```
   Same idea for one speed: `exists_good_on_interval` (`LonelinessTwoInsertionsInterval.lean:19`).
   Arithmetic helper: `exists_coprime_near_half` (`LonelinessTwoInsertionsAccelerationArithmetic.lean:56`),
   `(hr : 4 ≤ r) : ∃ k, 2*k ≤ r ∧ r ≤ 2*k+4 ∧ Nat.Coprime r k`.
9. `Loneliness.TwoInsertions.goddyn_wong_two_insertions`, `LonelinessTwoInsertionsAccelerations.lean:71`:
   ```lean
   theorem goddyn_wong_two_insertions (p b c : ℕ) (m : ℕ → ℕ)
       (hp : 3 ≤ p) (hb : 0 < b) (hc : 0 < c) (h : GoddynWongCriterion p m) :
       ∃ t ∈ Set.Icc (1/(p+2 : ℝ)) (1/(p : ℝ)),
         1/(p+2 : ℝ) ≤ clearance (b::c::acceleratedBase p m) t
   ```
10. View obstruction for rational subspaces.
    `Loneliness.CoordinateSubspace.spaceValue_lower_of_runner_bound` (`LonelinessCoalescenceValue.lean:86`)
    turns a runner bound into a bound for a coordinate-free subspace; see also
    `coalescence_value_lower` (:107). The general linear-algebra step is
    `Loneliness.Coalescence.coalescing_hyperplane_avoiding` (`LonelinessCoalescenceAvoiding.lean:99`).
    ```lean
    theorem spaceValue_lower_of_runner_bound [Nonempty ι]
        (E : Submodule ℚ (ι → ℚ)) (hfree : CoordinateFree (realSpan E))
        (m : ℕ) (r : ℝ)
        (hrunners : ∀ ds : List ℕ, ds ≠ [] → ds.Nodup →
          ds.length ≤ m → (∀ a ∈ ds, 0 < a) → r ≤ value ds)
        (hcard : Fintype.card ι - Module.finrank ℝ (realSpan E) + 1 ≤ m) :
        r ≤ spaceValue (realSpan E)
    ```

Shifted lonely runner (Zhang Q8.5): only finite counterexample certificates for 18 ≤ n ≤ 57. No
general lemma.

## A2. Integer distance graphs, Motzkin densities, chromatic bounds

**Headline.**
- Carraher et al. Conjecture 38 is proved; Conjecture 39 is refuted (`ThreeDistanceGraph.*`).
- Babai spectra of paths are proved completely (Johnson–Kaya–Matzke).
- Oravcová–Soták for k = 5..8 distances is proved only *relative to* the unproved spectrum
  classifications R5–R8.
- Haralambis' three-difference theorem (Motzkin density = loneliness value for |D| = 3) is proved
  completely. It is a formalisation of a known result.

Lemmas:

1. `Loneliness.DistanceColoring.colorable_of_value`, `LonelinessDistanceColoring.lean:85`.
   This is the link from loneliness to colouring (Zhu's κ ⇒ χ):
   ```lean
   theorem colorable_of_value (ds : List ℕ) (q : ℕ) (hq : 0 < q)
       (hvalue : (1 : ℝ) / q ≤ value ds) : (graph ds).Colorable q
   ```
   Here `graph ds : SimpleGraph ℤ` with `Adj m n := m ≠ n ∧ (m - n).natAbs ∈ ds` (line 14).
   Combined with A1.2, every integer distance graph with at most 5 distances is 6-colourable.
2. `OravcovaSotak.distance_colorable_card_add_one`, `OravcovaSotakBounds.lean:45`:
   `(graph D).Colorable (D.toFinset.card+1)`. The finite version is `finite_coloring_exists` (:12).
3. `OravcovaSotak.nearTight_of_not_colorable`, `OravcovaSotakClassification.lean:106`:
   `(hk : 0 < k) (h : ¬(graph D).Colorable k) : NearTight k D`.
4. `Haralambis.three_difference_theorem`, `HaralambisTheorem.lean:35`:
   ```lean
   theorem three_difference_theorem (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
       Loneliness.Packing.density (speeds d) = Loneliness.value (speeds d) ∧
         ∃ i j : Fin 3, i ≠ j ∧ 0 < d i+d j ∧ ∃ A : Set ℤ,
           NonmixedGap.IsPeriodic A (d i+d j : ℕ) ∧
           Loneliness.Packing.Avoids (speeds d) A ∧
           NonmixedGap.upperDensity A = Loneliness.Packing.density (speeds d)
   ```
   `Packing.density ds` is the sup of the upper density of sets `A ⊆ ℤ` with `t + d ∉ A` for all
   `d ∈ ds` and `t ∈ A` (`LonelinessPacking.lean:10-14`).
5. `DistanceGraph.odd_cycle_optimal`, `DistanceGraphOddCycle.lean:89`. Exact Motzkin density for
   D = {1, 2l}:
   ```lean
   theorem odd_cycle_optimal (l : ℕ) (hl : 0 < l) :
       ∃ A : Set ℤ, IsPeriodic A (2*(l:ℤ)+1) ∧
         (∀ t ∈ A, t+1 ∉ A ∧ t+2*(l:ℤ) ∉ A) ∧
         upperDensity A = (l:ℝ)/(2*(l:ℝ)+1) ∧
         ∀ B : Set ℤ, (∀ t ∈ B, t+1 ∉ B ∧ t+2*(l:ℤ) ∉ B) →
           upperDensity B ≤ upperDensity A
   ```
   Also proved: `NonmixedGap.nonmixed_gap_density`, `SymmetricFourPoint.symmetric_four_point_densities`,
   `ThreeDistanceGraph.gap_five_classification` (`ThreeDistanceGraphTheorem.lean:53`,
   `gapDensity k 5=fiveValue k ∧ gapValue k 5=fiveValue k`) and `gap_seven_classification`.
6. `BabaiPathSpectrum.independent_card_bound` (`BabaiPathSpectrum.lean:47`), `modular_colorable`
   (:240) and `spectrum_eq_interval` (:307). `ValidDistances n D := D ⊆ Ico 1 n`.
   ```lean
   theorem independent_card_bound (n : ℕ) (D : Finset ℕ)
       (hD : ValidDistances n D) (S : Finset (Fin n))
       (hS : ∀ u ∈ S, ∀ v ∈ S, ¬(distanceGraph n D).Adj u v) :
       S.card + D.card ≤ n
   theorem modular_colorable (n s : ℕ) (D : Finset ℕ) (hs : 0 < s)
       (hD : D ⊆ nonmultiples n s) : (distanceGraph n D).Colorable s
   theorem spectrum_eq_interval (n k : ℕ) (hn : 2 ≤ n) (_hk : 1 ≤ k) (hkn : k < n) :
       spectrum n k = Set.Icc ⌈(n : ℚ) / (n-k : ℕ)⌉₊ (k+1)
   ```

Conditional results (not usable as they stand):
- `triangle_free_five_distance_colorable_of_exhaustion` (`LonelinessFiveDistanceGraph.lean:9`) needs
  `SporadicExhaustion`.
- `six_triangle_free_colorable` (`LonelinessHigherTriangleConsequences.lean:218`) needs
  `PrimitiveClassifies 6 SixCandidate`.

Circular chromatic index (CircularIndex*, CircularInsertion*): these are mostly explicit circulant
families and certificates for exact values. I did not find a lemma general enough for other problems
(not mined in depth).

## A3. Frankl / union-closed (Frankl*, about 1,150 files)

**Headline.**
- *Frankl high girth.* Every point has frequency ≥ 0.518208 among the distinct unions of a
  k-uniform generating family (k ≥ 3), with every point in exactly 3 generators and incidence girth
  ≥ 16. Fully proved.
- *Frankl large.* The same with ≥ 657/1000 for k ≥ 15 and pairwise intersections of size ≤ 1. Fully
  proved.
- The cyclic span-four theorem is incomplete. `FranklSmall*` (918 files) holds the cyclic-word data
  for it.

Lemmas:

1. `FranklHighGirth.high_girth_generator_frequency`, `FranklHighGirthTheorem.lean:47`:
   ```lean
   theorem high_girth_generator_frequency [DecidableEq ι]
       (gen : ι → Finset α) (k : ℕ) (hk : 3 ≤ k)
       (hsize : ∀ i, (gen i).card = k)
       (hregular : ∀ a, (Frankl.Large.incident gen a).card = 3)
       (hg : NoShortCycle (incidenceGraph (fun i => (gen i : Set α))) 16) (a : α) :
       518208 * (FranklLocal.family (univ.image gen)).card ≤
         1000000 * ((FranklLocal.family (univ.image gen)).filter (fun U => a ∈ U)).card
   ```
2. `Frankl.Large.large_generator_frequency`, `FranklLargeTheorem.lean:28`. Hypotheses: `15 ≤ k`,
   uniform size, 3-regular, `(G e ∩ G f).card ≤ 1`. Conclusion: `657 * card ≤ 1000 * card(filter a ∈)`.
3. `Frankl.Lopsided.conditional_card_bound`, `FranklLopsided.lean:105`. This is a **finite,
   counting-measure lopsided Lovász Local Lemma** and does not depend on Frankl at all:
   ```lean
   theorem conditional_card_bound (bad : ι → Finset Ω) (neighbors : ι → Finset ι)
       (D : ℕ) {p x : R} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
       (hdegree : ∀ i, (neighbors i).card ≤ D)
       (hp : p ≤ x * (1 - x) ^ D)
       (hlopsided : ∀ i t, i ∉ t → Disjoint t (neighbors i) →
         ((bad i ∩ avoid bad t).card : R) ≤ p * ((avoid bad t).card : R)) :
       ∀ s i, i ∉ s →
         ((bad i ∩ avoid bad s).card : R) ≤ x * ((avoid bad s).card : R)
   ```
   Companions: `query_card_bound` (:163) and `avoid_union_card_lower` (:68).
4. `Frankl.Lopsided.sliced_harris_lopsided`, `FranklLopsidedHarris.lean:78`. A Harris/FKG inequality
   on the cube:
   ```lean
   theorem sliced_harris_lopsided (upper : Finset (Finset α))
       (lower : β → Finset (Finset α))
       (hupper : IsUpperSet (upper : Set (Finset α)))
       (hlower : ∀ b, IsLowerSet (lower b : Set (Finset α))) :
       (2 * 2 ^ Fintype.card α) * (sliceBad upper ∩ sliceAvoid lower).card ≤
         upper.card * (sliceAvoid lower).card
   ```
5. `FranklLocal.weighted_local_certificate_abundance` (`FranklLocalWeights.lean:113`) and
   `abundant_of_total_imbalance` (:66). This is the Poonen-style weighted-certificate criterion:
   ```lean
   theorem weighted_local_certificate_abundance {G : Finset (Finset α)}
       {W : Finset α} {w : α → ℝ}
       (hw : ∀ x ∈ W, 0 ≤ w x) (hpos : ∃ x ∈ W, 0 < w x)
       (hcert : WeightCertificate G W w) :
       ∃ x ∈ W, (family G).card ≤ 2*((family G).filter (fun U => x ∈ U)).card
   ```
6. `FranklLocal.local_certificate_transfer`, `FranklLocalEnumeration.lean:99`. A certificate depends
   only on the local generators:
   `(hlocal : localGenerators G W=localGenerators H W) (hc : certificateCheck H W w=true) : ∃ x ∈ W, Abundant (family G) x`.
7. `Frankl.FC.abundant_of_certificate`, `FranklFC.lean:91`. An FC-family certificate theorem for any
   union-closed `family` containing `base` with `A ⊆ W`. The conclusion is
   `∃ x ∈ W, 0 < w x ∧ Abundant family x`.

## A4. Hadamard 2396 and Legendre pairs (Hadamard*, about 290 files)

**Headline.** No order-2396 matrix is claimed.
- Proved: the order-479 automorphism obstruction, the fixed-border multiplier group, and the
  length-598 order-11 obstruction.
- Proved in general: **a Legendre pair on any finite abelian group G gives an actual Hadamard matrix
  of order 2|G| + 2.**
- Pending: the length-1197 multiplier bound of 9.

`IsLegendrePair f := (∀ i, SignValued (f i)) ∧ ∀ u, u ≠ 0 → pairCorrelation f u = -2`
(`HadamardLegendreBasic.lean:34`).

1. `HadamardLegendre.exists_hadamard_of_legendre_pair`, `HadamardLegendreConstruction.lean:164`. The
   result is Mathlib's `Matrix.IsHadamard`, over ℤ:
   ```lean
   theorem exists_hadamard_of_legendre_pair (f : Rows2 G) (hf : IsLegendrePair f) :
       ∃ H : Matrix (Fin (2 * Fintype.card G + 2)) (Fin (2 * Fintype.card G + 2)) ℤ,
         H.IsHadamard
   ```
   Also `twoRowMatrix_isHadamard` (:149) and `exists_hadamard_2396_of_legendre_pair` (:175).
2. `HadamardLegendre.compressed_pairCorrelation_formula`, `HadamardLegendreCompression.lean:82`.
   Compression of a Legendre pair along any surjective hom:
   ```lean
   theorem compressed_pairCorrelation_formula
       (π : G →+ Q) (hπ : Function.Surjective π) (f : Rows2 G)
       (hf : IsLegendrePair f) (t : Q) :
       pairCorrelation (fun i => compress π (f i)) t =
         -2 * (Nat.card π.ker : ℤ) +
           if t = 0 then 2 * ((Fintype.card G : ℤ) + 1) else 0
   ```
   Also `compressed_pair_energy` (:95):
   `(∑ i, ∑ q, (compress π (f i) q) ^ 2) = 2 * ((Fintype.card G : ℤ) + 1) - 2 * (Nat.card π.ker : ℤ)`.
3. `HadamardLegendre.rowSum_sign_of_legendre` (`HadamardLegendreBasic.lean:100`):
   `∀ i, rowSum (f i) = 1 ∨ rowSum (f i) = -1`. Also `sum_pairCorrelation_of_legendre` (:72), which
   gives `= 2`.
4. `HadamardLegendre.commonMultiplierGroup_eq_fixed_centeredRows` (`HadamardLegendreCentering.lean:185`)
   and `odd_automorphism_subgroup_isThreeGroup` (`HadamardLegendreOrderNineGroup.lean:72`). These are
   multiplier and automorphism structure, partly specific to order 9.
5. The Hadamard automorphism arithmetic (e.g. `no_norm_prime : a ^ 2 + 479 * b ^ 2 ≠ 4 * 599`) is
   specific to 479 and 599.

## A5. Pomerance–Sárközy and prime sums (PomeranceSarkozy*, 115 files)

**Headline.** Partial. Proved: the literal count, prime tails, finite-window total variation,
Bernoulli/Poisson comparisons, the joint Poisson count law, and Mertens-type prime-mean inputs. The
arithmetic limit statements are still open in A.

1. `PomeranceSarkozy.primeReciprocalSum_logLog_bounded` (`PomeranceSarkozyMertensRemainder.lean:92`).
   **Mertens' second theorem, bounded-error form:**
   ```lean
   theorem primeReciprocalSum_logLog_bounded :
       ∃ B : ℝ,∀ x : ℝ,2≤x→|primeReciprocalSum x-Real.log (Real.log x)|≤B
   ```
   with `primeReciprocalSum x = ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime,(1:ℝ)/(p:ℝ)`
   (`PomeranceSarkozyMertensAbel.lean:14`).
2. `PomeranceSarkozy.primeWeightedReciprocal_log_real_bounded` (`PomeranceSarkozyWeightedPrime.lean:79`).
   Mertens' first theorem, `∑ log p / p = log x + O(1)`:
   `∃ C : ℝ,0≤C ∧ ∀ x : ℝ,2≤x→|primeWeightedReciprocal ⌊x⌋₊-Real.log x|≤C`.
3. `PomeranceSarkozy.mangoldtReciprocal_log_bounds` (`PomeranceSarkozyMangoldtReciprocal.lean:60`):
   ```lean
   theorem mangoldtReciprocal_log_bounds (N : ℕ) (hN : 0<N) :
       Real.log (N:ℝ)-1≤mangoldtReciprocal N ∧
         mangoldtReciprocal N≤Real.log (N:ℝ)+(Real.log 4+4)
   ```
   Here `mangoldtReciprocal N = ∑ d ∈ range (N+1), Λ d / d`. Also `log_factorial_eq_mangoldt_floors`
   (`PomeranceSarkozyMangoldtFloor.lean:49`).
4. `PomeranceSarkozy.shifted_prime_tail_reciprocal` (`PomeranceSarkozyFiniteSieve.lean:69`). A
   union-bound sieve for having a prime factors in P:
   ```lean
   theorem shifted_prime_tail_reciprocal (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (L X h a : ℕ) :
       ((primeTailSamples P L X h a).card:ℚ) ≤
         (X:ℚ)*∑ S ∈ P.powersetCard a,∏ p ∈ S,(p:ℚ)⁻¹
   ```
5. `PomeranceSarkozy.sum_reciprocal_sq_le_cutoff` (`PomeranceSarkozyReciprocalTail.lean:31`):
   `(hy : 0<y) (hP : ∀ p∈P,y<p) : (∑ p ∈ P,(1/(p:ℚ))^2)≤1/(y:ℚ)`.
6. `PomeranceSarkozy.bernoulli_to_joint_poisson_counts_le` (`PomeranceSarkozyPoissonCountLaw.lean:43`).
   An L¹ Bernoulli-to-Poisson comparison. `PomeranceSarkozy.incidenceWindow_count_error`
   (`PomeranceSarkozyPrimeCRT.lean:76`) gives a CRT window-count error.

## A6. Erdős–Gyárfás abelian covers (ErdosGyarfas*)

`ErdosGyarfasUniversal.universal_cover_power_of_two_cycle` (`ErdosGyarfasUniversalMain.lean:17`). It is
proved by a checked table (`decide`), and 32 is sharp
(`least_power_of_two_cycle_length`, `ErdosGyarfasSharpMain.lean:58`).
```lean
theorem universal_cover_power_of_two_cycle {A : Type*} [AddCommGroup A]
    (labels : Fin 7 → A) :
    ∃ (u : Fin 5 × A) (p : (voltageCover labels).Walk u u) (k : ℕ),
      p.IsCycle ∧ 2 ≤ k ∧ k ≤ 5 ∧ p.length = 2 ^ k
```

## A7. Not found in A

There are no Sidon-set, sum-free-set or additive-basis lemmas in A (`grep -il sidon|sumfree` hits
nothing relevant). Partitions do appear: plane-partition Turán (`HeimNeuhauser*`, complete) and
Sobolewski–Ulas binary-partition congruences (`SobolewskiUlas*`, partial). Both are polynomial or
automaton certificates, and I found no partition lemma likely to transfer (not mined in depth).
Hajdu–Sárközy (`HajduSarkozyProducts.hajdu_sarkozy_shifted_products_conjecture`, total
multiplicative primitivity of shifted products) is complete, but I found no open FC statement that
it feeds.

---

# Part B: formal-conjectures

## B(i). Reusable proved lemmas in FormalConjecturesForMathlib

Most of the 870 declarations are definitions and API (`_iff`, `mono`, `_zero`). The substantive ones,
measured by proof length (≥ 20 lines), are:

| Declaration | File:line | Statement (copied) |
|---|---|---|
| `SimpleGraph.girth_sub_one_le_largestInducedTreeSize` | `Combinatorics/SimpleGraph/LargestInducedTree.lean:200` | `(hcyc : ¬ G.IsAcyclic) : G.girth - 1 ≤ largestInducedTreeSize G` |
| `SimpleGraph.maxDegree_add_girth_le_largestInducedTreeSize_add_three` | `Combinatorics/SimpleGraph/InducedTreeNeighborhood.lean:436` | `(hG : G.Connected) (hcyc : ¬ G.IsAcyclic) (hg4 : 4 ≤ G.girth) : G.maxDegree + G.girth ≤ largestInducedTreeSize G + 3` |
| `SimpleGraph.Walk.induce_support_isTree_of_length_eq_dist` | `LargestInducedTree.lean:148` | `(p : G.Walk u v) (hp : p.length = G.dist u v) : (G.induce (p.support.toFinset : Set α)).IsTree` |
| `SimpleGraph.isTree_induce_insert_indepSet_neighbors` | `InducedTreeNeighborhood.lean:361` | `(∀ s ∈ S, G.Adj v s) → G.IsIndepSet (S : Set α) → (G.induce ((insert v S : Finset α) : Set α)).IsTree` |
| `Combinatorics.Diagonal.hasRamseyProperty_choose` | `Combinatorics/Ramsey/Diagonal.lean:237` | `∀ (s t : ℕ), HasRamseyProperty (Nat.choose (s + t) s) s t` (Erdős–Szekeres) |
| `SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq` | `Combinatorics/SimpleGraph/Mycielski.lean:175` | `(hk : 2 ≤ k) : ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞)` |
| `SylvesterGallai.exists_ordinary_line` | `Geometry/OrdinaryLines.lean:215` | `(hs : ¬ Collinear ℝ (s : Set V)) : ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∀ p ∈ s, p ∈ line[ℝ, a, b] → p = a ∨ p = b` |
| `not_isAddComplete_range_diff_of_sum_range_le` | `NumberTheory/AdditivelyComplete.lean:212` | `(hA : StrictMono fun k => A (n₀ + k)) (hsum : ∀ m, n₀ ≤ m → ∑ i ∈ Finset.range m, A i ≤ A (m + 1)) {B : Set ℕ} (hB : B ⊆ Set.range A) (hB' : B.Infinite) : ¬ IsAddComplete (Set.range A \ B)` |
| `Nat.exists_antichain_powers_two_three` | `NumberTheory/AntichainPowers.lean:38` | every n is a sum of a ∣-antichain of numbers `2^a 3^b` |
| `isSidon_iff_le` | `Combinatorics/Basic.lean:140` | ordered Sidon criterion; `IsSidon.insert` (:94) |
| `SimpleGraph.exists_isCliqueEdgePartition_card_eq` | `Combinatorics/SimpleGraph/Chordal.lean:51` | trivial edge partition into cliques |
| `isPerfectPower_iff_factorization_gcd` | `Data/Nat/PerfectPower.lean:39` | perfect power iff gcd of exponents > 1 |

The quoted statements have their implicit `{α}`/`[Fintype]` binders omitted; the rest is verbatim.

## B(ii). `formal_proof` attributes

There are 1,224 links across 789 files: 1,046 `lean4`, 173 `formal_conjectures`, 5 `other_system`.
The main targets are:

| Target | Links |
|---|---:|
| `plby/lean-proofs` | 430 |
| `mo271/formal-conjectures` | 86 |
| `linrock/math-proofs` | 49 |
| `openai/math` | 38 |
| `anatoliiohorodnyk/lean-fc-proofs` | 35 |
| `VictorLiwentao/lean-oeis-proofs` | 22 |
| `Jayyhk/erdos-lean` | 19 |
| `google-deepmind/formal-conjectures` | 18 |
| `epoch-research/LeanOpenProblems-results` | 15 |

**None of the external proofs is available locally.** `src/openai-math/lean/` contains only
`README.md`, `formalization.yaml` and `lean-toolchain`, with no `.lean` files. So I could not check
whether the linked proofs contain general intermediate lemmas. Examples of what is linked, from the
paths only (unverified):
- `OAI/Geometry/PlaneColoring/Five.lean`, cited by `HadwigerNelsonAtLeastSix : 6 ≤ χ(ℝ²)`, solved,
  `ErdosProblems/508.lean`.
- `OAI/LinearAlgebra/CirculantHadamard/Main.lean`, cited by `circulant_hadamard_conjecture`,
  `Arxiv/2402.13202/CirculantHadamard.lean`.
- `OAI/Combinatorics/Sidorenko/RandomHost.lean`, `OAI/NumberTheory/Jacobsthal/...`.

The Hadwiger–Nelson ≥ 6 proof would be the main external chromatic-number input; it needs fetching.

## B(iii). Proved inside FC (research solved, no `sorry`) with a reusable core

- `erdos_949.variants.sidon` (`ErdosProblems/949.lean:47`):
  `∀ S : Set ℝ, IsSidon S → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ`.
- `erdos_698.variants.erdos_szekeres` (`ErdosProblems/698.lean:65`): a gcd lower bound for binomial
  coefficients.
- `sidorenko_conjecture.variants.star` (`Wikipedia/SidorenkoConjecture.lean:933`) and `sidorenko_K22`
  (:535): Sidorenko for stars and for K₂,₂, via `homDensity`.
- `erdos_602.variants.two_sets` (`ErdosProblems/602.lean:243`): Property B for two sets.
- `erdos_794.variants.balogh` (`ErdosProblems/794.lean:70`).
- `erdos_840.variants.erdos_freud_upper` (`ErdosProblems/840.lean:92`):
  `IsQuasiSidonConstant c → c ≤ 2`.
- `erdos_346.variants.gt_goldenRatio_not_IsAddComplete` (`ErdosProblems/346.lean:159`).
- `union_closed.variants.sharpness` (`Wikipedia/UnionClosed.lean:155`, 49 lines): the 1/2 cannot be
  improved.

---

# Part C: matches from lemma families to open FC statements

I checked every open statement by reading its declaration. "Gap" names what is still missing.
**(unverified)** marks my mathematical judgement or a literature status I did not check.

1. **LRC for ≤ 5 integer speeds (A1.1, A1.2, A1.6) → `LonelyRunnerConjecture.lonely_runner_conjecture`**
   (`Wikipedia/LonelyRunnerConjecture.lean:39`, open, also in `Subsets/FC100OpenSet2.lean:202`).
   The statement:
   ```lean
   theorem lonely_runner_conjecture (n : ℕ)
       (speed : Fin n ↪ ℝ) (lonely : Fin n → ℝ → Prop)
       (lonely_def : ∀ r t, lonely r t ↔ ∀ r2 : Fin n, r2 ≠ r →
           dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / n)
       (r : Fin n) : ∃ t ≥ 0, lonely r t
   ```
   The FC statement is for all n and has no small-n variant, so the honest target is a new variant
   `n ≤ 6` (my suggestion, not in FC). Gap:
   - (a) a real-to-integer speed reduction. It is known in the literature (Bohman–Holzman–Kleitman;
     Henze–Malikiosis) **(unverified)** and has no counterpart in A.
   - (b) a translation from relative speeds `|v_i − v_r|` to the list form. A's
     `five_speed_common_time` allows repeated speeds, which helps.
   - (c) translating `UnitAddCircle` distance into `Loneliness.distance`.

   The real-speed measure lemma A1.8 (`two_speed_interval_of_length`) is the only real-speed tool in A.
   - Related solved-but-`sorry` statement: `lonely_runner_conjecture.variants.tao_2017` (`:73`). Its
     `deltaGap n` uses `Fin n ↪ ℤ` with nonzero, possibly negative, speeds. A1.2 gives
     `deltaGap 5 ≥ 1/6` after replacing each speed by its absolute value, but that is not stated
     in FC.

2. **Legendre pair ⇒ Hadamard (A4.1) → `Hadamard.HadamardConjecture.variants.«167»`**
   (`Wikipedia/Hadamard.lean:150`, `668 < hadamardConstant`, open).
   - 668 = 2·333 + 2, so `exists_hadamard_of_legendre_pair` reduces the open statement to finding
     **one Legendre pair of length 333** (any abelian group of order 333). Whether one is known is
     **(unverified)**; I believe ℓ = 333 is not known.
   - The FC statement must also rule out other k < 167; `variants.first_cases` (668 ≤ …) is still
     `sorry`.
   - Bridge needed: FC's `IsHadamard` uses `|det| = n^(n/2)` over ℝ, while A uses Mathlib's
     `Matrix.IsHadamard` over ℤ. FC's `isHadamard_equiv_isHadamard'` (:54) carries a TODO.
   - The same lemma reduces `HadamardConjecture` (:91) for k = (ℓ+1)/2 to Legendre pairs of odd
     length ℓ.

3. **Mertens' second theorem (A5.1) → `Erdos726.erdos_726`** (`ErdosProblems/726.lean:46`, open):
   `∑_{p ≤ n, p/2 < n mod p} 1/p ~ (log log n)/2`. A5.1 supplies `∑ 1/p = log log n + O(1)`, which
   is necessary. The missing input is the equidistribution of `n mod p` over `p` in the sum, which
   is the actual open content. A5.4 (prime-tail sieve) and A5.3 are related inputs.
   - Weaker related matches: `erdos_890.parts.b` (`ErdosProblems/890.lean:59`, ω over k consecutive
     integers × `log log n / log n`) and `erdos_950.parts.iii` (`ErdosProblems/950.lean:64`,
     `f = o(log log n)` for `f n = ∑_{p<n} 1/(n-p)`). For these, A5.1–A5.3 are standard sizes and
     are far from sufficient **(unverified)**.

4. **Lopsided LLL (A3.3) → `Erdos1029.erdos_1029`** (`ErdosProblems/1029.lean:48`, open):
   `diagonalRamsey k / (k 2^{k/2}) → ∞`. `Frankl.Lopsided.conditional_card_bound` is the finite LLL
   that gives the classical lower bound `R(k) ≥ (√2/e)(1+o(1)) k 2^{k/2}`. That is the baseline,
   and the open statement asks for more, so this is a necessary-tool match only. The same tool is
   relevant to `erdos_87.parts.i/ii` (`ErdosProblems/87.lean:45,60`) **(unverified)**. Ramsey upper
   bounds come from FC's `hasRamseyProperty_choose`.

5. **Union-closed frequency theorems (A3.1, A3.2, A3.5–A3.7) → `UnionClosed.union_closed`**
   (`Wikipedia/UnionClosed.lean:59`) and `union_closed.variants.cardinality_even_of_union_closed_tight`
   (:216).
   - A3.1 and A3.2 prove the conjecture with constants above 1/2 for the family generated by
     3-regular high-girth or linear uniform generators, so special cases only.
   - The general tools are the local-certificate criteria A3.5–A3.7 (Poonen-type). They prove
     abundance of a point whenever a finite certificate exists, and they could close FC-family
     variants. No such variant is stated in FC.

6. **Induced trees (B(i)) → `WrittenOnTheWallII.conjecture72`** (`GraphConjecture72.lean:53`) and
   `conjecture84` (`GraphConjecture84.lean:58`).
   - conjecture72 asks for `⌈avgEcc + maxL/3⌉ ≤ largestInducedTreeSize`, where `maxL` is the
     independence number of a neighbourhood. `isTree_induce_insert_indepSet_neighbors` gives
     `maxL + 1 ≤ largestInducedTreeSize`, and the geodesic lemma gives `diam + 1 ≤ ...`. Combining
     them is the gap **(unverified)**.
   - conjecture84 asks for `2·rad/δ ≤ largestInducedTreeSize`. For δ ≥ 2 the geodesic lemma
     plausibly suffices, since `rad ≤ diam < tree size`. The δ = 1 case needs `2·rad ≤ T`
     **(unverified)**.

7. **Abelian-cover power-of-two cycles (A6) → `Erdos64.erdos_64`** (`ErdosProblems/64.lean:35`):
   does every graph with min degree ≥ 3 have a cycle of length 2^k, k ≥ 2? A6 covers one infinite
   family of such graphs, the abelian covers of K₄ with one edge subdivided. That is a special case
   only, with no general lemma.

8. **Distance-graph colouring (A2.1–A2.3)**. I found no open FC statement about chromatic numbers of
   integer distance graphs or Motzkin densities. The open distance-graph statements are about the
   plane or ℝⁿ:
   - `erdos_704.parts.ii` (`ErdosProblems/704.lean:79`)
   - `erdos_706` (`ErdosProblems/706.lean:54`)
   - Hadwiger–Nelson (`Wikipedia/HadwigerNelson.lean`)

   A2's 1-D lemmas do not transfer to these. So this family has no match; it would need new FC
   statements, e.g. a Zhu-type "χ(G(D)) ≤ |D|+1 for |D| ≤ 5" or Carraher et al.

9. **Sidon / sum-free.** A has nothing. FC's own `isSidon_iff_le`, `IsSidon.insert` and
   `erdos_949.variants.sidon` are API-level. The open targets (`erdos_39`, `erdos_44`,
   `erdos_329`, `erdos_1191.parts.i/ii`, `erdos_1206.parts.i/ii`, `green_31.variants.zmod_p`,
   `erdos_876.parts.i`) need analytic constructions that no local lemma provides.

10. **Prime filtering (A1.7, general p-adic digit avoidance).** This is a general covering lemma
    ("a unit multiplier avoids prescribed top digits under a budget"). I found no open FC statement
    that obviously needs it. A guess is covering-system and digit problems such as
    `NumberTheory/CoveringSystem`-based statements **(unverified, not checked)**.
