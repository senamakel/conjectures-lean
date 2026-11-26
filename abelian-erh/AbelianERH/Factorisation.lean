import AbelianERH.Statement
import AbelianERH.DirichletExp
import Artin.Analytic.Core.VonMangoldt

/-!
# From a coefficient identity to ERH

Let `K` be a number field, `N ≥ 1`, and `X` a finite set of Dirichlet characters mod `N` such that
`Λ_K(n) = ∑_{χ ∈ X} χ(n) Λ(n)` for every `n` coprime to `N` (`Λ_K` is artin-grh's
`Artin.Analytic.vonMangoldtK`, the coefficients of `-ζ_K'/ζ_K`). Then:

1. `dedekindZeta_eq_mul_prod`: `ζ_K(s) = E(s) · ∏_{χ ∈ X} L(s, χ)` for `Re s > 1`, with
   `E(s) = exp(∑_{(n, N) > 1} Λ_K(n) / log n · n^{-s})`. Take logarithms: `log ζ_K` has
   coefficients `Λ_K(n) / log n` (artin-grh's `dedekindZeta_eq_exp`) and `log L(s, χ)` has
   `χ(n) Λ(n) / log n` (`LSeries_eq_exp_logLCoeff`); they agree at `n` coprime to `N`, and
   `χ(n) = 0` at the other `n`.
2. `E` is holomorphic and zero-free on `Re s > 0`: its exponent is supported on the powers `p^k` of
   the primes `p ∣ N`, with coefficients at most `[K : ℚ]`, so it converges absolutely there
   (`LSeriesSummable_ramCoeff`).
3. `extendedRiemannHypothesis_of_coeff`: any continuation `Z` of `ζ_K` equals `E · ∏ L(·, χ)` on
   `{Re s > 0} ∖ {1}` (identity theorem; the set is connected). A zero of `Z` in the critical
   strip is therefore a zero of some `L(s, χ)`, and `DirichletLZerosOnLine` puts it on
   `Re s = 1/2`.

`vonMangoldtK_prime_pow` computes `Λ_K(q^k)` at a prime `q` with one inertia degree `f` above it and
`#{𝔮 ∣ q} · f = [K : ℚ]` (no ramification): it is `[K : ℚ] log q` if `f ∣ k` and `0` otherwise.
-/

namespace AbelianERH

open NumberField Finset ArithmeticFunction Complex Filter Topology LSeries Artin.Analytic
open scoped LSeries.notation

section PrimePow

variable (K : Type*) [Field K] [NumberField K]

/-- **`Λ_K` at an unramified prime power.** If every prime of `K` above `q` has inertia degree
`f` and there are `[K : ℚ] / f` of them, then `Λ_K(q^k) = [K : ℚ] log q` when `f ∣ k`, and `0`
otherwise. -/
theorem vonMangoldtK_prime_pow {q : ℕ} (hq : q.Prime) {f : ℕ}
    (hf : ∀ P ∈ primesAbove K q, P.inertiaDeg ℤ = f)
    (hcard : (primesAbove K q).card * f = Module.finrank ℚ K) {k : ℕ} (hk : 0 < k) :
    vonMangoldtK K (q ^ k) = if f ∣ k then (Module.finrank ℚ K : ℝ) * Real.log q else 0 := by
  classical
  have hq2 := hq.two_le
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have := (Module.finrank_pos : 0 < Module.finrank ℚ K)
      rw [h, mul_zero] at hcard
      omega
    · exact h
  unfold vonMangoldtK
  rw [Finset.sum_eq_single q]
  · have hP : ∀ P ∈ primesAbove K q, (∑ m ∈ Icc 1 (q ^ k),
        if Ideal.absNorm P ^ m = q ^ k then Real.log (Ideal.absNorm P) else 0) =
        if f ∣ k then (f : ℝ) * Real.log q else 0 := by
      intro P hP
      have hN : Ideal.absNorm P = q ^ f := by rw [← absNorm_eq_pow hq hP, hf P hP]
      have hlog : Real.log (Ideal.absNorm P) = f * Real.log q := by
        rw [hN, Nat.cast_pow, Real.log_pow]
      have hiff : ∀ m, (q ^ f) ^ m = q ^ k ↔ f * m = k := fun m => by
        rw [← pow_mul]; exact (Nat.pow_right_injective hq2).eq_iff
      simp_rw [hlog, hN, hiff]
      split_ifs with hdvd
      · obtain ⟨j, rfl⟩ := hdvd
        rw [Finset.sum_eq_single j]
        · simp
        · intro m _ hm
          exact ite_eq_right fun h => hm (Nat.eq_of_mul_eq_mul_left hfpos h)
        · intro hj
          exfalso
          apply hj
          rw [Finset.mem_Icc]
          have hj0 : 0 < j := Nat.pos_of_mul_pos_left hk
          refine ⟨hj0, ?_⟩
          calc j ≤ f * j := Nat.le_mul_of_pos_left j hfpos
            _ ≤ q ^ (f * j) := (Nat.lt_pow_self hq.one_lt).le
      · exact Finset.sum_eq_zero fun m _ => ite_eq_right fun h => hdvd ⟨m, h.symm⟩
    rw [Finset.sum_congr rfl hP, Finset.sum_const, nsmul_eq_mul]
    split_ifs
    · rw [← mul_assoc]
      congr 1
      exact_mod_cast hcard
    · simp
  · intro p hp hpq
    have hpr := (Finset.mem_filter.1 hp).2
    refine Finset.sum_eq_zero fun P hP => Finset.sum_eq_zero fun m hm => ite_eq_right fun h => hpq ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hf1 := one_le_inertiaDeg hpr hP
    have hdvd : p ∣ q ^ k := by
      rw [← h, ← absNorm_eq_pow hpr hP, ← pow_mul]
      exact dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))
    exact (Nat.prime_dvd_prime_iff_eq hpr hq).1 (hpr.dvd_of_dvd_pow hdvd)
  · intro h
    exfalso
    apply h
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_self_pow hk.ne' q), hq⟩

lemma vonMangoldtK_eq_zero {n : ℕ} (hn : Λ n = 0) : vonMangoldtK K n = 0 :=
  le_antisymm (by simpa [hn] using vonMangoldtK_le K n) (vonMangoldtK_nonneg K n)

end PrimePow

section Ramified

variable (K : Type*) [Field K] [NumberField K] (N : ℕ)

/-- The coefficients of `log ζ_K` at the `n` not coprime to `N`: the exponent of the factor `E`. -/
noncomputable def ramCoeff (n : ℕ) : ℂ := if n.Coprime N then 0 else (logZetaCoeff K n : ℂ)

lemma ramCoeff_support [NeZero N] {n : ℕ} (hn : ramCoeff K N n ≠ 0) :
    ∃ q ∈ N.primeFactors, ∃ k : ℕ, q ^ (k + 1) = n := by
  unfold ramCoeff at hn
  split_ifs at hn with hc
  · exact absurd rfl hn
  have hK : vonMangoldtK K n ≠ 0 := by
    intro h; apply hn; simp [logZetaCoeff, h]
  have hΛ : Λ n ≠ 0 := fun h => hK (vonMangoldtK_eq_zero K h)
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
  have hqN : q ∣ N := by
    by_contra h
    exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 h))
  have hN0 : N ≠ 0 := NeZero.ne N
  refine ⟨q, Nat.mem_primeFactors.2 ⟨hq, hqN, hN0⟩, k - 1, ?_⟩
  rw [Nat.sub_add_cancel hk]

lemma norm_ramCoeff_le (n : ℕ) : ‖ramCoeff K N n‖ ≤ Module.finrank ℚ K := by
  unfold ramCoeff
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_of_nonneg (logZetaCoeff_nonneg K n)]
    exact logZetaCoeff_le K n

/-- `∑_k d / (q^{k+1})^σ < ∞` for `q ≥ 2`, `σ > 0`, as a sum over `n ∈ {q^{k+1}}`. -/
lemma summable_indicator_powers {q : ℕ} (hq : 2 ≤ q) (d : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (Set.indicator (Set.range fun k : ℕ => q ^ (k + 1))
      fun n : ℕ => d / (n : ℝ) ^ σ) := by
  have hinj : Function.Injective fun k : ℕ => q ^ (k + 1) := fun a b h =>
    by simpa using Nat.pow_right_injective hq h
  rw [← hinj.summable_iff (fun x hx => Set.indicator_of_notMem hx _)]
  have hr : 1 < (q : ℝ) ^ σ := Real.one_lt_rpow (by exact_mod_cast hq) hσ
  have hr0 : 0 < ((q : ℝ) ^ σ)⁻¹ := inv_pos.2 (by linarith)
  have hr1 : ((q : ℝ) ^ σ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  refine ((summable_geometric_of_lt_one hr0.le hr1).mul_left (d * ((q : ℝ) ^ σ)⁻¹)).congr
    fun k => ?_
  simp only [Function.comp_apply, Set.indicator_of_mem (Set.mem_range_self k)]
  have hpow : ((q ^ (k + 1) : ℕ) : ℝ) ^ σ = ((q : ℝ) ^ σ) ^ (k + 1) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity), mul_comm]
  rw [hpow, div_eq_mul_inv, ← inv_pow, pow_succ]
  ring

lemma LSeriesSummable_ramCoeff [NeZero N] {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (ramCoeff K N) s := by
  classical
  set d : ℝ := (Module.finrank ℚ K : ℝ)
  set g : ℕ → ℝ := fun n => ∑ q ∈ N.primeFactors,
    Set.indicator (Set.range fun k : ℕ => q ^ (k + 1)) (fun n : ℕ => d / (n : ℝ) ^ s.re) n
  have hg : Summable g := summable_sum fun q hq =>
    summable_indicator_powers (Nat.prime_of_mem_primeFactors hq).two_le d hs
  refine Summable.of_norm_bounded hg fun n => ?_
  have hgn : 0 ≤ g n := Finset.sum_nonneg fun q _ => Set.indicator_nonneg
    (fun n _ => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) n
  by_cases h0 : ramCoeff K N n = 0
  · rw [LSeries.term_def]
    split_ifs
    · simpa using hgn
    · simpa [h0] using hgn
  obtain ⟨q, hq, k, rfl⟩ := ramCoeff_support K N h0
  have hn0 : q ^ (k + 1) ≠ 0 := pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
  rw [LSeries.norm_term_eq, ite_eq_right hn0]
  calc ‖ramCoeff K N (q ^ (k + 1))‖ / ((q ^ (k + 1) : ℕ) : ℝ) ^ s.re
      ≤ d / ((q ^ (k + 1) : ℕ) : ℝ) ^ s.re := by
        gcongr
        exact norm_ramCoeff_le K N _
    _ = Set.indicator (Set.range fun k : ℕ => q ^ (k + 1))
          (fun n : ℕ => d / (n : ℝ) ^ s.re) (q ^ (k + 1)) := by
        rw [Set.indicator_of_mem (Set.mem_range_self k)]
    _ ≤ g (q ^ (k + 1)) :=
        Finset.single_le_sum (f := fun q' => Set.indicator (Set.range fun k : ℕ => q' ^ (k + 1))
          (fun n : ℕ => d / (n : ℝ) ^ s.re) (q ^ (k + 1)))
          (fun q' _ => Set.indicator_nonneg (fun n _ => div_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _) hq

lemma abscissaOfAbsConv_ramCoeff_le [NeZero N] : abscissaOfAbsConv (ramCoeff K N) ≤ 0 :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_ramCoeff K N (by simpa using hy)

lemma differentiableAt_LSeries_ramCoeff [NeZero N] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (LSeries (ramCoeff K N)) s :=
  (LSeries_hasDerivAt ((abscissaOfAbsConv_ramCoeff_le K N).trans_lt
    (by exact_mod_cast hs))).differentiableAt

end Ramified

section Factorisation

variable (K : Type*) [Field K] [NumberField K] {N : ℕ} [NeZero N]

/-- The hypothesis on `X`: `Λ_K(n) = ∑_{χ ∈ X} χ(n) Λ(n)` for `n` coprime to `N`. -/
def CoeffIdentity (X : Finset (DirichletCharacter ℂ N)) : Prop :=
  ∀ n : ℕ, n.Coprime N → (vonMangoldtK K n : ℂ) = ∑ χ ∈ X, χ n * (Λ n : ℂ)

omit [NeZero N] in
lemma logZetaCoeff_eq {X : Finset (DirichletCharacter ℂ N)} (hX : CoeffIdentity K X) (n : ℕ) :
    (logZetaCoeff K n : ℂ) = (ramCoeff K N + ∑ χ ∈ X, logLCoeff χ) n := by
  rw [Pi.add_apply, Finset.sum_apply]
  unfold ramCoeff logLCoeff
  by_cases hc : n.Coprime N
  · rw [ite_eq_left hc, zero_add, logZetaCoeff, Complex.ofReal_div, hX n hc, Finset.sum_div]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.ofReal_div, mul_div_assoc]
  · rw [ite_eq_right hc, Finset.sum_eq_zero, add_zero]
    intro χ _
    have : ¬IsUnit (n : ZMod N) := by rwa [ZMod.isUnit_iff_coprime]
    rw [MulChar.map_nonunit χ this, zero_mul]

/-- **The factorisation** `ζ_K(s) = E(s) ∏_{χ ∈ X} L(s, χ)` for `Re s > 1`. -/
theorem dedekindZeta_eq_mul_prod {X : Finset (DirichletCharacter ℂ N)} (hX : CoeffIdentity K X)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      exp (LSeries (ramCoeff K N) s) * ∏ χ ∈ X, DirichletCharacter.LFunction χ s := by
  have hsum : ∀ χ ∈ X, LSeriesSummable (logLCoeff χ) s :=
    fun χ _ => LSeriesSummable_logLCoeff χ hs
  rw [dedekindZeta_eq_exp K hs, logDedekindZeta, LSeries_congr (fun {n} _ => logZetaCoeff_eq K hX n),
    LSeries_add (LSeriesSummable_ramCoeff K N (by linarith)) (LSeriesSummable.sum hsum),
    LSeries_sum hsum, Complex.exp_add, Complex.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun χ _ => ?_
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries_eq_exp_logLCoeff χ hs]

/-- `{Re s > 0} ∖ {1}` is preconnected: it is the union of four convex sets
`{Re > 0, Im > 0}`, `{0 < Re < 1}`, `{Re > 0, Im < 0}` and `{Re > 1}`, chained by common points. -/
lemma isPreconnected_halfPlane_diff_one : IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  set A := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}
  set B := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0}
  set C := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}
  set D := {s : ℂ | 1 < s.re}
  have hA : IsPreconnected A :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected B :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hD : IsPreconnected D := (convex_halfSpace_re_gt 1).isPreconnected
  have hAC : IsPreconnected (A ∪ C) :=
    hA.union (⟨1 / 2, 1 / 2⟩ : ℂ) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ hC
  have hACB : IsPreconnected (A ∪ C ∪ B) :=
    hAC.union (⟨1 / 2, -1 / 2⟩ : ℂ) (Or.inr ⟨by norm_num, by norm_num⟩)
      ⟨by norm_num, by norm_num⟩ hB
  have hall : IsPreconnected (A ∪ C ∪ B ∪ D) :=
    hACB.union (⟨2, 1⟩ : ℂ) (Or.inl (Or.inl ⟨by norm_num, by norm_num⟩)) (by norm_num [D]) hD
  convert hall using 1
  ext z
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_union,
    Set.mem_inter_iff, A, B, C, D]
  constructor
  · rintro ⟨h0, h1⟩
    rcases lt_trichotomy z.im 0 with him | him | him
    · exact Or.inl (Or.inr ⟨h0, him⟩)
    · rcases lt_trichotomy z.re 1 with hre | hre | hre
      · exact Or.inl (Or.inl (Or.inr ⟨h0, hre⟩))
      · exact absurd (Complex.ext (by simpa using hre) (by simpa using him)) h1
      · exact Or.inr hre
    · exact Or.inl (Or.inl (Or.inl ⟨h0, him⟩))
  · rintro (((⟨h0, him⟩ | ⟨h0, hre⟩) | ⟨h0, him⟩) | hre)
    · exact ⟨h0, fun h => by rw [h] at him; simp at him⟩
    · exact ⟨h0, fun h => by rw [h] at hre; simp at hre⟩
    · exact ⟨h0, fun h => by rw [h] at him; simp at him⟩
    · exact ⟨by linarith, fun h => by rw [h] at hre; simp at hre⟩

/-- **ERH for `K` from GRH for Dirichlet L-functions and the coefficient identity.** -/
theorem extendedRiemannHypothesis_of_coeff (hGRH : DirichletLZerosOnLine)
    {X : Finset (DirichletCharacter ℂ N)} (hX : CoeffIdentity K X) :
    ERH.ExtendedRiemannHypothesis K := by
  intro Z hZ s hs0 hs1 hZs
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {1}
  set F : ℂ → ℂ := fun s =>
    exp (LSeries (ramCoeff K N) s) * ∏ χ ∈ X, DirichletCharacter.LFunction χ s
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hZan : AnalyticOnNhd ℂ Z U :=
    (hZ.1.analyticOnNhd isOpen_compl_singleton).mono fun z hz => hz.2
  have hFan : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz1 : z ≠ 1 := hz.2
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_LSeries_ramCoeff K N hz.1).cexp.mul ?_
    exact DifferentiableAt.fun_finsetProd fun χ _ =>
      DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz1)
  have h2U : (2 : ℂ) ∈ U := ⟨show (0 : ℝ) < (2 : ℂ).re by norm_num, by norm_num⟩
  have heq : Z =ᶠ[𝓝 2] F := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | 1 < b.re} by norm_num)] with z hz
    rw [hZ.2 z hz, dedekindZeta_eq_mul_prod K hX hz]
  have hEq := hZan.eqOn_of_preconnected_of_eventuallyEq hFan isPreconnected_halfPlane_diff_one
    h2U heq
  have hsU : s ∈ U := ⟨hs0, fun h => by
    rw [Set.mem_singleton_iff] at h; rw [h] at hs1; norm_num at hs1⟩
  rw [hEq hsU] at hZs
  rcases mul_eq_zero.1 hZs with h | h
  · exact absurd h (Complex.exp_ne_zero _)
  · obtain ⟨χ, -, hχ⟩ := Finset.prod_eq_zero_iff.1 h
    exact hGRH N χ s hs0 hs1 hχ

end Factorisation

end AbelianERH
