import Implications.Erdos142.Statement

/-!
# Erdős #142 (`lower`) and the all-`k` form of #140 from a quantitative Szemerédi bound

From openai/math's bound `r_k(N) ≤ C N exp(−c (log log N)^{1+η})` for every `k ≥ 3`
(`Erdos142.OAI.QuantitativeDensityTheorem`, a tier-H hypothesis) we prove

* `Erdos142.variantsLower_of_quantitativeDensity`: formal-conjectures
  `erdos_142.variants.lower`, `r_k(N) = o(N / log N)` for every `k ≥ 2`;
* `Erdos140.allK_of_quantitativeDensity`: `r_k(N) = O(N / (log N)^C)` for every `k ≥ 3` and
  `C > 0`, through the stronger `Erdos140.isLittleO_of_quantitativeDensity` (`o` in place of `O`).

Steps.
1. `Erdos142.maxCard_le_extremalNumber`: for `k ≥ 2`, a set free of non-trivial `k`-APs in
   formal-conjectures' sense has no `HasAP` of length `k`, so `r k N ≤ extremalNumber k N`.
   Since `HasAP` of length `max k 3` contains one of length `k`, also
   `r k N ≤ extremalNumber (max k 3) N`, which covers `k = 2` with the `k = 3` bound.
2. `Erdos142.tendsto_exp_mul_log_rpow`: `exp(−c L^{1+η}) (log N)^C → 0`, `L = log log N`,
   because `(log N)^C = exp(C L)` and `C L − c L^{1+η} → −∞`.
-/

open Asymptotics Filter Real

namespace Erdos142

/-- A formal-conjectures `k`-AP-free set (`k ≥ 2`) is `APFree` in openai/math's sense. -/
theorem apFree_of_isAPOfLengthFree {S : Set ℕ} {k : ℕ} (hk : 2 ≤ k)
    (hS : S.IsAPOfLengthFree k) : OAI.APFree S k := by
  rintro ⟨a, d, hd, h⟩
  classical
  let f : ℕ → ℕ := fun n => a + n * d
  have hf : Function.Injective f := by
    intro m n hmn
    have : m * d = n * d := by simpa [f] using hmn
    exact Nat.eq_of_mul_eq_mul_right hd this
  let t : Set ℕ := ((Finset.range k).image f : Finset ℕ)
  have ht : t ⊆ S := by
    intro x hx
    simp only [t, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi
  have hAP : t.IsAPOfLength k := by
    refine ⟨a, d, ?_, ?_⟩
    · change Set.encard t = k
      simp only [t, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hf,
        Finset.card_range]
    · ext x
      simp only [t, f, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
        Set.mem_setOf_eq, smul_eq_mul, Nat.cast_lt, exists_prop]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, by ring⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, by ring⟩
  have := hS t ht hAP
  have : k ≤ 1 := by exact_mod_cast this
  omega

/-- `APFree` is monotone in the length (openai/math `APFree.of_le`, reproved here). -/
theorem apFree_of_le {A : Set ℕ} {k l : ℕ} (h : OAI.APFree A k) (hkl : k ≤ l) :
    OAI.APFree A l := by
  rintro ⟨a, d, hd, hA⟩
  exact h ⟨a, d, hd, fun i hi => hA i (hi.trans_le hkl)⟩

/-- Bridge: for `2 ≤ k ≤ l`, `r k N ≤ extremalNumber l N`. -/
theorem maxCard_le_extremalNumber {k l : ℕ} (hk : 2 ≤ k) (hkl : k ≤ l) (N : ℕ) :
    r k N ≤ OAI.extremalNumber l N := by
  classical
  apply csSup_le'
  rintro _ ⟨S, hSN, hS, rfl⟩
  unfold OAI.extremalNumber
  convert Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSN,
      apFree_of_le (apFree_of_isAPOfLengthFree hk hS) hkl⟩)

/-- `log log N → ∞` along the naturals. -/
theorem tendsto_loglog : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `C L − c L^{1+η} → −∞` as `L → ∞`. -/
theorem tendsto_sub_rpow {C c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun L : ℝ => C * L - c * L ^ (1 + η)) atTop atBot := by
  have hpow : Tendsto (fun L : ℝ => L ^ η) atTop atTop := tendsto_rpow_atTop hη
  have hev : ∀ᶠ L in atTop, C * L - c * L ^ (1 + η) ≤ -L := by
    filter_upwards [hpow.eventually_ge_atTop ((C + 1) / c), eventually_ge_atTop (1 : ℝ)]
      with L hL hL1
    have hL0 : 0 < L := by linarith
    have hsplit : L ^ (1 + η) = L * L ^ η := by
      rw [rpow_add hL0, rpow_one]
    have hcL : C + 1 ≤ c * L ^ η := by
      have := mul_le_mul_of_nonneg_left hL hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    rw [hsplit]
    nlinarith
  exact tendsto_atBot_mono' atTop hev tendsto_neg_atTop_atBot

/-- `exp(−c (log log N)^{1+η}) · (log N)^C → 0`. -/
theorem tendsto_exp_mul_log_rpow {C c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun N : ℕ => Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) *
      Real.log N ^ C) atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => Real.exp (C * Real.log (Real.log N) -
      c * (Real.log (Real.log N)) ^ (1 + η))) atTop (nhds 0) :=
    tendsto_exp_atBot.comp ((tendsto_sub_rpow (C := C) hc hη).comp tendsto_loglog)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  rw [rpow_def_of_pos hlog, ← Real.exp_add]
  congr 1
  ring

end Erdos142

namespace Erdos140

open Erdos142

/-- The stronger form: `r_k(N) = o(N / (log N)^C)` for every `k ≥ 2` and every real `C`. -/
theorem isLittleO_of_quantitativeDensity (h : OAI.QuantitativeDensityTheorem)
    (k : ℕ) (hk : 2 ≤ k) (C : ℝ) :
    (fun N : ℕ => (r k N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) / Real.log N ^ C) := by
  obtain ⟨C₀, c, η, hC₀, hc, hη, hbound⟩ := h (max k 3) (le_max_right _ _)
  set g : ℕ → ℝ := fun N => C₀ * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))
  -- `r k N ≤ g N` for `N ≥ 3`
  have hO : (fun N : ℕ => (r k N : ℝ)) =O[atTop] g := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have h1 : (r k N : ℝ) ≤ OAI.extremalNumber (max k 3) N := by
      exact_mod_cast maxCard_le_extremalNumber hk (le_max_left _ _) N
    have h2 := hbound N hN
    have hg : 0 ≤ g N := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hg, one_mul]
    exact h1.trans h2
  refine hO.trans_isLittleO ?_
  rw [isLittleO_iff_tendsto']
  · have := (tendsto_exp_mul_log_rpow (C := C) hc hη).const_mul C₀
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < Real.log N := Real.log_pos (by linarith)
    have hpow : 0 < Real.log N ^ C := rpow_pos_of_pos hlog C
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    simp only [g]
    field_simp
  · filter_upwards [eventually_ge_atTop 3] with N hN hzero
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < Real.log N := Real.log_pos (by linarith)
    have hpos : 0 < (N : ℝ) / Real.log N ^ C := by
      have := rpow_pos_of_pos hlog C
      positivity
    exact absurd hzero hpos.ne'

/-- **Erdős #140, all `k ≥ 3`** (our statement), from openai/math's quantitative bound. -/
theorem allK_of_quantitativeDensity (h : OAI.QuantitativeDensityTheorem) : AllK :=
  fun k hk C _ => (isLittleO_of_quantitativeDensity h k (by omega) C).isBigO

end Erdos140

namespace Erdos142

/-- **formal-conjectures `erdos_142.variants.lower`** from openai/math's quantitative bound. -/
theorem variantsLower_of_quantitativeDensity (h : OAI.QuantitativeDensityTheorem) :
    VariantsLower := by
  intro k hk
  have := Erdos140.isLittleO_of_quantitativeDensity h k hk 1
  simpa only [rpow_one] using this

end Erdos142
