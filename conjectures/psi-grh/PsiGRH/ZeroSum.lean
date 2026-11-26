import Erdos985.Analytic.ExplicitFormula.StepA
import PsiGRH.Inputs

/-!
# Zeros on the critical line and the sum `Σ_{|Im ρ| < T} m_ρ / |ρ|`

Under GRH every zero of a primitive `L(s, χ)` in the open critical strip has `Re ρ = 1/2`
(`re_eq_half_of_GRH`, via the functional equation from erdos-985). Splitting the zeros with
`|Im ρ| < T` by `k = ⌊|Im ρ|⌋` and counting each slice with `ZeroWindowCount` gives
`Σ_{|Im ρ| < T} m_ρ / |ρ| ≤ 4 C log(N(T + 2)) (1 + log(T + 1))` (`sum_stripZeros_le`).
-/

namespace PsiGRH

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- GRH: a zero of a primitive `L(s, χ)` in the open strip lies on `Re s = 1/2`. -/
theorem re_eq_half_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hρ : LFunction χ ρ = 0) : ρ.re = 1 / 2 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hΛ : completedLFunction χ ρ = 0 := by
    have hΓ := Erdos985.Analytic.StepAAux.gammaFactor_ne_zero χ h0
    have h := LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0)
    rw [hρ] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right hΓ
  rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
  · exfalso
    have h1' : completedLFunction χ (1 - (1 - ρ)) = 0 := by simpa using hΛ
    have h2 := Erdos985.Analytic.completedLFunction_inv_eq_zero hprim h1'
    have hne : (1 - ρ) ≠ 0 := fun h' => by
      have := congrArg Complex.re h'; simp at this; linarith
    have hne1 : (1 - ρ) ≠ 1 := fun h' => hρ0 (by linear_combination -h')
    exact hGRH N χ⁻¹ (1 - ρ) (by simp; linarith) (Or.inr hne1)
      (Erdos985.Analytic.LFunction_eq_zero_of_completed hne h2)
  · exact h
  · exfalso
    have hne1 : ρ ≠ 1 := fun h' => by rw [h'] at h1; simp at h1
    exact hGRH N χ ρ h (Or.inr hne1) hρ

/-- Under GRH, a zero `ρ` with `⌊|Im ρ|⌋ = k` has `|ρ| ≥ (k + 1)/2`. -/
lemma half_succ_le_norm {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ((⌊|ρ.im|⌋₊ : ℝ) + 1) / 2 ≤ ‖ρ‖ := by
  have h1 : (⌊|ρ.im|⌋₊ : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
  have h2 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h3 : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
  rw [hre, abs_of_pos (by norm_num)] at h3
  rcases Nat.eq_zero_or_pos ⌊|ρ.im|⌋₊ with h | h
  · rw [h]; simp; linarith
  · have : (1 : ℝ) ≤ ⌊|ρ.im|⌋₊ := by exact_mod_cast h
    linarith

/-- The slice `⌊|Im ρ|⌋ = k` of the strip lies in the two windows at heights `k` and `-k`. -/
lemma mem_windowZeros_of_floor {χ : DirichletCharacter ℂ N} {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ stripZeros χ T) :
    ρ ∈ windowZeros χ (⌊|ρ.im|⌋₊ : ℝ) ∨ ρ ∈ windowZeros χ (-(⌊|ρ.im|⌋₊ : ℝ)) := by
  obtain ⟨h0, h1, -, hL⟩ := hρ
  have hf1 : (⌊|ρ.im|⌋₊ : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
  have hf2 : |ρ.im| < (⌊|ρ.im|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  generalize ⌊|ρ.im|⌋₊ = k at hf1 hf2 ⊢
  rcases le_or_gt 0 ρ.im with h | h
  · left
    rw [abs_of_nonneg h] at hf1 hf2
    refine ⟨h0, h1, ?_, hL⟩
    rw [abs_le]; constructor <;> linarith
  · right
    rw [abs_of_neg h] at hf1 hf2
    refine ⟨h0, h1, ?_, hL⟩
    rw [abs_le]; constructor <;> linarith

/-- `Σ_{k < K} 1/(k+1) ≤ 1 + log K`. -/
lemma sum_range_inv_succ_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- Under GRH and `ZeroWindowCount` with constant `C`:
`Σ_{|Im ρ| < T} m_ρ / |ρ| ≤ 4 C log(N(T + 2)) (1 + log(T + 1))` for primitive `χ` and `T ≥ 1`. -/
theorem sum_stripZeros_le (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {C : ℝ}
    (hC : 0 < C)
    (hZ : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ t : ℝ, (windowZeros χ t).Finite ∧
        ∑ᶠ ρ ∈ windowZeros χ t, (analyticOrderNatAt (LFunction χ) ρ : ℝ) ≤
          C * Real.log (N * (|t| + 2)))
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (stripZeros χ T).Finite) :
    ∑ᶠ ρ ∈ stripZeros χ T, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖ ≤
      4 * C * Real.log (N * (T + 2)) * (1 + Real.log (T + 1)) := by
  classical
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt (LFunction χ) ρ : ℝ) with hm
  have hm0 : ∀ ρ, 0 ≤ m ρ := fun ρ => Nat.cast_nonneg _
  set S := hfin.toFinset with hS
  set K : ℕ := ⌈T⌉₊ with hK
  set g : ℂ → ℕ := fun ρ => ⌊|ρ.im|⌋₊ with hg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hLpos : 0 ≤ Real.log (N * (T + 2)) := Real.log_nonneg (by nlinarith)
  have hKT : (K : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
  -- each slice is bounded by two window counts
  have hslice : ∀ k ∈ Finset.range K,
      ∑ ρ ∈ S.filter (fun ρ => g ρ = k), m ρ ≤ 2 * C * Real.log (N * (T + 2)) := by
    intro k hk
    have hk' : (k : ℝ) + 2 ≤ T + 2 := by
      have : k < K := Finset.mem_range.mp hk
      have : (k : ℝ) + 1 ≤ K := by exact_mod_cast this
      linarith
    have hw : ∀ t : ℝ, |t| = k →
        ∑ᶠ ρ ∈ windowZeros χ t, m ρ ≤ C * Real.log (N * (T + 2)) := by
      intro t ht
      refine (hZ N χ hprim t).2.trans ?_
      have hN0 : (0 : ℝ) < N := by linarith
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hC.le
      rw [ht]; nlinarith
    obtain ⟨hfA, -⟩ := hZ N χ hprim (k : ℝ)
    obtain ⟨hfB, -⟩ := hZ N χ hprim (-(k : ℝ))
    have hA := hw k (by simp)
    have hB := hw (-(k : ℝ)) (by simp)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfA] at hA
    rw [finsum_mem_eq_finite_toFinset_sum _ hfB] at hB
    have hsub : S.filter (fun ρ => g ρ = k) ⊆ hfA.toFinset ∪ hfB.toFinset := by
      intro ρ hρ
      rw [Finset.mem_filter, hS, Set.Finite.mem_toFinset] at hρ
      obtain ⟨hρS, hgk⟩ := hρ
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      have := mem_windowZeros_of_floor hρS
      simp only [hg] at hgk
      rw [hgk] at this
      exact this
    calc ∑ ρ ∈ S.filter (fun ρ => g ρ = k), m ρ
        ≤ ∑ ρ ∈ hfA.toFinset ∪ hfB.toFinset, m ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => hm0 ρ)
      _ ≤ ∑ ρ ∈ hfA.toFinset, m ρ + ∑ ρ ∈ hfB.toFinset, m ρ := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ ρ ∈ hfA.toFinset ∩ hfB.toFinset, m ρ :=
            Finset.sum_nonneg fun ρ _ => hm0 ρ
          linarith
      _ ≤ 2 * C * Real.log (N * (T + 2)) := by linarith
  -- the slices cover the strip
  have hmaps : ∀ ρ ∈ S, g ρ ∈ Finset.range K := by
    intro ρ hρ
    rw [hS, Set.Finite.mem_toFinset] at hρ
    rw [Finset.mem_range]
    have h1 : |ρ.im| < T := hρ.2.2.1
    exact (Nat.floor_lt (abs_nonneg _)).mpr (h1.trans_le (Nat.le_ceil T))
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← hS,
    ← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.range K, ∑ ρ ∈ S.filter (fun ρ => g ρ = k), m ρ / ‖ρ‖
      ≤ ∑ k ∈ Finset.range K, (2 / ((k : ℝ) + 1)) * ∑ ρ ∈ S.filter (fun ρ => g ρ = k), m ρ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ρ hρ => ?_
        rw [Finset.mem_filter, hS, Set.Finite.mem_toFinset] at hρ
        obtain ⟨hρS, hgk⟩ := hρ
        have hre := re_eq_half_of_GRH hGRH hprim hρS.1 hρS.2.1 hρS.2.2.2
        have hn := half_succ_le_norm hre
        simp only [hg] at hgk
        rw [hgk] at hn
        have hpos : 0 < ((k : ℝ) + 1) / 2 := by positivity
        rw [div_le_iff₀ (hpos.trans_le hn)]
        calc m ρ = 2 / ((k : ℝ) + 1) * m ρ * (((k : ℝ) + 1) / 2) := by
              field_simp
          _ ≤ 2 / ((k : ℝ) + 1) * m ρ * ‖ρ‖ := by
              gcongr
    _ ≤ ∑ k ∈ Finset.range K, (2 / ((k : ℝ) + 1)) * (2 * C * Real.log (N * (T + 2))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        gcongr
        exact hslice k hk
    _ = 4 * C * Real.log (N * (T + 2)) *
          ∑ k ∈ Finset.range K, (1 : ℝ) / ((k : ℝ) + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ 4 * C * Real.log (N * (T + 2)) * (1 + Real.log (T + 1)) := by
        gcongr
        refine (sum_range_inv_succ_le K).trans ?_
        gcongr

end PsiGRH
