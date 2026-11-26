import Mathlib

/-!
# Step 7: Hadamard three-lines with logarithmic growth

If `F` is holomorphic on the closed strip `a ≤ σ ≤ b`, `‖F‖ ≤ A log (|t| + 2)` on the strip and
`‖F‖ ≤ B` on the right edge, then `‖F(σ + it)‖ ≤ C log (|t| + 2)^{(b-σ)/(b-a)}`.

Proof: `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` applied to
`F(s) exp((s - i t₀)²)`, which is bounded on the strip and concentrated at height `t₀`.
-/

namespace Lindelof

open Complex

/-- `log (|t| + 2)` times a Gaussian centred at `t₀` is at most `5 log (|t₀| + 2)`. -/
lemma log_mul_exp_neg_sq_le (t t₀ : ℝ) :
    Real.log (|t| + 2) * Real.exp (-(t - t₀) ^ 2) ≤ 5 * Real.log (|t₀| + 2) := by
  set u := |t - t₀| with hu
  set L := Real.log (|t₀| + 2) with hL
  have hu0 : 0 ≤ u := abs_nonneg _
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t₀])
  have hlog2 := Real.log_two_gt_d9
  have h1 : Real.log (|t| + 2) ≤ L + Real.log (u + 2) := by
    rw [hL, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have : |t| ≤ |t₀| + u := by
      have := abs_sub_abs_le_abs_sub t t₀; linarith
    nlinarith [abs_nonneg t₀]
  have h2 : Real.log (u + 2) ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by positivity); linarith
  have h3 : Real.log (|t| + 2) ≤ L * (2 * u + 3) := by nlinarith
  have hsq : (t - t₀) ^ 2 = u ^ 2 := (sq_abs _).symm
  rw [hsq]
  have he : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by linarith [Real.add_one_le_exp (u ^ 2)]
  have hpos : 0 < Real.exp (-u ^ 2) := Real.exp_pos _
  have hmul : Real.exp (-u ^ 2) * Real.exp (u ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : (2 * u + 3) * Real.exp (-u ^ 2) ≤ 5 := by
    have : 2 * u + 3 ≤ 5 * Real.exp (u ^ 2) := by nlinarith
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  calc Real.log (|t| + 2) * Real.exp (-u ^ 2) ≤ L * (2 * u + 3) * Real.exp (-u ^ 2) :=
        mul_le_mul_of_nonneg_right h3 hpos.le
    _ = L * ((2 * u + 3) * Real.exp (-u ^ 2)) := by ring
    _ ≤ L * 5 := mul_le_mul_of_nonneg_left h4 hL0
    _ = 5 * L := by ring

lemma norm_exp_shift_sq (s : ℂ) (t₀ : ℝ) :
    ‖exp ((s - t₀ * I) ^ 2)‖ = Real.exp (s.re ^ 2 - (s.im - t₀) ^ 2) := by
  rw [Complex.norm_exp]; congr 1; simp [pow_two]

theorem norm_le_log_rpow_of_strip {F : ℂ → ℂ} {a b A B : ℝ} (hab : a < b)
    (hF : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hA : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ A * Real.log (|s.im| + 2))
    (hB : ∀ s : ℂ, s.re = b → ‖F s‖ ≤ B) :
    ∃ C : ℝ, ∀ σ t : ℝ, a ≤ σ → σ ≤ b →
      ‖F (σ + t * I)‖ ≤ C * Real.log (|t| + 2) ^ ((b - σ) / (b - a)) := by
  set A' := max A 1
  set B' := max B 1
  set K := max (a ^ 2) (b ^ 2)
  have hA'1 : 1 ≤ A' := le_max_right _ _
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hK1 : 1 ≤ Real.exp K := Real.one_le_exp (le_max_of_le_left (sq_nonneg a))
  have hlogpos : ∀ x : ℝ, 0 < Real.log (|x| + 2) := fun x =>
    Real.log_pos (by linarith [abs_nonneg x])
  have hA' : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ A' * Real.log (|s.im| + 2) := fun s h1 h2 =>
    (hA s h1 h2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogpos _).le)
  have hsqK : ∀ σ : ℝ, a ≤ σ → σ ≤ b → σ ^ 2 ≤ K := fun σ h1 h2 => by
    rcases le_total 0 σ with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  refine ⟨5 * A' * Real.exp K * (B' * Real.exp K), fun σ t₀ hσa hσb => ?_⟩
  set G : ℂ → ℂ := fun s => F s * exp ((s - t₀ * I) ^ 2) with hG
  set L := Real.log (|t₀| + 2)
  have hL : 0 < L := hlogpos t₀
  have hGd : DifferentiableOn ℂ G {s : ℂ | a ≤ s.re ∧ s.re ≤ b} :=
    hF.mul (by fun_prop)
  -- bound on the whole closed strip
  have hGbd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖G s‖ ≤ 5 * A' * Real.exp K * L := by
    intro s h1 h2
    simp only [hG, norm_mul, norm_exp_shift_sq]
    have hexp : Real.exp (s.re ^ 2 - (s.im - t₀) ^ 2) =
        Real.exp (s.re ^ 2) * Real.exp (-(s.im - t₀) ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hk : Real.exp (s.re ^ 2) ≤ Real.exp K := Real.exp_le_exp.mpr (hsqK _ h1 h2)
    have hg := log_mul_exp_neg_sq_le s.im t₀
    calc ‖F s‖ * (Real.exp (s.re ^ 2) * Real.exp (-(s.im - t₀) ^ 2))
        ≤ A' * Real.log (|s.im| + 2) * (Real.exp K * Real.exp (-(s.im - t₀) ^ 2)) := by
          have hsA := hA' s h1 h2
          gcongr
          exact (norm_nonneg _).trans hsA
      _ = A' * Real.exp K * (Real.log (|s.im| + 2) * Real.exp (-(s.im - t₀) ^ 2)) := by ring
      _ ≤ A' * Real.exp K * (5 * L) := by gcongr
      _ = 5 * A' * Real.exp K * L := by ring
  have hright : ∀ s ∈ re ⁻¹' {b}, ‖G s‖ ≤ B' * Real.exp K := by
    intro s hs
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs
    simp only [hG, norm_mul, norm_exp_shift_sq]
    have hk : Real.exp (s.re ^ 2 - (s.im - t₀) ^ 2) ≤ Real.exp K :=
      Real.exp_le_exp.mpr (by nlinarith [hsqK s.re (by linarith) (by linarith)])
    gcongr
    exact (hB s hs).trans (le_max_left _ _)
  have hstrip : ∀ s ∈ Complex.HadamardThreeLines.verticalClosedStrip a b,
      a ≤ s.re ∧ s.re ≤ b := fun s hs => hs
  have hdc : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip a b) := by
    apply DifferentiableOn.diffContOnCl
    refine hGd.mono (closure_minimal ?_ ?_)
    · intro s hs; exact ⟨hs.1.le, hs.2.le⟩
    · exact (isClosed_le continuous_const continuous_re).inter
        (isClosed_le continuous_re continuous_const)
  have hbdd : BddAbove ((norm ∘ G) '' Complex.HadamardThreeLines.verticalClosedStrip a b) := by
    refine ⟨5 * A' * Real.exp K * L, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hGbd s (hstrip s hs).1 (hstrip s hs).2
  set z : ℂ := σ + t₀ * I
  have hzre : z.re = σ := by simp [z]
  have hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip a b := by
    show z.re ∈ Set.Icc a b; rw [hzre]; exact ⟨hσa, hσb⟩
  have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab hz hdc hbdd
    (fun s hs => hGbd s (le_of_eq hs.symm) (by rw [show s.re = a from hs]; exact hab.le)) hright
  rw [hzre] at h3
  set θ := (σ - a) / (b - a)
  have hba : 0 < b - a := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hba.le
  have hθ1 : θ ≤ 1 := (div_le_one hba).mpr (by linarith)
  have hexpo : 1 - θ = (b - σ) / (b - a) := by
    simp only [θ]; field_simp; ring
  -- `‖F z‖ ≤ ‖G z‖`
  have hFG : ‖F z‖ ≤ ‖G z‖ := by
    simp only [hG, norm_mul, norm_exp_shift_sq]
    have : z.im = t₀ := by simp [z]
    rw [this, sub_self]
    have : 1 ≤ Real.exp (z.re ^ 2 - 0 ^ 2) := Real.one_le_exp (by nlinarith)
    nlinarith [norm_nonneg (F z)]
  set P := 5 * A' * Real.exp K
  have hP1 : 1 ≤ P := by
    have : (1:ℝ) ≤ 5 * A' := by linarith
    simpa [P] using one_le_mul_of_one_le_of_one_le this hK1
  have hQ1 : 1 ≤ B' * Real.exp K := one_le_mul_of_one_le_of_one_le hB'1 hK1
  have hPpow : P ^ (1 - θ) ≤ P := by
    simpa using Real.rpow_le_rpow_of_exponent_le hP1 (show 1 - θ ≤ 1 by linarith)
  have hQpow : (B' * Real.exp K) ^ θ ≤ B' * Real.exp K := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ1 hθ1
  have hP0 : 0 ≤ P := by linarith
  rw [Real.mul_rpow hP0 hL.le] at h3
  rw [← hexpo]
  have hLp : 0 ≤ L ^ (1 - θ) := Real.rpow_nonneg hL.le _
  calc ‖F z‖ ≤ ‖G z‖ := hFG
    _ ≤ P ^ (1 - θ) * L ^ (1 - θ) * (B' * Real.exp K) ^ θ := h3
    _ ≤ P * L ^ (1 - θ) * (B' * Real.exp K) := by
        gcongr
    _ = P * (B' * Real.exp K) * L ^ (1 - θ) := by ring
end Lindelof
