import Erdos985.Analytic.Hadamard
import Erdos985.Analytic.ExplicitFormula.ZeroSum
import Artin.Analytic.Core.VonMangoldt
import Artin.Analytic.Core.NonvanishingOne
import Artin.Analytic.Core.GammaPart

/-!
# The entire function `ξ_K` (blueprint A1)

For `D : ContinuationData K`, `D.ξ(s) = s (s - 1) Λ_K(s)` is entire with `ξ(1 - s) = ξ(s)`.

* `xi_one_ne_zero`: `ξ(1) = γ_K(1) · Res_{s=1} ζ_K ≠ 0`, from Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`; hence `ξ(0) = ξ(1) ≠ 0`.
* `xi_zero_re_mem`: every zero `ρ` of `ξ` has `0 < Re ρ < 1` (`ζ_K ≠ 0` on `Re s ≥ 1`, and the
  functional equation); under `DedekindZetaRH K`, `Re ρ = 1/2` (`xi_zero_re_eq_half`).
* `xi_growth`: `ξ` has order at most `1` (left as `sorry`, see its docstring).
* `hadamard`: Hadamard's product in logarithmic-derivative form, from erdos-985's
  `hadamard_logDeriv`.
* `logDeriv_Z_eq`: `ζ_K'/ζ_K = ξ'/ξ - 1/s - 1/(s - 1) - G_K(s)` for `Re s > 1`, with
  `G_K = γ_K'/γ_K = ½ log |d_K| + r₁ Γ_ℝ'/Γ_ℝ + r₂ Γ_ℂ'/Γ_ℂ` (`gammaLogDerivK`).
* `hasSum_re_logDeriv_xi`: under RH, `Re ξ'/ξ(s) = ∑_ρ m_ρ Re 1/(s - ρ)` (the Hadamard constant
  satisfies `Re b = -∑ Re 1/ρ`, by the functional equation at `s = 3/2`).
-/

namespace Artin.Analytic

open Complex NumberField ArtinPrimitiveRootsConjecture Filter Topology

variable {K : Type*} [Field K] [NumberField K]

lemma Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [← Gammaℝ_mul_Gammaℝ_add_one]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs)
    (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))

lemma abs_discr_pos (K : Type*) [Field K] [NumberField K] : 0 < |(discr K : ℝ)| :=
  abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))

lemma gammaFactorK_ne_zero {s : ℂ} (hs : 0 < s.re) : gammaFactorK K s ≠ 0 := by
  unfold gammaFactorK
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)))
    (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => (abs_discr_pos K).ne' (by exact_mod_cast h.1)

lemma hasDerivAt_Gammaℝ' {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gammaℝ (Gammaℝ s * gR 0 s) s := by
  have h := Erdos985.Analytic.StepAAux.hasDerivAt_Gammaℝ hs
  convert h using 2
  simp [gR]

lemma hasDerivAt_Gammaℝ_add_one {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun w => Gammaℝ (w + 1)) (Gammaℝ (s + 1) * gR 0 (s + 1)) s :=
  (hasDerivAt_Gammaℝ' (s := s + 1) (by simp; linarith)).comp_add_const s 1

lemma Gammaℂ_eq_fun : Gammaℂ = fun w => Gammaℝ w * Gammaℝ (w + 1) :=
  funext fun w => (Gammaℝ_mul_Gammaℝ_add_one w).symm

lemma differentiableAt_Gammaℂ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℂ s := by
  rw [Gammaℂ_eq_fun]
  exact (hasDerivAt_Gammaℝ' hs).differentiableAt.mul (hasDerivAt_Gammaℝ_add_one hs).differentiableAt

lemma logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) : logDeriv Gammaℝ s = gR 0 s := by
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ' hs).deriv, mul_div_cancel_left₀ _
    (Gammaℝ_ne_zero_of_re_pos hs)]

lemma logDeriv_Gammaℂ {s : ℂ} (hs : 0 < s.re) : logDeriv Gammaℂ s = gR 0 s + gR 1 s := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have : Gammaℂ = Gammaℝ * fun w => Gammaℝ (w + 1) :=
    funext fun w => (Gammaℝ_mul_Gammaℝ_add_one w).symm
  rw [this, logDeriv_mul (f := Gammaℝ) (g := fun w => Gammaℝ (w + 1)) s
    (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos hs1)
    (hasDerivAt_Gammaℝ' hs).differentiableAt (hasDerivAt_Gammaℝ_add_one hs).differentiableAt,
    logDeriv_Gammaℝ hs]
  congr 1
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ_add_one hs).deriv,
    mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos hs1)]
  simp only [gR]
  push_cast
  ring_nf

variable (K) in
/-- `G_K = γ_K'/γ_K = ½ log |d_K| + r₁ Γ_ℝ'/Γ_ℝ + r₂ Γ_ℂ'/Γ_ℂ`. -/
noncomputable def gammaLogDerivK (s : ℂ) : ℂ :=
  (1 / 2) * (Real.log |(discr K : ℝ)| : ℂ) + InfinitePlace.nrRealPlaces K * gR 0 s +
    InfinitePlace.nrComplexPlaces K * (gR 0 s + gR 1 s)

lemma differentiableAt_gammaFactorK {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gammaFactorK K) s := by
  unfold gammaFactorK
  have hc : (((|(discr K : ℝ)| : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (abs_discr_pos K).ne'
  refine ((((differentiableAt_id.div_const 2).const_cpow (Or.inl hc))).mul
    ((hasDerivAt_Gammaℝ' hs).differentiableAt.pow _)).mul
    ((differentiableAt_Gammaℂ hs).pow _)

lemma logDeriv_gammaFactorK {s : ℂ} (hs : 0 < s.re) :
    logDeriv (gammaFactorK K) s = gammaLogDerivK K s := by
  have hc : (((|(discr K : ℝ)| : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (abs_discr_pos K).ne'
  set c : ℂ := (((|(discr K : ℝ)| : ℝ)) : ℂ)
  set A : ℂ → ℂ := fun w => c ^ (w / 2)
  set B : ℂ → ℂ := fun w => Gammaℝ w ^ InfinitePlace.nrRealPlaces K
  set C : ℂ → ℂ := fun w => Gammaℂ w ^ InfinitePlace.nrComplexPlaces K
  have hA : HasDerivAt A (c ^ (s / 2) * Complex.log c * (1 / 2)) s :=
    ((hasDerivAt_id s).div_const 2).const_cpow (Or.inl hc)
  have hA0 : A s ≠ 0 := by
    simp only [A]; rw [Ne, cpow_eq_zero_iff]; exact fun h => hc h.1
  have hB : DifferentiableAt ℂ B s := (hasDerivAt_Gammaℝ' hs).differentiableAt.pow _
  have hC : DifferentiableAt ℂ C s := (differentiableAt_Gammaℂ hs).pow _
  have hB0 : B s ≠ 0 := pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)
  have hC0 : C s ≠ 0 := pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs)
  have heq : gammaFactorK K = A * B * C := rfl
  rw [heq, logDeriv_mul (f := A * B) (g := C) s (mul_ne_zero hA0 hB0) hC0
      (hA.differentiableAt.mul hB) hC,
    logDeriv_mul (f := A) (g := B) s hA0 hB0 hA.differentiableAt hB,
    logDeriv_fun_pow (hasDerivAt_Gammaℝ' hs).differentiableAt,
    logDeriv_fun_pow (differentiableAt_Gammaℂ hs), logDeriv_Gammaℝ hs, logDeriv_Gammaℂ hs,
    logDeriv_apply, hA.deriv, mul_assoc, mul_div_cancel_left₀ _ hA0]
  have hlog : Complex.log c = (Real.log |(discr K : ℝ)| : ℂ) :=
    (ofReal_log (abs_nonneg _)).symm
  rw [hlog, gammaLogDerivK]
  ring

namespace ContinuationData

variable (D : ContinuationData K)

lemma Z_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) : D.Z s = dedekindZeta K s :=
  D.isDedekindZeta.2 s hs

lemma Z_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : D.Z s ≠ 0 := by
  rw [D.Z_eq_dedekindZeta hs]; exact dedekindZeta_ne_zero K hs

/-- **`ζ_K` has no zeros on `Re s = 1`** (de la Vallée Poussin; Landau for number fields). The
classical proof: for `σ > 1`, `log ζ_K(σ + it)` is a Dirichlet series with non-negative
coefficients (Euler product), so `|ζ_K(σ)³ ζ_K(σ + it)⁴ ζ_K(σ + 2it)| ≥ 1`; a zero at `1 + it`
(`t ≠ 0`) would make the left side `→ 0` as `σ → 1⁺`, because `ζ_K` has at most a simple pole at
`1` (`ξ` is entire) and is holomorphic at `1 + 2it`. See Narkiewicz, *Elementary and Analytic
Theory of Algebraic Numbers*, Lemma 7.4, or Lang, *Algebraic Number Theory*, XV §1. At `t = 0`,
`ζ_K` has its pole: `(s - 1) Z(s)` tends to the positive residue. -/
theorem Z_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1) : D.Z s ≠ 0 :=
  D.Z_ne_zero_on_one_line hs hs1

lemma gammaFactorK_one_ne_zero : gammaFactorK K 1 ≠ 0 := gammaFactorK_ne_zero (by norm_num)

lemma continuous_gammaFactorK_at_one : ContinuousAt (gammaFactorK K) 1 :=
  (differentiableAt_gammaFactorK (by norm_num)).continuousAt

/-- `ξ(1) = γ_K(1) · Res_{s=1} ζ_K`. -/
theorem xi_one : D.ξ 1 = gammaFactorK K 1 * (dedekindZeta_residue K : ℂ) := by
  have hlim : Tendsto (fun σ : ℝ => D.ξ σ) (𝓝[>] 1)
      (𝓝 ((1 : ℂ) * gammaFactorK K 1 * (dedekindZeta_residue K : ℂ))) := by
    have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
      have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
      simpa using this
    have h2 : Tendsto (fun σ : ℝ => gammaFactorK K σ) (𝓝[>] 1) (𝓝 (gammaFactorK K 1)) :=
      continuous_gammaFactorK_at_one.tendsto.comp h1
    have h3 := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
    have h3' : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * dedekindZeta K σ) (𝓝[>] 1)
        (𝓝 (dedekindZeta_residue K : ℂ)) := by
      convert h3 using 2
    refine ((h1.mul h2).mul h3').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
    have h1' : (σ : ℂ) ≠ 1 := fun h => by rw [h] at hσ'; simp at hσ'
    rw [D.ξ_eq σ (by linarith) h1', completedOf, D.Z_eq_dedekindZeta hσ']
    ring
  have hcont : Tendsto (fun σ : ℝ => D.ξ σ) (𝓝[>] 1) (𝓝 (D.ξ 1)) := by
    have := ((D.differentiable_ξ.continuous.comp continuous_ofReal).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 1))
    rw [Function.comp_apply, ofReal_one] at this
    exact this
  rw [tendsto_nhds_unique hcont hlim, one_mul]

theorem xi_one_ne_zero : D.ξ 1 ≠ 0 := by
  rw [xi_one]
  exact mul_ne_zero gammaFactorK_one_ne_zero
    (by exact_mod_cast (dedekindZeta_residue_pos K).ne')

theorem xi_zero_ne_zero : D.ξ 0 ≠ 0 := by
  have := D.ξ_one_sub 1
  rw [sub_self] at this
  rw [this]; exact D.xi_one_ne_zero

theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : D.ξ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact D.xi_one_ne_zero
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  rw [D.ξ_eq s (by linarith) hs1, completedOf]
  refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.2 hs1))
    (mul_ne_zero (gammaFactorK_ne_zero (by linarith)) ?_)
  rcases hs.lt_or_eq with h | h
  · exact D.Z_ne_zero_of_one_lt_re h
  · exact D.Z_ne_zero_of_re_eq_one h.symm hs1

/-- Every zero of `ξ` lies in the open critical strip. -/
theorem xi_zero_re_mem {ρ : ℂ} (hρ : D.ξ ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra h
    push Not at h
    apply D.xi_ne_zero_of_one_le_re (s := 1 - ρ) (by simp; linarith)
    rw [D.ξ_one_sub, hρ]
  · by_contra h
    push Not at h
    exact D.xi_ne_zero_of_one_le_re h hρ

/-- Under RH for `ζ_K`, every zero of `ξ` has real part `1/2`. -/
theorem xi_zero_re_eq_half (hRH : DedekindZetaRH K) {ρ : ℂ} (hρ : D.ξ ρ = 0) :
    ρ.re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := D.xi_zero_re_mem hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  refine hRH D.Z D.isDedekindZeta ρ h0 h1 ?_
  rw [D.ξ_eq ρ h0 hρ1, completedOf] at hρ
  rcases mul_eq_zero.1 hρ with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h hρ0
    · exact absurd (sub_eq_zero.1 h) hρ1
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h (gammaFactorK_ne_zero h0)
    · exact h

/-- **`ξ` has order at most `1`** (blueprint A1):
`‖ξ(s)‖ ≤ C exp(C ‖s‖ log(‖s‖ + 2))`. Proof: by `ξ(1 - s) = ξ(s)` it suffices to take
`Re s ≥ 1/2`. On `1/2 ≤ Re s ≤ 2` this is `D.strip_bound`. For `Re s ≥ 2`,
`ξ(s) = s (s - 1) |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` with `|ζ_K(s)| ≤ ζ_K(2)`,
`|Γ(w)| ≤ Γ(Re w)` and Stirling's `Γ(σ) ≤ σ^σ`, so each factor is `≤ exp(O(|s| log(|s| + 2)))`.
(Titchmarsh, *Theory of the Riemann zeta function*, 2.12, for `ζ`; Lang, *Algebraic Number
Theory*, XVII §1, for `ζ_K`.) The constant `C` may depend on `K`: only the existence of the
Hadamard product uses it. -/
theorem xi_growth :
    ∃ C : ℝ, ∀ s : ℂ, ‖D.ξ s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  sorry

/-- The multiplicity of a zero of `ξ`. -/
noncomputable def mult (ρ : {ρ : ℂ // D.ξ ρ = 0}) : ℕ := analyticOrderNatAt D.ξ ρ

/-- **Hadamard's product for `ξ`**, logarithmic-derivative form (erdos-985's
`hadamard_logDeriv`). -/
theorem hadamard :
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // D.ξ ρ = 0} =>
        (D.mult ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, D.ξ z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv D.ξ z / D.ξ z = b + ∑' ρ : {ρ : ℂ // D.ξ ρ = 0},
        (D.mult ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) :=
  Erdos985.Analytic.hadamard_logDeriv D.differentiable_ξ D.xi_zero_ne_zero D.xi_growth

/-- Every zero of `ξ` has positive multiplicity. -/
theorem mult_ne_zero (ρ : {ρ : ℂ // D.ξ ρ = 0}) : D.mult ρ ≠ 0 := by
  have han : AnalyticOnNhd ℂ D.ξ Set.univ :=
    D.differentiable_ξ.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt D.ξ 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr D.xi_zero_ne_zero))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ (ρ : ℂ)) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [mult] at hm
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h ρ.2

/-- The zeros of `ξ` form a countable set. -/
theorem countable_zeros : Countable {ρ : ℂ // D.ξ ρ = 0} := by
  have hs := D.hadamard.1 1 one_pos
  rw [← Set.countable_univ_iff]
  convert hs.countable_support
  symm
  rw [Function.support_eq_univ]
  intro ρ
  have hm := D.mult_ne_zero ρ
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (D.xi_zero_re_mem ρ.2).1.ne' (by simp [h])
  have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  positivity

/-- `ζ_K'/ζ_K = ξ'/ξ - 1/s - 1/(s - 1) - G_K` for `Re s > 1`. -/
theorem logDeriv_Z_eq {s : ℂ} (hs : 1 < s.re) :
    deriv D.Z s / D.Z s =
      deriv D.ξ s / D.ξ s - 1 / s - 1 / (s - 1) - gammaLogDerivK K s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hs0' : 0 < s.re := by linarith
  have hev : D.ξ =ᶠ[𝓝 s] (fun w : ℂ => w) * (fun w : ℂ => w - 1) * gammaFactorK K * D.Z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show s ∈ {w : ℂ | 1 < w.re} from hs)] with w hw
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    have hw' : 1 < w.re := hw
    rw [D.ξ_eq w (by linarith) hw1, completedOf]
    simp only [Pi.mul_apply]
    ring
  have hZd : DifferentiableAt ℂ D.Z s :=
    (D.isDedekindZeta.1.differentiableAt (isOpen_compl_singleton.mem_nhds hs1))
  have hZ0 := D.Z_ne_zero_of_one_lt_re hs
  have hg0 := gammaFactorK_ne_zero (K := K) hs0'
  have hgd := differentiableAt_gammaFactorK (K := K) hs0'
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have hid1 : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := differentiableAt_id.sub_const 1
  have hL : logDeriv D.ξ s = 1 / s + 1 / (s - 1) + gammaLogDerivK K s + deriv D.Z s / D.Z s := by
    rw [(logDeriv_congr_nhds hev).eq_of_nhds,
      logDeriv_mul (f := (fun w : ℂ => w) * (fun w : ℂ => w - 1) * gammaFactorK K) (g := D.Z) s
        (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.2 hs1)) hg0) hZ0 ((hid.mul hid1).mul hgd) hZd,
      logDeriv_mul (f := (fun w : ℂ => w) * (fun w : ℂ => w - 1)) (g := gammaFactorK K) s
        (mul_ne_zero hs0 (sub_ne_zero.2 hs1)) hg0 (hid.mul hid1) hgd,
      logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s hs0 (sub_ne_zero.2 hs1)
        hid hid1, logDeriv_gammaFactorK hs0']
    simp only [logDeriv_apply, deriv_id'', deriv_sub_const]
  rw [logDeriv_apply] at hL
  rw [hL]
  ring

/-- Logarithmic derivative of the functional equation: `ξ'/ξ(1 - s) = -ξ'/ξ(s)`. -/
theorem logDeriv_xi_one_sub (s : ℂ) :
    deriv D.ξ (1 - s) / D.ξ (1 - s) = -(deriv D.ξ s / D.ξ s) := by
  have hF : HasDerivAt (fun w => D.ξ (1 - w)) (deriv D.ξ (1 - s) * (-1)) s :=
    (D.differentiable_ξ (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
  have hfun : (fun w => D.ξ (1 - w)) = D.ξ := funext D.ξ_one_sub
  rw [hfun] at hF
  rw [hF.deriv, D.ξ_one_sub]
  ring

/-- Under RH, `Re ξ'/ξ(s) = ∑_ρ m_ρ Re 1/(s - ρ)`, for `s` not a zero. The Hadamard constant
drops out: at `s = 3/2` the functional equation `ξ'/ξ(-1/2) = -ξ'/ξ(3/2)` and
`Re 1/(-1/2 - ρ) = -Re 1/(3/2 - ρ)` (for `Re ρ = 1/2`) give `Re ξ'/ξ(3/2) = ∑ m_ρ Re 1/(3/2 - ρ)`,
hence `Re b = -∑ m_ρ Re 1/ρ`, a convergent sum since `Re 1/ρ = 1/(2|ρ|²)`. -/
theorem hasSum_re_logDeriv_xi (hRH : DedekindZetaRH K) {s : ℂ} (hs : D.ξ s ≠ 0) :
    HasSum (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℝ) * (1 / (s - ρ)).re)
      (deriv D.ξ s / D.ξ s).re := by
  obtain ⟨hsumε, b, H⟩ := D.hadamard
  set x : ℝ := 3 / 2 with hx
  have hx0 : D.ξ x ≠ 0 := D.xi_ne_zero_of_one_le_re (by simp [hx]; norm_num)
  have hx1 : D.ξ (1 - x) ≠ 0 := by rw [D.ξ_one_sub]; exact hx0
  obtain ⟨sA, eA⟩ := H x hx0
  obtain ⟨sB, eB⟩ := H (1 - x) hx1
  obtain ⟨sS, eS⟩ := H s hs
  have hcrit : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => D.xi_zero_re_eq_half hRH ρ.2
  -- Step 1: `Re ξ'/ξ(3/2) = ∑ m Re 1/(3/2 - ρ)`.
  have h1 : HasSum (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℝ) * (1 / ((x : ℂ) - ρ)).re)
      (deriv D.ξ x / D.ξ x).re := by
    have hd := Complex.reCLM.hasSum (sA.hasSum.sub sB.hasSum)
    have hterm : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0},
        Complex.reCLM ((D.mult ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
          - (D.mult ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ))
          = 2 * ((D.mult ρ : ℝ) * (1 / ((x : ℂ) - ρ)).re) := by
      intro ρ
      have := Erdos985.Analytic.ZeroSumAux.re_inv_reflect (hcrit ρ) x
      simp only [Complex.reCLM_apply, sub_re, mul_re, add_re, natCast_re, natCast_im, zero_mul,
        sub_zero]
      rw [this]; ring
    simp only [hterm] at hd
    have hval : Complex.reCLM (∑' ρ : {ρ : ℂ // D.ξ ρ = 0},
          (D.mult ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
        - ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ))
        = 2 * (deriv D.ξ x / D.ξ x).re := by
      have hFE := D.logDeriv_xi_one_sub x
      have e : ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)
          - ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℂ) * (1 / ((1 : ℂ) - x - ρ) + 1 / ρ)
          = 2 * (deriv D.ξ x / D.ξ x) := by
        have eA' := eA; have eB' := eB
        rw [hFE] at eB'
        linear_combination (-1 : ℂ) * eA' + eB'
      rw [e]
      simp
    rw [hval] at hd
    have := hd.div_const 2
    simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at this
    exact this
  -- Step 2: `∑ m Re 1/ρ = -Re b`.
  have h2 : HasSum (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℝ) * (1 / (ρ : ℂ)).re) (-b.re) := by
    have hA := Complex.reCLM.hasSum sA.hasSum
    have e : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0}, Complex.reCLM ((D.mult ρ : ℂ) *
        (1 / ((x : ℂ) - ρ) + 1 / ρ)) = (D.mult ρ : ℝ) * (1 / ((x : ℂ) - ρ)).re
          + (D.mult ρ : ℝ) * (1 / (ρ : ℂ)).re := by
      intro ρ
      simp only [Complex.reCLM_apply, mul_re, add_re, natCast_re, natCast_im, zero_mul, sub_zero]
      ring
    simp only [e] at hA
    have hv : Complex.reCLM (∑' ρ : {ρ : ℂ // D.ξ ρ = 0},
        (D.mult ρ : ℂ) * (1 / ((x : ℂ) - ρ) + 1 / ρ)) = (deriv D.ξ x / D.ξ x).re - b.re := by
      rw [eA]; simp
    rw [hv] at hA
    have := hA.sub h1
    simp only [add_sub_cancel_left] at this
    convert this using 1
    ring
  -- Step 3: general `s`.
  have hS := Complex.reCLM.hasSum sS.hasSum
  have e : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0}, Complex.reCLM ((D.mult ρ : ℂ) *
      (1 / (s - ρ) + 1 / ρ)) = (D.mult ρ : ℝ) * (1 / (s - ρ)).re
        + (D.mult ρ : ℝ) * (1 / (ρ : ℂ)).re := by
    intro ρ
    simp only [Complex.reCLM_apply, mul_re, add_re, natCast_re, natCast_im, zero_mul, sub_zero]
    ring
  simp only [e] at hS
  have hv : Complex.reCLM (∑' ρ : {ρ : ℂ // D.ξ ρ = 0},
      (D.mult ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) = (deriv D.ξ s / D.ξ s).re - b.re := by
    rw [eS]; simp
  rw [hv] at hS
  have := hS.sub h2
  simp only [add_sub_cancel_right] at this
  convert this using 1
  ring

end ContinuationData

end Artin.Analytic
