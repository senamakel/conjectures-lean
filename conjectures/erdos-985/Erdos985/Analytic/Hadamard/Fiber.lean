import Mathlib
import Vendor.PNT.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order

/-!
# Auxiliary lemmas for `hadamard_logDeriv`

* Passing from sums over the PNT+ multiplicity index `divisorZeroIndex₀ f univ` (each zero `ρ`
  repeated `analyticOrderNatAt f ρ` times) to multiplicity-weighted sums over `{ρ // f ρ = 0}`.
* The growth hypothesis `‖f z‖ ≤ C exp(C ‖z‖ log(‖z‖ + 2))` implies `EntireOfOrderAtMost 1 f`.
-/

namespace Erdos985.Analytic.HadamardAux

open Complex.Hadamard

variable {f : ℂ → ℂ}

lemma val_isZero (hf : Differentiable ℂ f) (p : divisorZeroIndex₀ f Set.univ) :
    f (divisorZeroIndex₀_val p) = 0 := by
  have h := divisorZeroIndex₀_val_mem_divisor_support p
  rw [divisor_univ_eq_analyticOrderNatAt_int hf] at h
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by exact_mod_cast h)

/-- The zero underlying a multiplicity index. -/
noncomputable def zeroProj (hf : Differentiable ℂ f) (p : divisorZeroIndex₀ f Set.univ) :
    {ρ : ℂ // f ρ = 0} :=
  ⟨divisorZeroIndex₀_val p, val_isZero hf p⟩

/-- A sum over the multiplicity index is a multiplicity-weighted sum over the zero set. -/
lemma hasSum_weighted {E : Type*} [NormedAddCommGroup E]
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (g : ℂ → E) {a : E}
    (h : HasSum (fun p : divisorZeroIndex₀ f Set.univ => g (divisorZeroIndex₀_val p)) a) :
    HasSum (fun ρ : {ρ : ℂ // f ρ = 0} => analyticOrderNatAt f ρ • g ρ) a := by
  classical
  set π := zeroProj hf
  have h' := (Equiv.sigmaFiberEquiv π).hasSum_iff.mpr h
  refine h'.sigma fun ρ => ?_
  have hiff : ∀ p, π p = ρ ↔ p ∈ divisorZeroIndex₀_fiberFinset f (ρ : ℂ) := by
    intro p
    rw [mem_divisorZeroIndex₀_fiberFinset]
    simp [π, zeroProj, Subtype.ext_iff]
  let _ : Fintype {p // π p = ρ} :=
    Fintype.subtype (divisorZeroIndex₀_fiberFinset f (ρ : ℂ)) (fun p => (hiff p).symm)
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h0 => hf0 (by simpa [h0] using ρ.2)
  have hcard : Fintype.card {p // π p = ρ} = analyticOrderNatAt f ρ := by
    rw [← divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt hf hρ0]
    exact Fintype.card_of_subtype _ (fun p => (hiff p).symm)
  have hc : ∀ c : {p // π p = ρ},
      g (divisorZeroIndex₀_val ((Equiv.sigmaFiberEquiv π) ⟨ρ, c⟩)) = g ρ := by
    intro c
    have : divisorZeroIndex₀_val c.1 = ρ := congrArg Subtype.val c.2
    simp [Equiv.sigmaFiberEquiv_apply, this]
  simp only [Function.comp_def, hc]
  rw [← hcard]
  convert hasSum_fintype (fun _ : {p // π p = ρ} => g ρ) using 1
  simp

/-- The order-one growth hypothesis gives finite order at most one in the PNT+ sense. -/
lemma entireOfOrderAtMost_one (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    EntireOfOrderAtMost 1 f := by
  obtain ⟨C, hC⟩ := hgrowth
  have hCpos : 0 < C := by
    have h0 := hC 0
    simp only [norm_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] at h0
    exact lt_of_lt_of_le (norm_pos_iff.2 hf0) h0
  refine ⟨hf, fun ε hε => ?_⟩
  refine ⟨|Real.log C| + C * (1 + 1 / ε) + 1, by positivity, fun z => ?_⟩
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have h1 : 1 ≤ 1 + r := by linarith
  set Y := (1 + r) ^ ((1 : ℝ) + ε)
  have hA : 1 + r ≤ Y := Real.self_le_rpow_of_one_le h1 (by linarith)
  have hB : 1 ≤ Y := le_trans h1 hA
  have hlog : Real.log (r + 2) ≤ 1 + (1 + r) ^ ε / ε := by
    have h4 : Real.log (r + 2) ≤ Real.log 2 + Real.log (1 + r) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have h3 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 1 + r) hε
    linarith
  have hmul : (1 + r) * (1 + r) ^ ε = Y := by
    simp only [Y]
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have e1 : Real.log C ≤ |Real.log C| * Y :=
    le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hB)
  have e2 : C * r * Real.log (r + 2) ≤ C * (1 + 1 / ε) * Y := by
    calc C * r * Real.log (r + 2) ≤ C * (1 + r) * (1 + (1 + r) ^ ε / ε) := by
          gcongr
          · exact Real.log_nonneg (by linarith)
          · linarith
      _ = C * ((1 + r) + ((1 + r) * (1 + r) ^ ε) / ε) := by ring
      _ = C * ((1 + r) + Y / ε) := by rw [hmul]
      _ ≤ C * (Y + Y / ε) := by gcongr
      _ = C * (1 + 1 / ε) * Y := by ring
  calc ‖f z‖ ≤ C * Real.exp (C * r * Real.log (r + 2)) := hC z
    _ = Real.exp (Real.log C + C * r * Real.log (r + 2)) := by
      rw [Real.exp_add, Real.exp_log hCpos]
    _ ≤ Real.exp ((|Real.log C| + C * (1 + 1 / ε) + 1) * Y) := by
      gcongr
      have : (|Real.log C| + C * (1 + 1 / ε) + 1) * Y
          = |Real.log C| * Y + C * (1 + 1 / ε) * Y + Y := by ring
      rw [this]
      linarith

end Erdos985.Analytic.HadamardAux
