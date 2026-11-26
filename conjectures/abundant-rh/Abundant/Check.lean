import Abundant.Statement
import Nicolas.Check.Sound
import Erdos985.Analytic.Digamma.EulerMascheroni

/-!
# The finite check for `n ≤ 5040` (Caveney–Nicolas–Sondow, Lemma 2 and the value `G(4)`)

For every `n ≤ 5040` the checker certifies, in exact rational arithmetic:
* if `n` is composite and `n ≠ 4`: either `G(n) < e^γ`, or `G(n) < G(n/p)` for some prime
  `p ∣ n` (the witness is searched among the prime factors of `n`);
* if `4 ∣ n` and `n > 4`: `G(n) < G(4)`.

`log log n` is bracketed by `llLo n ≤ log log n ≤ llUp n`. The upper bound is nicolas-rh's
`logUp` applied twice (`Nicolas.Check.log_le_logUp`). The lower bound is robin-rh's bisection
`logLo` applied twice, and the checker verifies `expUpper L ≤ y` for each value, so its
correctness is not assumed (`Robin.Lagarias.le_log_of_expUpper_le`). `e^γ` is bounded below by
`expLower 0.57688 ≤ e^{0.57688} < e^γ` (erdos-985's `γ > 0.57688`). One `native_decide`
(`check_ok`); soundness is `finite_check` and `four_check`.
-/

namespace Abundant.Check

open Real ArithmeticFunction Robin.Lagarias
open scoped ArithmeticFunction.sigma

/-- `σ(n)`, computably. -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sig_eq (n : ℕ) : sig n = σ 1 n := (sigma_one_apply n).symm

/-- Candidate lower bound for `log log n`. -/
def llLo (n : ℕ) : ℚ := logLo (logLo (n : ℚ))

/-- The checks that make `llLo n` a lower bound. -/
def llLoOK (n : ℕ) : Bool :=
  decide (0 ≤ logLo (n : ℚ)) && decide (expUpper (logLo (n : ℚ)) ≤ (n : ℚ)) &&
    decide (0 < llLo n) && decide (expUpper (llLo n) ≤ logLo (n : ℚ))

/-- Upper bound for `log log n`. -/
def llUp (n : ℕ) : ℚ := Nicolas.Check.logUp (Nicolas.Check.logUp (n : ℚ))

def llUpOK (n : ℕ) : Bool := decide (1 ≤ Nicolas.Check.logUp (n : ℚ))

/-- Lower bound for `e^γ`. -/
def EL : ℚ := expLower (57688 / 100000)

/-- `G(n) < e^γ`. -/
def condA (n : ℕ) : Bool :=
  llLoOK n && decide ((sig n : ℚ) < EL * n * llLo n)

/-- `G(n) < G(n/p)`. -/
def condB (n p : ℕ) : Bool :=
  decide (3 ≤ n / p) && llLoOK n && llUpOK (n / p) &&
    decide ((sig n : ℚ) * ((n / p : ℕ) : ℚ) * llUp (n / p) < (sig (n / p) : ℚ) * n * llLo n)

/-- The condition at `n` for composite `n ≠ 4`. -/
def okN (n : ℕ) : Bool :=
  decide (n < 4) || decide (n = 4) || Nicolas.Check.isPrime n || condA n ||
    n.primeFactorsList.any (fun p ↦ condB n p)

/-- `G(n) < G(4)` for multiples `n > 4` of `4`. -/
def okFour (n : ℕ) : Bool :=
  !decide (4 ∣ n) || decide (n ≤ 4) ||
    (llLoOK n && llUpOK 4 && decide ((sig n : ℚ) * 4 * llUp 4 < 7 * n * llLo n))

/-- The whole check, `n ≤ 5040`. -/
def check : Bool := (List.range 5041).all fun n ↦ okN n && okFour n

theorem check_ok : check = true := by native_decide

/-! ### Soundness -/

lemma llLo_spec {n : ℕ} (h : llLoOK n = true) :
    0 < (llLo n : ℝ) ∧ (llLo n : ℝ) ≤ Real.log (Real.log n) := by
  simp only [llLoOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hL1 : ((logLo (n : ℚ) : ℚ) : ℝ) ≤ Real.log n := by
    have := le_log_of_expUpper_le (y := (n : ℝ)) h1 (by exact_mod_cast h2)
    exact this
  have hpos : (0 : ℝ) < logLo (n : ℚ) := by
    have he := exp_le_expUpper (le_of_lt h3)
    have : ((expUpper (llLo n) : ℚ) : ℝ) ≤ ((logLo (n : ℚ) : ℚ) : ℝ) := by exact_mod_cast h4
    linarith [Real.exp_pos ((llLo n : ℚ) : ℝ)]
  have hL2 : ((llLo n : ℚ) : ℝ) ≤ Real.log ((logLo (n : ℚ) : ℚ) : ℝ) :=
    le_log_of_expUpper_le (le_of_lt h3) (by exact_mod_cast h4)
  refine ⟨by exact_mod_cast h3, hL2.trans (Real.log_le_log hpos hL1)⟩

lemma llUp_spec {n : ℕ} (hn : 2 ≤ n) (h : llUpOK n = true) :
    Real.log (Real.log n) ≤ (llUp n : ℝ) := by
  simp only [llUpOK, decide_eq_true_eq] at h
  have h1 : Real.log n ≤ (Nicolas.Check.logUp (n : ℚ) : ℝ) := by
    have := Nicolas.Check.log_le_logUp (q := (n : ℚ)) (by exact_mod_cast (show 1 ≤ n by omega))
    simpa using this
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  calc Real.log (Real.log n) ≤ Real.log (Nicolas.Check.logUp (n : ℚ) : ℝ) :=
        Real.log_le_log hlog h1
    _ ≤ (llUp n : ℝ) := Nicolas.Check.log_le_logUp h

lemma loglog_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Real.log (Real.log n) := by
  apply Real.log_pos
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.exp_one_lt_d9
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) (by linarith)

lemma EL_le : (EL : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  have h1 := expLower_le_exp (x := (57688 / 100000 : ℚ)) (by norm_num)
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have h2 : Real.exp (((57688 / 100000 : ℚ)) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
    apply Real.exp_le_exp.mpr; push_cast; linarith
  exact h1.trans h2

lemma condA_sound {n : ℕ} (hn : 3 ≤ n) (h : condA n = true) :
    robinRatio n < Real.exp Real.eulerMascheroniConstant := by
  simp only [condA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlo, hq⟩ := h
  obtain ⟨hlo0, hlo1⟩ := llLo_spec hlo
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLL := loglog_pos hn
  have hr : ((sig n : ℚ) : ℝ) < (EL : ℝ) * n * (llLo n : ℝ) := by exact_mod_cast hq
  rw [sig_eq] at hr
  push_cast at hr
  rw [robinRatio, div_lt_iff₀ (mul_pos hn0 hLL)]
  have : (EL : ℝ) * n * (llLo n : ℝ)
      ≤ Real.exp Real.eulerMascheroniConstant * (n * Real.log (Real.log n)) := by
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_right EL_le hn0.le) hlo1 hlo0.le (by positivity)
  linarith

lemma condB_sound {n p : ℕ} (hn : 3 ≤ n) (h : condB n p = true) :
    robinRatio n < robinRatio (n / p) := by
  simp only [condB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq3, hlo⟩, hup⟩, hq⟩ := h
  obtain ⟨hlo0, hlo1⟩ := llLo_spec hlo
  have hup1 := llUp_spec (by omega) hup
  set q := n / p
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hLLn := loglog_pos hn
  have hLLq := loglog_pos hq3
  have hr : ((sig n : ℚ) : ℝ) * (q : ℝ) * (llUp q : ℝ)
      < ((sig q : ℚ) : ℝ) * (n : ℝ) * (llLo n : ℝ) := by exact_mod_cast hq
  rw [sig_eq, sig_eq] at hr
  push_cast at hr
  rw [robinRatio, robinRatio, div_lt_div_iff₀ (mul_pos hn0 hLLn) (mul_pos hq0 hLLq)]
  have hs : (0 : ℝ) ≤ σ 1 n := by positivity
  have hs' : (0 : ℝ) ≤ σ 1 q := by positivity
  have e1 : (σ 1 n : ℝ) * (q * Real.log (Real.log q)) ≤ (σ 1 n : ℝ) * q * (llUp q : ℝ) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hup1 (by positivity)
  have e2 : (σ 1 q : ℝ) * n * (llLo n : ℝ) ≤ (σ 1 q : ℝ) * (n * Real.log (Real.log n)) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hlo1 (by positivity)
  linarith

lemma sigma_four : σ 1 4 = 7 := by
  rw [← sig_eq]; decide

lemma four_sound {n : ℕ} (hn : 3 ≤ n) (hup : llUpOK 4 = true) (hlo : llLoOK n = true)
    (hq : (sig n : ℚ) * 4 * llUp 4 < 7 * n * llLo n) : robinRatio n < robinRatio 4 := by
  obtain ⟨hlo0, hlo1⟩ := llLo_spec hlo
  have hup1 := llUp_spec (by norm_num) hup
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLLn := loglog_pos hn
  have hLL4 := loglog_pos (show 3 ≤ 4 by norm_num)
  have hr : ((sig n : ℚ) : ℝ) * 4 * (llUp 4 : ℝ) < 7 * (n : ℝ) * (llLo n : ℝ) := by
    exact_mod_cast hq
  rw [sig_eq] at hr
  push_cast at hr
  rw [robinRatio, robinRatio, sigma_four, div_lt_div_iff₀ (mul_pos hn0 hLLn) (by positivity)]
  push_cast
  have e1 : (σ 1 n : ℝ) * (4 * Real.log (Real.log 4)) ≤ (σ 1 n : ℝ) * 4 * (llUp 4 : ℝ) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hup1 (by positivity)
  have e2 : 7 * (n : ℝ) * (llLo n : ℝ) ≤ 7 * (n * Real.log (Real.log n)) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hlo1 (by positivity)
  linarith

lemma check_at {n : ℕ} (hn : n ≤ 5040) : okN n = true ∧ okFour n = true := by
  have h := check_ok
  simp only [check, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact h n (by omega)

/-- **The finite check, part 1** (CNS Lemma 2, extended to all composites `≤ 5040`): every
composite `4 < n ≤ 5040` has `G(n) < e^γ` or `G(n) < G(n/p)` for a prime `p ∣ n`. -/
theorem finite_check {n : ℕ} (h4 : 4 < n) (hn : n ≤ 5040) (hnp : ¬ n.Prime) :
    robinRatio n < Real.exp Real.eulerMascheroniConstant ∨
      ∃ p, p.Prime ∧ p ∣ n ∧ robinRatio n < robinRatio (n / p) := by
  have h := (check_at hn).1
  simp only [okN, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with (((h | h) | h) | h) | ⟨p, hp, hb⟩
  · omega
  · omega
  · exact absurd ((Nicolas.Check.isPrime_iff n).mp h) hnp
  · exact Or.inl (condA_sound (by omega) h)
  · exact Or.inr ⟨p, Nat.prime_of_mem_primeFactorsList hp, Nat.dvd_of_mem_primeFactorsList hp,
      condB_sound (by omega) hb⟩

/-- **The finite check, part 2**: `G(n) < G(4)` for every multiple `4 < n ≤ 5040` of `4`. -/
theorem four_check {n : ℕ} (h4 : 4 < n) (hn : n ≤ 5040) (hdvd : 4 ∣ n) :
    robinRatio n < robinRatio 4 := by
  have h := (check_at hn).2
  simp only [okFour, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with (h | h) | ⟨⟨hlo, hup⟩, hq⟩
  · exact absurd hdvd h
  · omega
  · exact four_sound (by omega) hup hlo hq

end Abundant.Check
