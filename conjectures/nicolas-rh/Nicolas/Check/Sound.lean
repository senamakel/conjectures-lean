import Nicolas.Check.Defs
import Nicolas.Primorial
import Nicolas.Mertens
import Erdos985.Analytic.Principal.Bounds.Numerics

/-!
# Soundness of the finite check

`Inv m st`: `R ≤ exp(Σ_{p≤m} c_p)`, `θ(m) ≤ T`, and if the flag is set then
`e^γ log θ(p) < exp(Σ_{p'≤p} c_{p'})` for every prime `3 ≤ p ≤ m`. `step` preserves it
(`inv_step`), so `run m` satisfies `Inv m` (`inv_run`).
-/

namespace Nicolas.Check

open Real Chebyshev Robin Finset

lemma rdDown_le (q : ℚ) : rdDown q ≤ q := by
  unfold rdDown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

lemma le_rdUp (q : ℚ) : q ≤ rdUp q := by
  unfold rdUp
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

lemma log_le_logUpR {r : ℚ} (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    Real.log r ≤ (logUpR r : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hr2 : (r : ℝ) ≤ 2 := by exact_mod_cast h2
  set y : ℝ := 1 - 1 / (r : ℝ) with hy
  have hy0 : 0 ≤ y := by
    rw [hy, sub_nonneg, div_le_one (by linarith)]; exact hr1
  have hy1 : y ≤ 1 / 2 := by
    rw [hy]
    have : 1 / 2 ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le (by linarith) hr2
    linarith
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs nTerms
  rw [abs_of_nonneg hy0] at h
  have hlog : Real.log (1 - y) = -Real.log r := by
    rw [hy, sub_sub_cancel, one_div, Real.log_inv]
  rw [hlog] at h
  have hcast : (logUpR r : ℝ) = (∑ i ∈ range nTerms, y ^ (i + 1) / (i + 1))
      + y ^ (nTerms + 1) / (1 - y) := by
    simp only [logUpR, logSeries, hy]
    push_cast
    rfl
  rw [hcast]
  linarith [(abs_le.mp h).1]

lemma log_le_logUp {q : ℚ} (hq : 1 ≤ q) : Real.log q ≤ (logUp q : ℝ) := by
  set n := ⌊q⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hq)
  set e := Nat.log 2 n with he
  have hpe : 2 ^ e ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hpe' : n < 2 ^ (e + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hqn : (n : ℚ) ≤ q := Nat.floor_le (by linarith)
  have hqn' : q < n + 1 := Nat.lt_floor_add_one q
  have h2e : (0 : ℚ) < 2 ^ e := by positivity
  have hr1 : 1 ≤ q / 2 ^ e := by
    rw [le_div_iff₀ h2e, one_mul]
    exact le_trans (by exact_mod_cast hpe) hqn
  have hr2 : q / 2 ^ e ≤ 2 := by
    rw [div_le_iff₀ h2e]
    have : ((n + 1 : ℕ) : ℚ) ≤ 2 ^ (e + 1) := by exact_mod_cast hpe'
    push_cast at this
    rw [pow_succ] at this
    linarith
  have hlr := log_le_logUpR hr1 hr2
  have hq0' : (0 : ℚ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq0'
  have hsplit : Real.log q = e * Real.log 2 + Real.log ((q / 2 ^ e : ℚ) : ℝ) := by
    push_cast
    rw [Real.log_div hq0.ne' (by positivity), Real.log_pow]
    ring
  have hl2 : Real.log 2 ≤ (l2U : ℝ) := by
    have := Real.log_two_lt_d9; simp only [l2U]; push_cast; linarith
  have hdef : logUp q = rdUp ((e : ℚ) * l2U + logUpR (q / (2 : ℚ) ^ e)) := rfl
  have hup := le_rdUp ((e : ℚ) * l2U + logUpR (q / (2 : ℚ) ^ e))
  rw [← hdef] at hup
  have hup' : (((e : ℚ) * l2U + logUpR (q / (2 : ℚ) ^ e) : ℚ) : ℝ) ≤ (logUp q : ℝ) := by
    exact_mod_cast hup
  push_cast at hup'
  rw [hsplit]
  have : (e : ℝ) * Real.log 2 ≤ e * l2U := mul_le_mul_of_nonneg_left hl2 (by positivity)
  linarith

lemma exp_gamma_le_EU : Real.exp Real.eulerMascheroniConstant ≤ (EU : ℝ) := by
  have hγ := Erdos985.Analytic.PrincipalAux.eulerMascheroniConstant_lt'
  have h1 : Real.exp Real.eulerMascheroniConstant ≤ Real.exp ((5774 / 10000 : ℚ) : ℝ) := by
    apply Real.exp_le_exp.mpr; push_cast; linarith
  exact h1.trans (Robin.Lagarias.exp_le_expUpper (by norm_num))

lemma isPrime_iff (n : ℕ) : isPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_minFac]
  simp [isPrime]

lemma primeSum_succ (f : ℕ → ℝ) (m : ℕ) :
    primeSum f ((m + 1 : ℕ) : ℝ) = primeSum f (m : ℝ) + if (m + 1).Prime then f (m + 1) else 0 := by
  rw [Nicolas.primeSum_eq_primesLE, Nicolas.primeSum_eq_primesLE, Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert (Nat.notMem_primesLE m), add_comm]
  · simp

lemma theta_succ (m : ℕ) :
    θ ((m + 1 : ℕ) : ℝ) = θ (m : ℝ) + if (m + 1).Prime then Real.log (m + 1 : ℕ) else 0 := by
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log, Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert (Nat.notMem_primesLE m), add_comm]
  · simp

/-- The invariant of the check after processing `1, …, m`. -/
def Inv (m : ℕ) (st : St) : Prop :=
  (st.R : ℝ) ≤ Real.exp (primeSum cp (m : ℝ)) ∧ θ (m : ℝ) ≤ (st.T : ℝ) ∧
    (st.ok = true → ∀ p : ℕ, p ≤ m → p.Prime → 3 ≤ p →
      Real.exp Real.eulerMascheroniConstant * Real.log (θ (p : ℝ))
        < Real.exp (primeSum cp (p : ℝ)))

lemma inv_init : Inv 0 init := by
  have h0 : primeSum cp ((0 : ℕ) : ℝ) = 0 := by
    rw [Nicolas.primeSum_eq_primesLE, Nat.primesLE_zero]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]; simp [init]
  · simp [init, theta_zero]
  · intro _ p hp hpr
    have : p = 0 := by omega
    subst this
    exact absurd hpr Nat.not_prime_zero

lemma inv_step {m : ℕ} {st : St} (h : Inv m st) : Inv (m + 1) (step st (m + 1)) := by
  obtain ⟨hR, hT, hok⟩ := h
  unfold step
  by_cases hp : (m + 1).Prime
  · have hpb : isPrime (m + 1) = true := (isPrime_iff _).mpr hp
    simp only [hpb, ↓reduceIte]
    have hn2 : 2 ≤ m + 1 := hp.two_le
    have hn2' : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn2
    have hps := primeSum_succ cp m
    have hth := theta_succ m
    simp only [hp, ↓reduceIte] at hps hth
    -- the product
    have hR' : (rdDown (st.R * ((m + 1 : ℕ) : ℚ) / (((m + 1 : ℕ) : ℚ) - 1)) : ℝ)
        ≤ Real.exp (primeSum cp ((m + 1 : ℕ) : ℝ)) := by
      have h1 := rdDown_le (st.R * ((m + 1 : ℕ) : ℚ) / (((m + 1 : ℕ) : ℚ) - 1))
      have h1' : (rdDown (st.R * ((m + 1 : ℕ) : ℚ) / (((m + 1 : ℕ) : ℚ) - 1)) : ℝ)
          ≤ (st.R : ℝ) * ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) - 1) := by
        have := (Rat.cast_le (K := ℝ)).mpr h1
        push_cast at this ⊢
        exact this
      have hpos : 0 < ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) - 1) := by
        apply div_pos <;> linarith
      rw [hps, Real.exp_add, cp_eq_log hn2, Real.exp_log hpos]
      calc _ ≤ (st.R : ℝ) * ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) - 1) := h1'
        _ = (st.R : ℝ) * (((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) - 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hR hpos.le
    -- θ
    have hT' : θ ((m + 1 : ℕ) : ℝ) ≤ ((st.T + logUp ((m + 1 : ℕ) : ℚ) : ℚ) : ℝ) := by
      have hl := log_le_logUp (q := ((m + 1 : ℕ) : ℚ)) (by exact_mod_cast (by omega : 1 ≤ m + 1))
      rw [hth]
      push_cast at hl ⊢
      linarith
    refine ⟨hR', hT', ?_⟩
    intro hok' q hq hqp hq3
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨hok0, hcase⟩ := hok'
    rcases Nat.lt_or_ge q (m + 1) with hlt | hge
    · exact hok hok0 q (by omega) hqp hq3
    have hqe : q = m + 1 := by omega
    subst hqe
    rcases hcase with h3 | hc
    · omega
    set T' := st.T + logUp ((m + 1 : ℕ) : ℚ)
    have hθ1 := Nicolas.one_lt_theta (x := ((m + 1 : ℕ) : ℝ)) (by exact_mod_cast hq3)
    have hT1 : (1 : ℚ) ≤ T' := by
      have : (1 : ℝ) ≤ (T' : ℝ) := by linarith
      exact_mod_cast this
    have hlogT := log_le_logUp hT1
    have hlθ : Real.log (θ ((m + 1 : ℕ) : ℝ)) ≤ Real.log (T' : ℝ) :=
      Real.log_le_log (by linarith) hT'
    have hlθ0 : 0 ≤ Real.log (θ ((m + 1 : ℕ) : ℝ)) := (Real.log_pos hθ1).le
    have hc' : ((EU * logUp T' : ℚ) : ℝ) < (rdDown (st.R * ((m + 1 : ℕ) : ℚ)
        / (((m + 1 : ℕ) : ℚ) - 1)) : ℝ) := by exact_mod_cast hc
    push_cast at hc'
    have hEU := exp_gamma_le_EU
    calc Real.exp Real.eulerMascheroniConstant * Real.log (θ ((m + 1 : ℕ) : ℝ))
        ≤ (EU : ℝ) * (logUp T' : ℝ) :=
          mul_le_mul hEU (hlθ.trans hlogT) hlθ0 ((Real.exp_pos _).le.trans hEU)
      _ < _ := by
        push_cast at hR' ⊢
        exact lt_of_lt_of_le hc' hR'
  · have hpb : isPrime (m + 1) = false := by
      rw [Bool.eq_false_iff]; intro h'; exact hp ((isPrime_iff _).mp h')
    simp only [hpb, Bool.false_eq_true, ↓reduceIte]
    have hps := primeSum_succ cp m
    have hth := theta_succ m
    simp only [hp, ↓reduceIte, add_zero] at hps hth
    refine ⟨by rw [hps]; exact hR, by rw [hth]; exact hT, ?_⟩
    intro hok' q hq hqp hq3
    have : q ≠ m + 1 := fun h' => hp (h' ▸ hqp)
    exact hok hok' q (by omega) hqp hq3

lemma inv_run (m : ℕ) : Inv m (run m) := by
  induction m with
  | zero => exact inv_init
  | succ m ih => exact inv_step ih

/-- **The finite computation**: the flag is still set after processing `1, …, 10^5`, i.e.
`EU · logUp T < R` at every prime `3 ≤ p ≤ 10^5` (9591 primes; `R` rounded-down
`∏ p/(p−1)`, `T` rounded-up `θ(p)`, 40-term log series). Uses `native_decide`. -/
theorem loop_ok : (loop bound 1 init).ok = true := by
  native_decide

/-- **Finite range.** `e^γ log θ(p) < exp(Σ_{p'≤p} c_{p'})` for every prime `3 ≤ p ≤ 10^5`. -/
theorem finite_range {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpB : p ≤ 100000) :
    Real.exp Real.eulerMascheroniConstant * Real.log (θ (p : ℝ))
      < Real.exp (primeSum cp (p : ℝ)) := by
  have h := loop_run bound 0
  simp only [zero_add] at h
  have hok : (run bound).ok = true := by
    rw [← h]; exact loop_ok
  exact (inv_run bound).2.2 hok p hpB hp hp3

end Nicolas.Check
