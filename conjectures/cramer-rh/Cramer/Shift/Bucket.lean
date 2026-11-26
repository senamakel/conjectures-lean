import Cramer.Shift.MajSum

/-!
# Bounding `majZ` by two numbers

For `S = 2mσ/h`, `T = 2mτ/h`, `σ ≥ 0.15` and `ε = h/m ≤ 1/800`,

`Lc(S,T) + 1/40 ≤ ½ log(m/h) + ¼ log Q + κ`,   `κ = −½ log π + 1/40 + 0.0086 < 0`,

whenever `(σ + 1/3200)² (1 + τ²/(σ − 3/3200)²) ≤ Q`. Each majorant term carries a bucket
`Q = 4^{n−6}` (`bucketOK`, checked in integers), so
`majZ ≤ (4m/h) (SS · ½ log(m/h) + NS · ½ log 2)` with `SS = Σ (C/KC) σ` and
`NS = Σ (C/KC) σ (n − 6)`.
-/

namespace Cramer.Shift

open Real

/-- The bucket check: `4096 (3200 Sg + NN)² ((3200 Sg − 3NN)² + 3200² Tu²) ≤ 4^n (3200 NN)² (3200 Sg − 3NN)²`. -/
def bucketOK (Sg Tu n : ℕ) : Bool :=
  decide (150000 ≤ Sg) &&
  decide (4096 * (3200 * Sg + NN) ^ 2 * ((3200 * Sg - 3 * NN) ^ 2 + 3200 ^ 2 * Tu ^ 2)
    ≤ 4 ^ n * (3200 * NN) ^ 2 * (3200 * Sg - 3 * NN) ^ 2)

/-- The first bucket that works (or `30`). -/
def nb (Sg Tu : ℕ) : ℕ := ((List.range 30).find? (fun n => bucketOK Sg Tu n)).getD 30

/-- `Σ C Sg`. -/
def SSn (maj : List (ℕ × ℕ × ℕ)) : ℕ := (maj.map (fun c => c.1 * c.2.1)).sum
/-- `Σ C Sg (n − 6)`. -/
def NSn (maj : List (ℕ × ℕ × ℕ)) : ℤ :=
  (maj.map (fun c => (c.1 * c.2.1 : ℤ) * ((nb c.2.1 c.2.2 : ℤ) - 6))).sum

lemma bucket_real {Sg Tu n : ℕ} (h : bucketOK Sg Tu n = true) :
    (0.15 : ℝ) ≤ (Sg : ℝ) / NN ∧
    ((Sg : ℝ) / NN + 1 / 3200) ^ 2 * (1 + ((Tu : ℝ) / NN) ^ 2 / ((Sg : ℝ) / NN - 3 / 3200) ^ 2)
      ≤ (4 : ℝ) ^ (n : ℕ) / 4096 := by
  unfold bucketOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have hN := hNN
  have hS : (150000 : ℝ) ≤ Sg := by exact_mod_cast h0
  have hsub : ((3200 * Sg - 3 * NN : ℕ) : ℝ) = 3200 * Sg - 3 * NN := by
    rw [Nat.cast_sub (by norm_num [NN] at h0 ⊢; omega)]; push_cast; ring
  have h1' : (4096 : ℝ) * (3200 * Sg + NN) ^ 2 * ((3200 * Sg - 3 * NN) ^ 2 + 3200 ^ 2 * Tu ^ 2)
      ≤ 4 ^ n * (3200 * NN) ^ 2 * (3200 * Sg - 3 * NN) ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast at this
    rw [hsub] at this
    linarith
  have hNv : (NN : ℝ) = 1000000 := by norm_num [NN]
  refine ⟨by rw [le_div_iff₀ hN, hNv]; linarith, ?_⟩
  have hd : (0 : ℝ) < 3200 * Sg - 3 * NN := by rw [hNv]; linarith
  have hd' : (0 : ℝ) < (Sg : ℝ) / NN - 3 / 3200 := by
    have : (Sg : ℝ) / NN - 3 / 3200 = (3200 * Sg - 3 * NN) / (3200 * NN) := by field_simp
    rw [this]; positivity
  have e : ((Sg : ℝ) / NN + 1 / 3200) ^ 2 * (1 + ((Tu : ℝ) / NN) ^ 2 / ((Sg : ℝ) / NN - 3 / 3200) ^ 2)
      = (3200 * Sg + NN) ^ 2 * ((3200 * Sg - 3 * NN) ^ 2 + 3200 ^ 2 * Tu ^ 2)
        / ((3200 * NN) ^ 2 * (3200 * Sg - 3 * NN) ^ 2) := by
    have : (Sg : ℝ) / NN - 3 / 3200 = (3200 * Sg - 3 * NN) / (3200 * NN) := by field_simp
    rw [this]
    have hd2 : (3200 * (Sg : ℝ) - 3 * NN) ≠ 0 := hd.ne'
    generalize (3200 * (Sg : ℝ) - 3 * NN) = d at hd2 ⊢
    have : (NN : ℝ) ≠ 0 := hN.ne'
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- **One term.** -/
lemma Lc_term_le {σ τ m h Q : ℝ} (hσ : 0.15 ≤ σ) (hm : 0 < m) (hh : 0 < h) (hε : h / m ≤ 1 / 800)
    (hQ : (σ + 1 / 3200) ^ 2 * (1 + τ ^ 2 / (σ - 3 / 3200) ^ 2) ≤ Q) :
    Lc (2 * m * σ / h) (2 * m * τ / h) + 1 / 40
      ≤ 1 / 2 * Real.log (m / h) + 1 / 4 * Real.log Q - 1 / 2 := by
  set ε := h / m with hεdef
  have hε0 : 0 < ε := div_pos hh hm
  set S := 2 * m * σ / h with hSdef
  have hSe : S = 2 * σ / ε := by rw [hSdef, hεdef]; field_simp
  have hmh : m / h = 1 / ε := by rw [hεdef]; field_simp
  have hS : 1600 * σ ≤ S := by
    rw [hSe, le_div_iff₀ hε0]; nlinarith
  have hS240 : 240 ≤ S := by linarith
  -- the small terms
  have hr1 : 1 / (1 / 2 + S) + 1 / (S - 1 / 2) ≤ 0.0084 := by
    have a1 : 1 / (1 / 2 + S) ≤ 1 / 240 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have a2 : 1 / (S - 1 / 2) ≤ 1 / 239 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hr2 : 1.52 * (2 : ℝ) ^ (1 - S) ≤ 0.0001 := by
    have : (2 : ℝ) ^ (1 - S) ≤ (2 : ℝ) ^ (-(20 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg (by norm_num)] at this
    norm_num at this
    linarith
  -- the logarithms
  have hlog1 : Real.log ((1 / 2 + S) / 2) ≤ Real.log (1 / ε) + Real.log (σ + 1 / 3200) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hSe]
    have : (1 / 2 + 2 * σ / ε) / 2 = (σ + ε / 4) / ε := by field_simp; ring
    rw [this, div_mul_eq_mul_div, one_mul]
    apply div_le_div_of_nonneg_right _ hε0.le
    linarith
  have hT : (2 * m * τ / h) ^ 2 / (S - 3 / 2) ^ 2 ≤ τ ^ 2 / (σ - 3 / 3200) ^ 2 := by
    have hden : (σ - 3 / 3200) ^ 2 * (2 / ε) ^ 2 ≤ (S - 3 / 2) ^ 2 := by
      have h1 : 0 ≤ σ - 3 / 3200 := by linarith
      have h2 : (σ - 3 / 3200) * (2 / ε) ≤ S - 3 / 2 := by
        rw [hSe]
        have : 3 / 2 ≤ 3 / 3200 * (2 / ε) := by
          rw [show 3 / 3200 * (2 / ε) = 3 / (1600 * ε) by field_simp; ring, le_div_iff₀ (by positivity)]
          nlinarith
        have e : (σ - 3 / 3200) * (2 / ε) = 2 * σ / ε - 3 / 3200 * (2 / ε) := by ring
        linarith
      have h3 : 0 ≤ (σ - 3 / 3200) * (2 / ε) := by positivity
      rw [← mul_pow]; exact pow_le_pow_left₀ h3 h2 2
    have eT : 2 * m * τ / h = τ * (2 / ε) := by rw [hεdef]; field_simp
    rw [eT, mul_pow, div_le_div_iff₀ (by
      have : 0 < (σ - 3 / 3200) ^ 2 * (2 / ε) ^ 2 := by
        have : 0 < σ - 3 / 3200 := by linarith
        positivity
      linarith) (by have : 0 < σ - 3 / 3200 := by linarith
                    positivity)]
    have := mul_le_mul_of_nonneg_left hden (sq_nonneg τ)
    nlinarith [sq_nonneg τ, sq_nonneg (2 / ε)]
  have hlog2 : Real.log (1 + (2 * m * τ / h) ^ 2 / (S - 3 / 2) ^ 2)
      ≤ Real.log (1 + τ ^ 2 / (σ - 3 / 3200) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hQ0 : 0 < (σ + 1 / 3200) ^ 2 * (1 + τ ^ 2 / (σ - 3 / 3200) ^ 2) := by positivity
  have hlogQ : 2 * Real.log (σ + 1 / 3200) + Real.log (1 + τ ^ 2 / (σ - 3 / 3200) ^ 2) ≤ Real.log Q := by
    have h := Real.log_le_log hQ0 hQ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    push_cast at h
    linarith
  have hpi : 1.144 ≤ Real.log Real.pi := le_of_lt Erdos985.Analytic.PrincipalAux.log_pi_gt'
  unfold Lc
  rw [← hmh] at hlog1
  linarith

/-- **`majZ` in two numbers.** -/
theorem majZ_le (maj : List (ℕ × ℕ × ℕ))
    (hb : ∀ c ∈ maj, bucketOK c.2.1 c.2.2 (nb c.2.1 c.2.2) = true)
    {m h : ℝ} (hm : 0 < m) (hh : 0 < h) (hε : h / m ≤ 1 / 800) :
    majZ maj m h ≤ 4 * m / h * ((SSn maj : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h))
      + (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2)) := by
  have hN := hNN
  have hKC : (0 : ℝ) < KC := by norm_num [KC]
  have hL : 0 ≤ Real.log (m / h) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hh]; rw [div_le_iff₀ hm] at hε; linarith
  induction maj with
  | nil => simp [majZ, SSn, NSn]
  | cons c cs ih =>
    have ih' := ih (fun d hd => hb d (List.mem_cons_of_mem _ hd))
    obtain ⟨C, Sg, Tu⟩ := c
    have hc := hb _ (List.mem_cons_self ..)
    simp only at hc
    obtain ⟨hσ, hQ⟩ := bucket_real hc
    have hterm := Lc_term_le (τ := (Tu : ℝ) / NN) hσ hm hh hε hQ
    have hlogQ : Real.log ((4 : ℝ) ^ (nb Sg Tu : ℕ) / 4096)
        = ((nb Sg Tu : ℝ) - 6) * Real.log 2 * 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow,
        Real.log_pow]
      push_cast; ring
    rw [hlogQ] at hterm
    simp only [majZ, SSn, NSn, List.map_cons, List.sum_cons] at ih' ⊢
    rw [Nat.cast_add, Int.cast_add]
    set σ : ℝ := (Sg : ℝ) / NN
    have hσ0 : 0 ≤ σ := by linarith
    have hC : (0 : ℝ) ≤ (C : ℝ) / KC := by positivity
    have h2S : 0 ≤ 2 * (2 * m * σ / h) := by positivity
    have key : (C : ℝ) / KC * (2 * (2 * m * σ / h) * (Lc (2 * m * σ / h) (2 * m * ((Tu : ℝ) / NN) / h) + 1 / 40))
        ≤ 4 * m / h * (((C * Sg : ℕ) : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h))
          + (((C * Sg : ℤ) * ((nb Sg Tu : ℤ) - 6) : ℤ) : ℝ) / (KC * NN) * (Real.log 2 / 2)) := by
      have h1 : (C : ℝ) / KC * (2 * (2 * m * σ / h) * (Lc (2 * m * σ / h) (2 * m * ((Tu : ℝ) / NN) / h) + 1 / 40))
          ≤ (C : ℝ) / KC * (2 * (2 * m * σ / h) * (1 / 2 * Real.log (m / h)
              + 1 / 4 * (((nb Sg Tu : ℝ) - 6) * Real.log 2 * 2))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply mul_le_mul_of_nonneg_left _ h2S
        linarith
      refine h1.trans (le_of_eq ?_)
      simp only [σ]
      push_cast
      field_simp
      ring
    have e : ∀ A B C' D : ℝ, 4 * m / h * ((A + B) / (KC * NN) * (1 / 2 * Real.log (m / h))
        + (C' + D) / (KC * NN) * (Real.log 2 / 2))
        = 4 * m / h * (A / (KC * NN) * (1 / 2 * Real.log (m / h)) + C' / (KC * NN) * (Real.log 2 / 2))
          + 4 * m / h * (B / (KC * NN) * (1 / 2 * Real.log (m / h)) + D / (KC * NN) * (Real.log 2 / 2)) := by
      intro A B C' D; ring
    rw [e]
    exact add_le_add key ih'

end Cramer.Shift
