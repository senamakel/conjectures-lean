import Cramer.Shift.Check

/-!
# The tail `x ≥ X_T` and the assembled pointwise statement

For `x ≥ x_T`, each centred term satisfies `σ²/(σ² + x²) ≥ (σ² x_T²/(σ² + x_T²))/x²`, so the
centred terms alone give `M(x) ≥ (Σ 2C σ² x_T²/(σ² + x_T²))/(KC x²)`. `tailOK` checks that this
beats `envT(x) = 802/(800x²)`. With a chain of checked cells on `[0, x_T]` every `y ≥ 0` is
`CellGood`.
-/

namespace Cramer.Shift

open Real

/-- `⌊KK Sg² XT² / (XT² + Sg²)⌋`. -/
def tailF (Sg XT : ℕ) : ℕ := KK * Sg ^ 2 * XT ^ 2 / (XT ^ 2 + Sg ^ 2)

/-- The rounded tail mass of the centred terms. -/
def tailSum (maj : List (ℕ × ℕ × ℕ)) (XT : ℕ) : ℕ :=
  (maj.map (fun c => if c.2.2 = 0 then 2 * c.1 * tailF c.2.1 XT else 0)).sum

/-- The tail check. -/
def tailOK (maj : List (ℕ × ℕ × ℕ)) (XT : ℕ) : Bool :=
  decide (0 < XT) && decide (802 * NN ^ 2 * KK * KC ≤ 800 * tailSum maj XT)

lemma tailSum_le (maj : List (ℕ × ℕ × ℕ)) {XT : ℕ} {x : ℝ} (hXT : 0 < XT)
    (hx : (XT : ℝ) / NN ≤ x) :
    (tailSum maj XT : ℝ) / (KK * KC * NN ^ 2 * x ^ 2) ≤ majF maj x := by
  have hN := hNN
  have hK : (0 : ℝ) < KK := by norm_num [KK]
  have hKC : (0 : ℝ) < KC := by norm_num [KC]
  have hxT : (0 : ℝ) < (XT : ℝ) / NN := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le hxT hx
  induction maj with
  | nil => simp [tailSum, majF]
  | cons c cs ih =>
    simp only [tailSum, majF, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add, add_div]
    refine add_le_add ?_ ih
    obtain ⟨C, Sg, Tu⟩ := c
    simp only
    have hl0 := lor_nonneg ((Sg : ℝ) / NN) (x - (Tu : ℝ) / NN)
    have hl1 := lor_nonneg ((Sg : ℝ) / NN) (x + (Tu : ℝ) / NN)
    split_ifs with hT
    · subst hT
      simp only [CharP.cast_eq_zero, zero_div, sub_zero, add_zero]
      -- `lor σ x ≥ tailF/(KK N² x²)`
      have key : (tailF Sg XT : ℝ) / (KK * NN ^ 2 * x ^ 2) ≤ lor ((Sg : ℝ) / NN) x := by
        have h1 := Nat.div_mul_le_self (KK * Sg ^ 2 * XT ^ 2) (XT ^ 2 + Sg ^ 2)
        have h1' : (tailF Sg XT : ℝ) * ((XT : ℝ) ^ 2 + (Sg : ℝ) ^ 2) ≤ KK * (Sg : ℝ) ^ 2 * (XT : ℝ) ^ 2 := by
          exact_mod_cast h1
        rcases Nat.eq_zero_or_pos Sg with rfl | hS
        · simp [tailF, lor_nonneg]
        have hSr : (0 : ℝ) < Sg := by exact_mod_cast hS
        set f : ℝ := ((tailF Sg XT : ℕ) : ℝ)
        have hf0 : 0 ≤ f := Nat.cast_nonneg _
        set σ : ℝ := (Sg : ℝ) / NN
        set v : ℝ := ((XT : ℝ) / NN) ^ 2
        set u : ℝ := x ^ 2
        have hσ : 0 < σ := by positivity
        have hv : 0 < v := by positivity
        have hvu : v ≤ u := pow_le_pow_left₀ hxT.le hx 2
        set kk : ℝ := KK * NN ^ 2 * σ ^ 2
        have hkk : 0 < kk := by positivity
        have hfv : f * (v + σ ^ 2) ≤ kk * v := by
          have e1 : (XT : ℝ) ^ 2 + (Sg : ℝ) ^ 2 = NN ^ 2 * (v + σ ^ 2) := by
            simp only [v, σ]; field_simp
          have e2 : (KK : ℝ) * (Sg : ℝ) ^ 2 * (XT : ℝ) ^ 2 = NN ^ 2 * (kk * v) := by
            simp only [kk, v, σ]; field_simp
          rw [e1, e2] at h1'
          have : (0 : ℝ) < NN ^ 2 := by positivity
          nlinarith
        have hfu : f * (u + σ ^ 2) ≤ kk * u := by
          have a1 : f * (u + σ ^ 2) * v ≤ f * (v + σ ^ 2) * u := by
            have : f * σ ^ 2 * v ≤ f * σ ^ 2 * u := by
              apply mul_le_mul_of_nonneg_left hvu; positivity
            nlinarith
          have a2 : f * (v + σ ^ 2) * u ≤ kk * v * u :=
            mul_le_mul_of_nonneg_right hfv (by positivity)
          have : f * (u + σ ^ 2) * v ≤ kk * u * v := by nlinarith
          exact le_of_mul_le_mul_right this hv
        unfold lor
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (KK : ℝ) * NN ^ 2 * x ^ 2 = kk * u / σ ^ 2 := by
          simp only [kk, u]; field_simp
        rw [this]
        have : σ ^ 2 * (kk * u / σ ^ 2) = kk * u := by field_simp
        nlinarith
      have e : ((2 * C * tailF Sg XT : ℕ) : ℝ) / (KK * KC * NN ^ 2 * x ^ 2)
          = (C : ℝ) / KC * (2 * ((tailF Sg XT : ℝ) / (KK * NN ^ 2 * x ^ 2))) := by
        push_cast; field_simp
      rw [e]
      have hC : (0 : ℝ) ≤ (C : ℝ) / KC := by positivity
      have := mul_le_mul_of_nonneg_left (show 2 * ((tailF Sg XT : ℝ) / (KK * NN ^ 2 * x ^ 2))
        ≤ lor ((Sg : ℝ) / NN) x + lor ((Sg : ℝ) / NN) x by linarith) hC
      exact this
    · simp only [Nat.cast_zero, zero_div]
      positivity

/-- **The tail.** -/
lemma tail_good {maj : List (ℕ × ℕ × ℕ)} {XT : ℕ} (h : tailOK maj XT = true) {x : ℝ}
    (hx : (XT : ℝ) / NN ≤ x) : CellGood maj x := by
  unfold tailOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hXT, hchk⟩ := h
  have hN := hNN
  have hK : (0 : ℝ) < KK := by norm_num [KK]
  have hKC : (0 : ℝ) < KC := by norm_num [KC]
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  left
  refine ⟨hx0, le_trans ?_ (tailSum_le maj hXT hx)⟩
  have hchk' : (802 : ℝ) * NN ^ 2 * KK * KC ≤ 800 * tailSum maj XT := by exact_mod_cast hchk
  unfold envT
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x, pow_pos hx0 2]

/-- **Every `y ≥ 0` is good**, from a chain on `[0, XT]` and the tail check. -/
theorem all_good {maj : List (ℕ × ℕ × ℕ)} {cs : List (ℕ × ℕ × ℕ × ℕ)} {XT : ℕ}
    (hchain : chainOK 0 XT cs = true) (hcells : cs.all (cellOK maj) = true)
    (htail : tailOK maj XT = true) : ∀ y : ℝ, 0 ≤ y → CellGood maj y := by
  intro y hy
  rcases le_or_gt y ((XT : ℝ) / NN) with h | h
  · refine chainOK_sound cs 0 XT hchain ?_ y (by simpa using hy) h
    intro c hc
    exact List.all_eq_true.mp hcells c hc
  · exact tail_good htail h.le

end Cramer.Shift
