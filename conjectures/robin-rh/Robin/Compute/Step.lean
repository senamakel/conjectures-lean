import Robin.Compute.Sieve
import Robin.Compute.Envelope

/-!
# The invariant of the computation and its preservation

`Valid x0 s` says: there is a finite set `U ⊆ [2, B)` containing every prime below `B` with
`D Σ_U log(1 + 1/m) ≤ A` and `T ≤ D Σ_U log m`, and Robin's inequality holds for every `n` with
`x0/XS ≤ log n < cov/XS`. `segStep` and `checkpoint` preserve it.
-/

namespace Robin.Compute

open RobinCompute Real Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Robin's inequality at `n`. -/
def RobinAt (n : ℕ) : Prop :=
  (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

def Covered (x0 c : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (x0 : ℝ) / XS ≤ Real.log n → Real.log n < (c : ℝ) / XS → RobinAt n

def Valid (x0 : ℕ) (s : St) : Prop :=
  2 ≤ s.B ∧ ∃ U : Finset ℕ, (∀ m ∈ U, 2 ≤ m ∧ m < s.B) ∧ (∀ p, p.Prime → p < s.B → p ∈ U) ∧
    (D : ℝ) * ∑ m ∈ U, Real.log (1 + 1 / (m : ℝ)) ≤ s.A ∧
    (s.T : ℝ) ≤ D * ∑ m ∈ U, Real.log m ∧ Covered x0 s.cov

theorem valid_init (x0 : ℕ) : Valid x0 ⟨2, 0, 0, x0⟩ := by
  refine ⟨le_rfl, ∅, by simp, ?_, by simp, by simp, ?_⟩
  · intro p hp hp2; simp only at hp2; exact absurd hp.two_le (by omega)
  · intro n _ h1 h2; exact absurd h2 (not_lt.mpr h1)

/-! ### Segment bounds -/

lemma log_one_add_inv_le_mom {B i : ℕ} (hB : 1 ≤ B) :
    Real.log (1 + 1 / ((B + i : ℕ) : ℝ)) ≤
      2 * ((2 * B + 1 : ℝ) ^ 2 - 2 * i * (2 * B + 1) + 4 * i ^ 2) / (2 * B + 1) ^ 3 +
        2 / (3 * (2 * B + 1) * ((2 * B + 1) ^ 2 - 1)) := by
  have hm : 0 < B + i := by omega
  have h := log_le_sum_tail (B + i) 1 1 hm one_pos
  simp only [Finset.range_one, Finset.sum_singleton, sterm, Nat.cast_one] at h
  push_cast at h
  set b : ℝ := 2 * B + 1 with hb
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hb3 : 3 ≤ b := by linarith
  have hi : (0 : ℝ) ≤ i := by positivity
  set z : ℝ := 1 / (2 * ((B : ℝ) + i) + 1) with hz
  have hzb : z = 1 / (b + 2 * i) := by rw [hz, hb]; ring_nf
  clear_value z
  have hz0 : 0 < z := by rw [hzb]; positivity
  have hz1 : z ≤ 1 / b := by rw [hzb]; apply one_div_le_one_div_of_le (by linarith); linarith
  have hzb1 : z < 1 := lt_of_le_of_lt hz1 (by rw [div_lt_one (by linarith)]; linarith)
  have h1 : 2 * (1 / (2 * 0 + 1)) * z ^ (2 * 0 + 1) ≤
      2 * (b ^ 2 - 2 * i * b + 4 * i ^ 2) / b ^ 3 := by
    norm_num
    rw [hzb, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg hi 3, sq_nonneg (i : ℝ)]
  have h2 : 2 * (1 / (2 * 1 + 1)) * z ^ (2 * 1 + 1) / (1 - z ^ 2) ≤
      2 / (3 * b * (b ^ 2 - 1)) := by
    have hzz : 1 - 1 / b ^ 2 ≤ 1 - z ^ 2 := by
      have : z ^ 2 ≤ (1 / b) ^ 2 := pow_le_pow_left₀ hz0.le hz1 2
      rw [div_pow, one_pow] at this; linarith
    have hpos : 0 < 1 - 1 / b ^ 2 := by
      rw [sub_pos, div_lt_one (by positivity)]; nlinarith
    have hz3 : z ^ 3 ≤ (1 / b) ^ 3 := pow_le_pow_left₀ hz0.le hz1 3
    calc 2 * (1 / (2 * 1 + 1)) * z ^ (2 * 1 + 1) / (1 - z ^ 2)
        ≤ 2 * (1 / (2 * 1 + 1)) * (1 / b) ^ 3 / (1 - 1 / b ^ 2) := by
          apply div_le_div₀ (by positivity) _ hpos hzz
          have := hz3; rw [div_pow, one_pow, one_div] at this
          norm_num; linarith
      _ = 2 / (3 * b * (b ^ 2 - 1)) := by
          have : b ^ 2 - 1 ≠ 0 := by nlinarith
          field_simp; ring
  have h' : Real.log (1 + 1 / ((B : ℝ) + i)) ≤ 2 * (1 / (2 * 0 + 1)) * z ^ (2 * 0 + 1) +
      2 * (1 / (2 * 1 + 1)) * z ^ (2 * 1 + 1) / (1 - z ^ 2) := by
    convert h using 3 <;> push_cast <;> ring_nf
  push_cast
  linarith

lemma sum_quad (F : Finset ℕ) (α β γ : ℝ) :
    ∑ i ∈ F, (α + β * (i : ℝ) + γ * ((i : ℝ) * i)) =
      α * F.card + β * (∑ i ∈ F, (i : ℝ)) + γ * (∑ i ∈ F, (i : ℝ) * i) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
    ← Finset.mul_sum, nsmul_eq_mul]
  ring

theorem momA_ge (B : ℕ) (hB : 1 ≤ B) (F : Finset ℕ) :
    (D : ℝ) * ∑ i ∈ F, Real.log (1 + 1 / ((B + i : ℕ) : ℝ)) ≤
      (momA B F.card (∑ i ∈ F, i) (∑ i ∈ F, i * i) : ℝ) := by
  set b := 2 * B + 1 with hb
  have hb3 : 3 ≤ b := by omega
  set bR : ℝ := 2 * B + 1 with hbR
  have hbR3 : 3 ≤ bR := by have : (1 : ℝ) ≤ B := by exact_mod_cast hB
                           linarith
  set K : ℝ := 2 / (3 * bR * (bR ^ 2 - 1))
  have hterm : ∀ i ∈ F, Real.log (1 + 1 / ((B + i : ℕ) : ℝ)) ≤
      (2 / bR + K) + (-4 / bR ^ 2) * (i : ℝ) + (8 / bR ^ 3) * ((i : ℝ) * i) := by
    intro i _
    have h := log_one_add_inv_le_mom (B := B) (i := i) hB
    have e : 2 * (bR ^ 2 - 2 * i * bR + 4 * (i : ℝ) ^ 2) / bR ^ 3 =
        2 / bR + (-4 / bR ^ 2) * (i : ℝ) + (8 / bR ^ 3) * ((i : ℝ) * i) := by
      field_simp; ring
    rw [← hbR, e] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [sum_quad] at hsum
  have hsub : 2 * (∑ i ∈ F, i) * b ≤ F.card * b * b + 4 * ∑ i ∈ F, i * i := by
    have : ∀ i ∈ F, 2 * i * b ≤ b * b + 4 * (i * i) := fun i _ => by nlinarith
    have h := Finset.sum_le_sum this
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul, ← Finset.mul_sum] at h
    linarith
  have hden1 : 0 < b ^ 3 := by positivity
  have hden2 : 0 < 3 * b * (b * b - 1) := by
    have : 1 < b * b := by nlinarith
    have : 0 < b * b - 1 := by omega
    positivity
  have c1 := le_cdiv (2 * D * (F.card * b * b + 4 * ∑ i ∈ F, i * i - 2 * (∑ i ∈ F, i) * b))
    (b ^ 3) hden1
  have c2 := le_cdiv (2 * D) (3 * b * (b * b - 1)) hden2
  unfold momA
  rw [← hb]
  push_cast
  rw [Nat.cast_mul, Nat.cast_sub hsub] at c1
  rw [Nat.cast_mul (3 * b), Nat.cast_sub (by nlinarith : 1 ≤ b * b)] at c2
  push_cast at c1 c2
  have hb' : (b : ℝ) = bR := by rw [hb, hbR]; push_cast; ring
  rw [hb'] at c1 c2
  have hD := D_pos
  have hc : (0 : ℝ) ≤ F.card := by positivity
  have e : (D : ℝ) * ((2 / bR + K) * F.card + (-4 / bR ^ 2) * (∑ i ∈ F, (i : ℝ)) +
      (8 / bR ^ 3) * (∑ i ∈ F, (i : ℝ) * i)) =
      2 * D * (F.card * bR * bR + 4 * ∑ i ∈ F, (i : ℝ) * i - 2 * (∑ i ∈ F, (i : ℝ)) * bR) /
        bR ^ 3 + F.card * (2 * D / (3 * bR * (bR * bR - 1))) := by
    have : bR * bR - 1 ≠ 0 := by nlinarith
    have : bR ^ 2 - 1 ≠ 0 := by nlinarith
    simp only [K]
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left hsum hD.le
  rw [e] at this
  push_cast at this
  have h2 := mul_le_mul_of_nonneg_left c2 hc
  linarith

lemma log_add_ge_mom {B i : ℕ} (hB : 1 ≤ B) :
    Real.log B + ((1 / B) * (i : ℝ) + (-1 / (2 * B ^ 2)) * ((i : ℝ) * i)) ≤
      Real.log ((B + i : ℕ) : ℝ) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hi : (0 : ℝ) ≤ i := by positivity
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; simp
  have hH := hasSum_log B i hB hpos
  have h1 := sum_le_hasSum (range 1) (fun k _ => sterm_nonneg (by positivity) k) hH
  simp only [Finset.range_one, Finset.sum_singleton, sterm] at h1
  have hsplit : Real.log ((B + i : ℕ) : ℝ) = Real.log B + Real.log (1 + (i : ℝ) / B) := by
    rw [← Real.log_mul hB'.ne' (by positivity)]; congr 1; push_cast; field_simp
  rw [hsplit]
  have e : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * ((i : ℝ) / (2 * B + i : ℕ)) ^ (2 * 0 + 1) -
      ((1 / B) * (i : ℝ) + (-1 / (2 * B ^ 2)) * ((i : ℝ) * i)) =
      (i : ℝ) ^ 3 / (2 * B ^ 2 * (2 * B + i)) := by
    push_cast; field_simp; ring
  have : (0 : ℝ) ≤ (i : ℝ) ^ 3 / (2 * B ^ 2 * (2 * B + i)) := by positivity
  linarith

theorem momT_le (B : ℕ) (hB : 1 ≤ B) (F : Finset ℕ) (hF : ∀ i ∈ F, i ≤ 2 * B) :
    (momT B F.card (∑ i ∈ F, i) (∑ i ∈ F, i * i) : ℝ) ≤
      D * ∑ i ∈ F, Real.log ((B + i : ℕ) : ℝ) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hterm : ∀ i ∈ F, Real.log B + (1 / B) * (i : ℝ) + (-1 / (2 * B ^ 2)) * ((i : ℝ) * i) ≤
      Real.log ((B + i : ℕ) : ℝ) := fun i _ => by
    have := log_add_ge_mom (B := B) (i := i) hB; linarith
  have hsum := Finset.sum_le_sum hterm
  rw [sum_quad] at hsum
  have hsub : ∑ i ∈ F, i * i ≤ 2 * B * ∑ i ∈ F, i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_right i (hF i hi)
  have hl := logLoNatC_le hB
  have hfl := div_le' (D * (2 * B * ∑ i ∈ F, i - ∑ i ∈ F, i * i)) (2 * B * B)
  unfold momT
  push_cast
  rw [Nat.cast_mul D, Nat.cast_sub hsub] at hfl
  push_cast at hfl
  have hD := D_pos
  have e : (D : ℝ) * (Real.log B * F.card + (1 / B) * (∑ i ∈ F, (i : ℝ)) +
      (-1 / (2 * B ^ 2)) * (∑ i ∈ F, (i : ℝ) * i)) =
      F.card * (D * Real.log B) + D * (2 * B * (∑ i ∈ F, (i : ℝ)) - ∑ i ∈ F, (i : ℝ) * i) /
        (2 * B * B) := by
    field_simp; ring
  have := mul_le_mul_of_nonneg_left hsum hD.le
  rw [e] at this
  push_cast at this
  have hc : (0 : ℝ) ≤ F.card := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hc]

lemma segLen_pos (B : ℕ) : 0 < segLen B := by unfold segLen; positivity

lemma segLen_le {B : ℕ} (hB : 1 ≤ B) : segLen B ≤ B := by
  unfold segLen
  have h2 : 2 ^ Nat.log2 B ≤ B := Nat.log2_self_le (by omega)
  calc 2 ^ min 22 (Nat.log2 B - 10) ≤ 2 ^ Nat.log2 B :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ B := h2

theorem segStep_valid (x0 : ℕ) (sp : Array ℕ) (s : St) (hv : Valid x0 s) :
    Valid x0 (segStep sp s) := by
  obtain ⟨hB2, U, hU, hP, hA, hT, hC⟩ := hv
  set B := s.B with hBdef
  set h := segLen B
  set arr := sieveSeg sp B h
  have hinv := sieveSeg_inv sp B h
  set F := unmarked arr h
  set U' := U ∪ F.image (B + ·)
  have hdisj : Disjoint U (F.image (B + ·)) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm'
    have := (hU _ hm).2; omega
  have hinj : Set.InjOn (B + ·) (F : Set ℕ) := fun a _ b _ hab => by simpa using hab
  have hsumU' : ∀ f : ℕ → ℝ, ∑ m ∈ U', f m = ∑ m ∈ U, f m + ∑ i ∈ F, f (B + i) := by
    intro f; rw [Finset.sum_union hdisj, Finset.sum_image hinj]
  have hU' : ∀ m ∈ U', 2 ≤ m ∧ m < B + h := by
    intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · have := hU m hm; omega
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      have : i < h := by simp [F, unmarked] at hi; exact hi.1
      omega
  have hP' : ∀ p, p.Prime → p < B + h → p ∈ U' := by
    intro p hp hph
    by_cases hpB : p < B
    · exact Finset.mem_union_left _ (hP p hp hpB)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨p - B, prime_mem_unmarked hinv (by omega) ?_, show B + (p - B) = p by omega⟩
      rwa [show B + (p - B) = p by omega]
  have hcast : ∀ i, ((B + i : ℕ) : ℝ) = (B : ℝ) + i := fun i => by push_cast; rfl
  unfold segStep
  dsimp only
  split_ifs with hex
  · -- exact mode
    rw [scanExact_eq]
    refine ⟨show 2 ≤ B + h by omega, U', hU', hP', ?_, ?_, hC⟩
    · rw [hsumU', mul_add]
      push_cast
      have : (D : ℝ) * ∑ i ∈ F, Real.log (1 + 1 / ((B + i : ℕ) : ℝ)) ≤
          ∑ i ∈ F, (logUpS (B + i) 1 : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => le_logUp1 (B + i) (by omega)
      simp only [hcast] at this ⊢
      linarith
    · rw [hsumU', mul_add]
      push_cast
      have : ∑ i ∈ F, (logLoNatC (B + i) : ℝ) ≤
          (D : ℝ) * ∑ i ∈ F, Real.log ((B + i : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => logLoNatC_le (by omega)
      simp only [hcast] at this ⊢
      linarith
  · -- moment mode
    have hhB := segLen_le (B := B) (by omega)
    rw [scanMom_eq]
    have hFi : ∀ i ∈ F, i ≤ 2 * B := by
      intro i hi; have : i < h := by simp [F, unmarked] at hi; exact hi.1
      omega
    refine ⟨show 2 ≤ B + h by omega, U', hU', hP', ?_, ?_, hC⟩
    · rw [hsumU', mul_add]
      push_cast
      have := momA_ge B (by omega) F
      simp only [hcast] at this ⊢
      linarith
    · rw [hsumU', mul_add]
      push_cast
      have := momT_le B (by omega) F hFi
      simp only [hcast] at this ⊢
      linarith

end Robin.Compute
