import GoldbachAverage.Statement2
import GoldbachAverage.Main
import Cramer.MeanSquare.Main

/-!
# Fujii's theorem: `Σ_{n ≤ x} G(n) = x²/2 + O(x^{3/2})` under RH

The input is Cramér's mean square `∫_1^X (ψ(t) − t)² dt ≪ X²` under RH (cramer-rh's
`Cramer.meanSquare_of_RH`). Write `E(t) = ψ(t) − t`. By `GoldbachAverage/Sum.lean`,

  `S(N) − N²/2 = −N/2 + Σ_{k<N} E(k) + Σ_{a ≤ N} Λ(a) E(N − a)`.

The pointwise bound `|E| ≪ √N log² N` costs `log² N` in the last sum. Instead, with
`h = ⌊√N⌋`:

1. `sample`: since `ψ` is nondecreasing, `E(c) ≤ E(t) + h` on `[c, c+h]` and
   `E(c) ≥ E(t) − h` on `[c−h, c]`, so `h E(c)² ≤ 2 ∫_{c−h}^{c+h} E² + 2h³`; summed over an
   arithmetic progression of step `h` (`sampleSum`), `h Σ_j E(s + jh)² ≤ 4 ∫ E² + 2Kh³`.
2. `blocks_le`: cut `a ∈ [1, N]` into blocks `(jh, jh+h]`. On a block, `N − a` lies between
   `N − jh − h` and `N − jh`, so `|E(N−a)| ≤ |E(N−jh)| + |E(N−jh−h)| + h` (monotonicity again),
   and the block carries `Λ`-mass `ψ(jh+h) − ψ(jh) = h + E(jh+h) − E(jh)`.
3. `xy ≤ (x² + y²)/2` turns the block sum into four sampled sums of `E²` at step `h`, each
   `≪ (1/h) ∫_{−2h}^{N+2h} E² + Kh³ ≪ N²/h`. So the prime-weighted sum is `≪ N²/h ≪ N^{3/2}`
   with no logarithm. The sum `Σ_{k<N} E(k)` is the same estimate at step `1`.

`fujii_nat_of_meanSquare` is unconditional given the mean-square hypothesis;
`fujii_of_RH` feeds it `Cramer.meanSquare_of_RH`.
-/

namespace GoldbachAverage.Fujii

open ArithmeticFunction Chebyshev Filter Asymptotics MeasureTheory intervalIntegral

/-- `E(t) = ψ(t) − t`. -/
noncomputable abbrev E (t : ℝ) : ℝ := ψ t - t

lemma ii (a b : ℝ) : IntervalIntegrable (fun t : ℝ => E t ^ 2) volume a b :=
  Cramer.MeanSq.intervalIntegrable_sq a b

lemma int_mono {a b c d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    (∫ t in a..b, E t ^ 2) ≤ (∫ t in c..d, E t ^ 2) :=
  integral_mono_interval hca hab hbd (Filter.Eventually.of_forall fun _ => sq_nonneg _) (ii c d)

/-- One sample: `h E(c)² ≤ 2 ∫_{c−h}^{c+h} E² + 2h³`. -/
lemma sample (c h : ℝ) (hh : 0 < h) :
    h * E c ^ 2 ≤ 2 * (∫ t in (c - h)..(c + h), E t ^ 2) + 2 * h ^ 3 := by
  have key : ∀ a : ℝ, (∀ t ∈ Set.Icc a (a + h), |E c| ≤ |E t| + h) →
      h * E c ^ 2 ≤ 2 * (∫ t in a..(a + h), E t ^ 2) + 2 * h ^ 3 := by
    intro a ha
    have hpt : ∀ t ∈ Set.Icc a (a + h), E c ^ 2 ≤ 2 * E t ^ 2 + 2 * h ^ 2 := by
      intro t ht
      have h1 := ha t ht
      have h0 : 0 ≤ |E c| := abs_nonneg _
      have e1 : E c ^ 2 = |E c| ^ 2 := (sq_abs _).symm
      have e2 : E t ^ 2 = |E t| ^ 2 := (sq_abs _).symm
      rw [e1, e2]
      nlinarith [sq_nonneg (|E t| - h)]
    have hI : (∫ _t in a..(a + h), E c ^ 2) ≤ (∫ t in a..(a + h), (2 * E t ^ 2 + 2 * h ^ 2)) :=
      integral_mono_on (by linarith) (by simp) (((ii a (a + h)).const_mul 2).add (by simp)) hpt
    rw [intervalIntegral.integral_const, integral_add ((ii a (a + h)).const_mul 2) (by simp), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at hI
    simp only [smul_eq_mul, add_sub_cancel_left] at hI
    nlinarith
  by_cases hc : 0 ≤ E c
  · have := key c fun t ht => by
      have hp : ψ c ≤ ψ t := psi_mono ht.1
      rw [abs_of_nonneg hc]
      have := le_abs_self (E t)
      simp only [E] at *
      linarith [ht.2]
    have hm := int_mono (a := c) (b := c + h) (c := c - h) (d := c + h) (by linarith)
      (by linarith) le_rfl
    linarith
  · rw [not_le] at hc
    have := key (c - h) fun t ht => by
      have hp : ψ t ≤ ψ c := psi_mono (by linarith [ht.2])
      rw [abs_of_neg hc]
      have := neg_abs_le (E t)
      simp only [E] at *
      linarith [ht.1]
    have hm := int_mono (a := c - h) (b := c - h + h) (c := c - h) (d := c + h) le_rfl
      (by linarith) (by linarith)
    linarith

/-- Samples along a progression of step `h`. -/
lemma sampleSum (s h : ℝ) (hh : 0 < h) (K : ℕ) :
    h * ∑ j ∈ Finset.range K, E (s + j * h) ^ 2 ≤
      4 * (∫ t in (s - h)..(s + K * h), E t ^ 2) + 2 * K * h ^ 3 := by
  set a : ℕ → ℝ := fun k => s - h + k * h with ha
  have hadj1 : ∑ j ∈ Finset.range K, (∫ t in a j..a (j + 1), E t ^ 2) =
      (∫ t in a 0..a K, E t ^ 2) :=
    sum_integral_adjacent_intervals fun k _ => ii _ _
  have hadj2 : ∑ j ∈ Finset.range K, (∫ t in a (j + 1)..a (j + 1 + 1), E t ^ 2) =
      (∫ t in a (0 + 1)..a (K + 1), E t ^ 2) :=
    sum_integral_adjacent_intervals (a := fun k => a (k + 1)) fun k _ => ii _ _
  have hsplit : ∀ j : ℕ, (∫ t in (s + j * h - h)..(s + j * h + h), E t ^ 2) =
      (∫ t in a j..a (j + 1), E t ^ 2) + (∫ t in a (j + 1)..a (j + 1 + 1), E t ^ 2) := by
    intro j
    rw [integral_add_adjacent_intervals (ii _ _) (ii _ _)]
    have e1 : s + (j : ℝ) * h - h = a j := by simp only [ha]; ring
    have e2 : s + (j : ℝ) * h + h = a (j + 1 + 1) := by simp only [ha]; push_cast; ring
    rw [e1, e2]
  have h1 : (∫ t in a 0..a K, E t ^ 2) ≤ (∫ t in (s - h)..(s + K * h), E t ^ 2) :=
    int_mono (by simp [ha])
      (by simp only [ha, Nat.cast_zero, zero_mul]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) K) hh.le])
      (by simp only [ha]; linarith)
  have h2 : (∫ t in a (0 + 1)..a (K + 1), E t ^ 2) ≤ (∫ t in (s - h)..(s + K * h), E t ^ 2) :=
    int_mono (by simp only [ha]; push_cast; linarith)
      (by simp only [ha]; push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) K) hh.le])
      (by simp only [ha]; push_cast; linarith)
  calc h * ∑ j ∈ Finset.range K, E (s + j * h) ^ 2
      = ∑ j ∈ Finset.range K, h * E (s + j * h) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range K, (2 * (∫ t in (s + j * h - h)..(s + j * h + h), E t ^ 2)
          + 2 * h ^ 3) := Finset.sum_le_sum fun j _ => sample _ h hh
    _ = 2 * (∫ t in a 0..a K, E t ^ 2) + 2 * (∫ t in a (0 + 1)..a (K + 1), E t ^ 2)
          + 2 * K * h ^ 3 := by
        simp_rw [hsplit, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, hadj1, hadj2]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := by linarith

lemma sum_blocks (f : ℕ → ℝ) (h K : ℕ) :
    ∑ a ∈ Finset.range (K * h), f a =
      ∑ j ∈ Finset.range K, ∑ r ∈ Finset.range h, f (j * h + r) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- `|E(N − a)|` on the block `a ∈ (jh, jh+h]` is controlled by the two end samples. -/
lemma pt (N h j r : ℕ) (hr : r < h) (ha : j * h + r + 1 ≤ N) :
    |E ((N - (j * h + r + 1) : ℕ) : ℝ)| ≤
      |E ((N - j * h : ℕ) : ℝ)| + |E ((N - (j * h + h) : ℕ) : ℝ)| + h := by
  generalize j * h = m at ha ⊢
  have n1 : N - (m + r + 1) ≤ N - m := by omega
  have n2 : N - m ≤ N - (m + r + 1) + h := by omega
  have n3 : N - (m + h) ≤ N - (m + r + 1) := by omega
  have n4 : N - (m + r + 1) ≤ N - (m + h) + h := by omega
  have r1 : ((N - (m + r + 1) : ℕ) : ℝ) ≤ ((N - m : ℕ) : ℝ) := by exact_mod_cast n1
  have r2 : ((N - m : ℕ) : ℝ) ≤ ((N - (m + r + 1) : ℕ) : ℝ) + h := by exact_mod_cast n2
  have r3 : ((N - (m + h) : ℕ) : ℝ) ≤ ((N - (m + r + 1) : ℕ) : ℝ) := by exact_mod_cast n3
  have r4 : ((N - (m + r + 1) : ℕ) : ℝ) ≤ ((N - (m + h) : ℕ) : ℝ) + h := by exact_mod_cast n4
  have p1 := psi_mono r1
  have p2 := psi_mono r3
  have a1 := le_abs_self (E ((N - m : ℕ) : ℝ))
  have a2 := neg_abs_le (E ((N - (m + h) : ℕ) : ℝ))
  have a3 := abs_nonneg (E ((N - m : ℕ) : ℝ))
  have a4 := abs_nonneg (E ((N - (m + h) : ℕ) : ℝ))
  simp only [E] at *
  rw [abs_le]
  constructor <;> linarith

lemma psi_block (j h : ℕ) :
    ∑ r ∈ Finset.range h, (Λ (j * h + r + 1) : ℝ) =
      ψ ((j * h + h : ℕ) : ℝ) - ψ ((j * h : ℕ) : ℝ) := by
  rw [psi_natCast, psi_natCast, show j * h + h + 1 = (j * h + 1) + h by ring,
    Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.add_right_comm]

/-- The prime-weighted sum, cut into blocks of length `h`. -/
lemma blocks_le (N h : ℕ) (hh : 1 ≤ h) :
    ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * |E ((N - a : ℕ) : ℝ)| ≤
      ∑ j ∈ Finset.range (N / h + 1), (ψ ((j * h + h : ℕ) : ℝ) - ψ ((j * h : ℕ) : ℝ)) *
        (|E ((N - j * h : ℕ) : ℝ)| + |E ((N - (j * h + h) : ℕ) : ℝ)| + h) := by
  set K := N / h + 1 with hK
  have hNK : N + 1 ≤ K * h + 1 := by
    have h1 := Nat.div_add_mod N h
    have h2 := Nat.mod_lt N (by omega : h > 0)
    rw [hK, add_mul, one_mul, mul_comm]
    generalize h * (N / h) = q at h1 ⊢
    omega
  set g : ℕ → ℝ := fun a => if a ≤ N then (Λ a : ℝ) * |E ((N - a : ℕ) : ℝ)| else 0 with hg
  have g0 : ∀ a, 0 ≤ g a := fun a => by
    simp only [hg]; split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (abs_nonneg _)
    · exact le_rfl
  calc ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * |E ((N - a : ℕ) : ℝ)|
      = ∑ a ∈ Finset.range (N + 1), g a := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have : a ≤ N := by simpa [Nat.lt_succ_iff] using ha
        simp [hg, this]
    _ ≤ ∑ a ∈ Finset.range (K * h + 1), g a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNK)
          fun a _ _ => g0 a
    _ = ∑ a ∈ Finset.range (K * h), g (a + 1) := by
        rw [Finset.sum_range_succ']
        simp [hg]
    _ = ∑ j ∈ Finset.range K, ∑ r ∈ Finset.range h, g (j * h + r + 1) :=
        sum_blocks (fun a => g (a + 1)) h K
    _ ≤ _ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← psi_block, Finset.sum_mul]
        refine Finset.sum_le_sum fun r hr => ?_
        have hr' : r < h := Finset.mem_range.mp hr
        simp only [hg]
        split_ifs with ha
        · exact mul_le_mul_of_nonneg_left (pt N h j r hr' ha) vonMangoldt_nonneg
        · exact mul_nonneg vonMangoldt_nonneg (by positivity)

/-- `xy ≤ (x² + y²)/2` with three-term squares. -/
lemma amgm (X Y hh p q u v : ℝ) (hX0 : 0 ≤ X) (hX : X ≤ hh + |p| + |q|)
    (hY : Y = |u| + |v| + hh) (hh0 : 0 ≤ hh) :
    X * Y ≤ 3 / 2 * (2 * hh ^ 2 + p ^ 2 + q ^ 2 + u ^ 2 + v ^ 2) := by
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have h1 : X * Y ≤ (hh + |p| + |q|) * Y := mul_le_mul_of_nonneg_right hX hY0
  have ep := sq_abs p
  have eq := sq_abs q
  have eu := sq_abs u
  have ev := sq_abs v
  rw [hY] at h1
  nlinarith [sq_nonneg (hh + |p| + |q| - (|u| + |v| + hh)), sq_nonneg (hh - |p|),
    sq_nonneg (hh - |q|), sq_nonneg (|p| - |q|), sq_nonneg (|u| - |v|), sq_nonneg (|u| - hh),
    sq_nonneg (|v| - hh)]

lemma E_nat_sub_sq_le (N m : ℕ) : E ((N - m : ℕ) : ℝ) ^ 2 ≤ E ((N : ℝ) - m) ^ 2 := by
  by_cases hm : m ≤ N
  · rw [Nat.cast_sub hm]
  · have : N - m = 0 := by omega
    rw [this]
    simp [E, psi_zero]
    positivity

/-- The bound on `∫_{−2h}^{X} E²` from the mean-square hypothesis. -/
lemma J_le (C X₀ : ℝ) (hms : ∀ X ≥ X₀, (∫ t in (1 : ℝ)..X, E t ^ 2) ≤ C * X ^ 2)
    (h X : ℝ) (hh : 1 ≤ h) (hX : X₀ ≤ X) (_hX1 : 1 ≤ X) :
    (∫ t in (-2 * h)..X, E t ^ 2) ≤ 12 * h ^ 3 + C * X ^ 2 := by
  rw [← integral_add_adjacent_intervals (ii (-2 * h) 1) (ii 1 X)]
  have hsmall : (∫ t in (-2 * h)..1, E t ^ 2) ≤ (∫ _t in (-2 * h)..1, 4 * h ^ 2) := by
    refine integral_mono_on (by linarith) (ii _ _) (by simp) fun t ht => ?_
    have : ψ t = 0 := psi_eq_zero_of_lt_two (by linarith [ht.2])
    simp only [E, this, zero_sub, neg_sq]
    nlinarith [ht.1, ht.2]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hsmall
  have := hms X hX
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Mean square ⇒ Fujii**, for integers. -/
theorem fujii_nat_of_meanSquare (C X₀ : ℝ) (hC : 0 ≤ C)
    (hms : ∀ X ≥ X₀, (∫ t in (1 : ℝ)..X, E t ^ 2) ≤ C * X ^ 2) (N : ℕ) (hN : 4 ≤ N)
    (hNX : X₀ ≤ N) :
    |goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2| ≤ (688 + 468 * C) * ((N : ℝ) * Real.sqrt N) := by
  set h : ℕ := Nat.sqrt N with hhdef
  have hh1 : 1 ≤ h := Nat.le_sqrt.mpr (by omega)
  have hhN : h * h ≤ N := Nat.sqrt_le N
  have hNh : N < (h + 1) * (h + 1) := Nat.lt_succ_sqrt N
  set q : ℕ := N / h with hq
  have hqh : q * h ≤ N := Nat.div_mul_le_self N h
  have hqh2 : N < q * h + h := by
    have h1 := Nat.div_add_mod N h
    have h2 := Nat.mod_lt N (by omega : h > 0)
    rw [hq, mul_comm]
    generalize h * (N / h) = r at h1 ⊢
    omega
  -- real versions
  have H1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
  have HN : (h : ℝ) * h ≤ N := by exact_mod_cast hhN
  have NH : (N : ℝ) < (h + 1) * (h + 1) := by exact_mod_cast hNh
  have N4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have Q1 : (q : ℝ) * h ≤ N := by exact_mod_cast hqh
  have Q2 : (N : ℝ) < (q : ℝ) * h + h := by exact_mod_cast hqh2
  set H : ℝ := (h : ℝ) with hH
  set Nr : ℝ := (N : ℝ) with hNr
  have H0 : (0 : ℝ) < H := by linarith
  have HleN : H ≤ Nr := by nlinarith
  have Q0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  set J : ℝ := (∫ t in (-2 * H)..(Nr + 2 * H), E t ^ 2) with hJ
  have hJb : J ≤ 12 * H ^ 3 + C * (Nr + 2 * H) ^ 2 :=
    J_le C X₀ hms H (Nr + 2 * H) H1 (by linarith) (by linarith)
  -- the decomposition
  set e : ℕ → ℝ := fun k => E (k : ℝ) with he
  have hS : goldbachSum (N : ℝ) - Nr ^ 2 / 2 =
      -Nr / 2 + ∑ k ∈ Finset.range N, e k +
        ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a) := by
    rw [goldbachSum_eq_convolution]
    have hA : ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ((N : ℝ) - a) =
        (N : ℝ) * (N - 1) / 2 + ∑ k ∈ Finset.range N, e k := by
      rw [sum_vonMangoldt_mul_sub, ← sum_range_cast, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [he, E]
    have hsplit : ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ψ ((N - a : ℕ) : ℝ) =
        ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ((N : ℝ) - a) +
          ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have haN : a ≤ N := by simpa [Nat.lt_succ_iff] using ha
      simp only [he, E, Nat.cast_sub haN]
      ring
    rw [hsplit, hA, hNr]
    ring
  -- term A
  have hA2 : 1 * ∑ k ∈ Finset.range N, E (0 + (k : ℝ) * 1) ^ 2 ≤
      4 * (∫ t in (0 - 1)..(0 + (N : ℝ) * 1), E t ^ 2) + 2 * N * 1 ^ 3 :=
    sampleSum 0 1 one_pos N
  have hA3 : (∫ t in (0 - 1)..(0 + (N : ℝ) * 1), E t ^ 2) ≤ J :=
    int_mono (by linarith) (by linarith) (by linarith)
  have hAsq : ∑ k ∈ Finset.range N, e k ^ 2 ≤ 4 * J + 2 * Nr := by
    have : ∑ k ∈ Finset.range N, e k ^ 2 = ∑ k ∈ Finset.range N, E (0 + (k : ℝ) * 1) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [he]
    rw [this]
    linarith
  have hA : H * |∑ k ∈ Finset.range N, e k| ≤ (4 * J + 2 * Nr) / 2 + Nr * H ^ 2 / 2 := by
    have h1 : |∑ k ∈ Finset.range N, e k| ≤ ∑ k ∈ Finset.range N, |e k| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ k, H * |e k| ≤ (e k ^ 2 + H ^ 2) / 2 := fun k => by
      have := sq_abs (e k)
      nlinarith [sq_nonneg (|e k| - H)]
    calc H * |∑ k ∈ Finset.range N, e k| ≤ ∑ k ∈ Finset.range N, H * |e k| := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h1 H0.le
      _ ≤ ∑ k ∈ Finset.range N, (e k ^ 2 + H ^ 2) / 2 := Finset.sum_le_sum fun k _ => h2 k
      _ = (∑ k ∈ Finset.range N, e k ^ 2) / 2 + Nr * H ^ 2 / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
          simp [hNr]
          ring
      _ ≤ _ := by linarith
  -- term B
  set K : ℕ := q + 1 with hKdef
  have hB1 := blocks_le N h hh1
  rw [← hq, ← hKdef] at hB1
  have hB2 : ∑ j ∈ Finset.range K, (ψ ((j * h + h : ℕ) : ℝ) - ψ ((j * h : ℕ) : ℝ)) *
        (|E ((N - j * h : ℕ) : ℝ)| + |E ((N - (j * h + h) : ℕ) : ℝ)| + h) ≤
      ∑ j ∈ Finset.range K, 3 / 2 * (2 * H ^ 2 + E (0 + j * H) ^ 2 + E (H + j * H) ^ 2 +
        E ((Nr - q * H) + ((q - j : ℕ) : ℝ) * H) ^ 2 +
        E ((Nr - K * H) + ((q - j : ℕ) : ℝ) * H) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjq : j ≤ q := by have := Finset.mem_range.mp hj; omega
    have hjh : j * h ≤ N := le_trans (Nat.mul_le_mul_right h hjq) hqh
    have c1 : ((j * h + h : ℕ) : ℝ) = H + j * H := by push_cast; ring
    have c2 : ((j * h : ℕ) : ℝ) = 0 + j * H := by push_cast; ring
    have c3 : ((N - j * h : ℕ) : ℝ) = (Nr - q * H) + ((q - j : ℕ) : ℝ) * H := by
      rw [Nat.cast_sub hjh, Nat.cast_sub hjq]; push_cast; ring
    have c4 : (Nr - K * H) + ((q - j : ℕ) : ℝ) * H = (N : ℝ) - ((j * h + h : ℕ) : ℝ) := by
      rw [Nat.cast_sub hjq]; simp only [hKdef]; push_cast; ring
    have hmono : ψ ((j * h : ℕ) : ℝ) ≤ ψ ((j * h + h : ℕ) : ℝ) :=
      psi_mono (by exact_mod_cast Nat.le_add_right _ _)
    have hX : ψ ((j * h + h : ℕ) : ℝ) - ψ ((j * h : ℕ) : ℝ) ≤
        H + |E (0 + j * H)| + |E (H + j * H)| := by
      have a1 := le_abs_self (E (H + j * H))
      have a2 := neg_abs_le (E (0 + j * H))
      rw [c1, c2] at hmono ⊢
      simp only [E] at *
      linarith
    have h4 := E_nat_sub_sq_le N (j * h + h)
    rw [← c4] at h4
    have := amgm _ _ H (E (0 + j * H)) (E (H + j * H)) (E ((N - j * h : ℕ) : ℝ))
      (E ((N - (j * h + h) : ℕ) : ℝ)) (by linarith) hX rfl H0.le
    rw [c3] at this ⊢
    linarith
  -- the four sampled families
  have refl : ∀ s : ℝ, ∑ j ∈ Finset.range K, E (s + ((q - j : ℕ) : ℝ) * H) ^ 2 =
      ∑ j ∈ Finset.range K, E (s + (j : ℝ) * H) ^ 2 := by
    intro s
    rw [← Finset.sum_range_reflect (fun j => E (s + (j : ℝ) * H) ^ 2) K]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hKdef, Nat.add_sub_cancel]
  have Kr : (K : ℝ) = q + 1 := by simp only [hKdef]; push_cast; ring
  have KH : (K : ℝ) * H ≤ Nr + H := by rw [Kr]; nlinarith
  have KH2 : Nr ≤ (K : ℝ) * H := by rw [Kr]; nlinarith
  have fam : ∀ s : ℝ, -H ≤ s → s + K * H ≤ Nr + 2 * H →
      H * ∑ j ∈ Finset.range K, E (s + j * H) ^ 2 ≤ 4 * J + 2 * K * H ^ 3 := by
    intro s hs1 hs2
    have := sampleSum s H H0 K
    have hm : (∫ t in (s - H)..(s + K * H), E t ^ 2) ≤ J :=
      int_mono (by linarith) (by nlinarith [Nat.cast_nonneg (α := ℝ) K]) hs2
    linarith
  have F1 := fam 0 (by linarith) (by linarith)
  have F2 := fam H (by linarith) (by linarith)
  have F3 := fam (Nr - q * H) (by linarith) (by rw [Kr]; nlinarith)
  have F4 := fam (Nr - K * H) (by linarith) (by linarith)
  rw [← refl] at F3 F4
  have hBsum : ∑ j ∈ Finset.range K, 3 / 2 * (2 * H ^ 2 + E (0 + j * H) ^ 2 +
        E (H + j * H) ^ 2 + E ((Nr - q * H) + ((q - j : ℕ) : ℝ) * H) ^ 2 +
        E ((Nr - K * H) + ((q - j : ℕ) : ℝ) * H) ^ 2) =
      3 / 2 * (2 * K * H ^ 2 + ∑ j ∈ Finset.range K, E (0 + j * H) ^ 2 +
        ∑ j ∈ Finset.range K, E (H + j * H) ^ 2 +
        ∑ j ∈ Finset.range K, E ((Nr - q * H) + ((q - j : ℕ) : ℝ) * H) ^ 2 +
        ∑ j ∈ Finset.range K, E ((Nr - K * H) + ((q - j : ℕ) : ℝ) * H) ^ 2) := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hB : H * |∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a)| ≤
      15 * K * H ^ 3 + 24 * J := by
    have h0 : |∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a)| ≤
        ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * |E ((N - a : ℕ) : ℝ)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg : (0 : ℝ) ≤ Λ a)]
    have := h0.trans (hB1.trans (hB2.trans (le_of_eq hBsum)))
    have h5 := mul_le_mul_of_nonneg_left this H0.le
    have h6 : H * (3 / 2 * (2 * K * H ^ 2 + ∑ j ∈ Finset.range K, E (0 + j * H) ^ 2 +
        ∑ j ∈ Finset.range K, E (H + j * H) ^ 2 +
        ∑ j ∈ Finset.range K, E ((Nr - q * H) + ((q - j : ℕ) : ℝ) * H) ^ 2 +
        ∑ j ∈ Finset.range K, E ((Nr - K * H) + ((q - j : ℕ) : ℝ) * H) ^ 2)) =
        3 * K * H ^ 3 + 3 / 2 * (H * ∑ j ∈ Finset.range K, E (0 + j * H) ^ 2) +
        3 / 2 * (H * ∑ j ∈ Finset.range K, E (H + j * H) ^ 2) +
        3 / 2 * (H * ∑ j ∈ Finset.range K, E ((Nr - q * H) + ((q - j : ℕ) : ℝ) * H) ^ 2) +
        3 / 2 * (H * ∑ j ∈ Finset.range K, E ((Nr - K * H) + ((q - j : ℕ) : ℝ) * H) ^ 2) := by
      ring
    rw [h6] at h5
    linarith
  -- assembly
  have hfin : H * |goldbachSum (N : ℝ) - Nr ^ 2 / 2| ≤
      H * Nr / 2 + ((4 * J + 2 * Nr) / 2 + Nr * H ^ 2 / 2) + (15 * K * H ^ 3 + 24 * J) := by
    rw [hS]
    have t := abs_add_three (-Nr / 2) (∑ k ∈ Finset.range N, e k)
      (∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * e (N - a))
    have : |-Nr / 2| = Nr / 2 := by rw [abs_div, abs_neg, abs_of_nonneg (by linarith)]; norm_num
    rw [this] at t
    nlinarith
  have hKH3 : (K : ℝ) * H ^ 3 ≤ 2 * Nr ^ 2 := by
    have : (K : ℝ) * H ^ 3 = (K * H) * (H * H) := by ring
    rw [this]
    have : (K : ℝ) * H ≤ 2 * Nr := by linarith
    nlinarith
  have hH3 : H ^ 3 ≤ Nr ^ 2 := by
    have : H ^ 3 = H * (H * H) := by ring
    rw [this]; nlinarith
  have hJ2 : J ≤ 12 * Nr ^ 2 + 9 * C * Nr ^ 2 := by
    have : (Nr + 2 * H) ^ 2 ≤ 9 * Nr ^ 2 := by nlinarith
    nlinarith
  have hH2 : Nr * H ^ 2 ≤ Nr ^ 2 := by nlinarith
  have hHN : H * Nr ≤ Nr ^ 2 := by nlinarith
  have hmain : H * |goldbachSum (N : ℝ) - Nr ^ 2 / 2| ≤ (344 + 234 * C) * Nr ^ 2 := by
    nlinarith
  -- `N²/h ≤ 2 N √N`
  have hs : Real.sqrt Nr ≤ 2 * H := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt Nr := Real.sqrt_nonneg _
  have hsq : Real.sqrt Nr * Real.sqrt Nr = Nr := Real.mul_self_sqrt (by linarith)
  have hgoal : (344 + 234 * C) * Nr ^ 2 ≤ H * ((688 + 468 * C) * (Nr * Real.sqrt Nr)) := by
    have : Nr ^ 2 = Nr * (Real.sqrt Nr * Real.sqrt Nr) := by rw [hsq]; ring
    rw [this]
    have hC' : 0 ≤ 344 + 234 * C := by linarith
    have : Nr * Real.sqrt Nr * Real.sqrt Nr ≤ Nr * Real.sqrt Nr * (2 * H) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  have := hmain.trans hgoal
  exact le_of_mul_le_mul_left this H0

end GoldbachAverage.Fujii

namespace GoldbachAverage

open Fujii Chebyshev Filter Asymptotics

/-- **Cramér's mean square ⇒ Fujii's bound**, with no RH in the statement. -/
theorem fujiiBound_of_meanSquare (h : Cramer.CramerMeanSquare) : FujiiBound := by
  obtain ⟨C, hC, hb⟩ := h.exists_pos
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hb.bound
  have hms : ∀ X ≥ max X₀ 1, (∫ t in (1 : ℝ)..X, E t ^ 2) ≤ C * X ^ 2 := by
    intro X hX
    have := hX₀ X (le_trans (le_max_left _ _) hX)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg X)] at this
    exact (le_abs_self _).trans this
  refine ⟨688 + 468 * C + 1, max X₀ 1 + 5, fun x hx => ?_⟩
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hx0 : 0 ≤ x := by linarith [le_max_right X₀ 1]
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN4 : 4 ≤ N := Nat.le_floor (by push_cast; linarith [le_max_right X₀ 1])
  have hNX : max X₀ 1 ≤ (N : ℝ) := by linarith
  have h := fujii_nat_of_meanSquare C (max X₀ 1) hC.le hms N hN4 hNX
  have hS : goldbachSum x = goldbachSum (N : ℝ) := by
    unfold goldbachSum; rw [Nat.floor_natCast]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hdiff : |(N : ℝ) ^ 2 / 2 - x ^ 2 / 2| ≤ x := by
    rw [abs_le]; constructor <;> nlinarith
  have hsx : Real.sqrt N ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
  have hs1 : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]; linarith [le_max_right X₀ 1]
  have hQ : (N : ℝ) * Real.sqrt N ≤ x * Real.sqrt x :=
    mul_le_mul hNx hsx (Real.sqrt_nonneg _) hx0
  have hxx : x ≤ x * Real.sqrt x := by nlinarith
  have hC0 : 0 ≤ 688 + 468 * C := by linarith
  rw [hS]
  calc |goldbachSum (N : ℝ) - x ^ 2 / 2|
      = |(goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2) + ((N : ℝ) ^ 2 / 2 - x ^ 2 / 2)| := by
        ring_nf
    _ ≤ |goldbachSum (N : ℝ) - (N : ℝ) ^ 2 / 2| + |(N : ℝ) ^ 2 / 2 - x ^ 2 / 2| :=
        abs_add_le _ _
    _ ≤ (688 + 468 * C) * (x * Real.sqrt x) + x * Real.sqrt x := by
        have := mul_le_mul_of_nonneg_left hQ hC0
        linarith
    _ = _ := by ring

theorem fujiiStatement_of_bound (h : FujiiBound) : FujiiStatement := by
  obtain ⟨C, x₀, hb⟩ := h
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop x₀, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have e : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [e]
  exact hb x hx

/-- **Fujii (1991)**: under RH, `|Σ_{n ≤ x} G(n) − x²/2| ≤ C x^{3/2}` for large `x`. -/
theorem fujii_of_RH (hRH : RiemannHypothesis) : FujiiBound :=
  fujiiBound_of_meanSquare (Cramer.meanSquare_of_RH hRH)

/-- **Fujii (1991)**: under RH, `Σ_{n ≤ x} G(n) = x²/2 + O(x^{3/2})`. -/
theorem fujiiStatement_of_RH (hRH : RiemannHypothesis) : FujiiStatement :=
  fujiiStatement_of_bound (fujii_of_RH hRH)

end GoldbachAverage
