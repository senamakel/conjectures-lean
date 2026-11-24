import Mertens.Statement

/-!
# Finite sums of `fract` and of the Bernoulli polynomial `B₂`

* `sum_fract_add_div`: Hermite's identity for `fract`,
  `∑_{i<n} {x + i/n} = {n x} + (n-1)/2`.
* `sum_B2_fract_add_div`: the distribution relation `∑_{j<r} B₂({u + j/r}) = B₂({r u})/r`.
* `sum_B2_fract_mul_div`: `∑_{i<q} B₂({r i/q}) = gcd(r, q)²/(6q)`.
-/

namespace Mertens

open Finset

/-- The second Bernoulli polynomial `B₂(u) = u² - u + 1/6`. -/
noncomputable def B2 (u : ℝ) : ℝ := u ^ 2 - u + 1 / 6

lemma sum_range_cast_id (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_range_quad (a b c : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (a * (i : ℝ) ^ 2 + b * i + c) =
      a * (n * (n - 1) * (2 * n - 1) / 6) + b * (n * (n - 1) / 2) + c * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Hermite's identity for the fractional part. -/
lemma sum_fract_add_div (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ range n, Int.fract (x + i / n) = Int.fract (n * x) + (n - 1) / 2 := by
  have h := Int.sum_floor_add_div x n
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold Int.fract
  rw [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_range_cast_id, sum_const, card_range,
    nsmul_eq_mul]
  have h' : ∑ i ∈ range n, (⌊x + (i : ℝ) / n⌋ : ℝ) = (⌊(n : ℝ) * x⌋ : ℝ) := by exact_mod_cast h
  rw [h']
  field_simp
  ring

/-- Shifting the window of a sum of an `r`-periodic function on `ℤ`. -/
lemma sum_range_periodic_shift (ψ : ℤ → ℝ) (r : ℕ) (hψ : ∀ a, ψ (a + r) = ψ a) (n : ℤ) :
    ∑ j ∈ range r, ψ (n + j) = ∑ j ∈ range r, ψ j := by
  have step : ∀ m : ℤ, ∑ j ∈ range r, ψ (m + 1 + j) = ∑ j ∈ range r, ψ (m + j) := by
    intro m
    have h1 := sum_range_succ' (fun j : ℕ => ψ (m + j)) r
    have h2 := sum_range_succ (fun j : ℕ => ψ (m + j)) r
    rw [h1] at h2
    have h3 : ∑ j ∈ range r, ψ (m + ((j + 1 : ℕ) : ℤ)) = ∑ j ∈ range r, ψ (m + 1 + j) := by
      refine sum_congr rfl fun j _ => ?_; push_cast; ring_nf
    rw [h3, hψ] at h2
    simp only [Nat.cast_zero, add_zero] at h2
    linarith
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => rw [step, ih]
  | pred k ih =>
    rw [← ih, ← step]
    ring_nf

/-- The distribution relation for `B₂`. -/
lemma sum_B2_fract_add_div (u : ℝ) {r : ℕ} (hr : 0 < r) :
    ∑ j ∈ range r, B2 (Int.fract (u + j / r)) = B2 (Int.fract (r * u)) / r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set w := Int.fract ((r : ℝ) * u) with hw
  set n := ⌊(r : ℝ) * u⌋
  have hw0 : 0 ≤ w := Int.fract_nonneg _
  have hw1 : w < 1 := Int.fract_lt_one _
  have hu : u = (n + w) / r := by
    rw [hw, Int.floor_add_fract]; field_simp
  set ψ : ℤ → ℝ := fun a => B2 (Int.fract ((a + w) / r))
  have hψ : ∀ a, ψ (a + r) = ψ a := by
    intro a
    simp only [ψ]
    congr 1
    rw [show (((a + r : ℤ) : ℝ) + w) / r = ((a : ℝ) + w) / r + 1 by push_cast; field_simp; ring,
      Int.fract_add_one]
  have h1 : ∀ j ∈ range r, B2 (Int.fract (u + j / r)) = ψ (n + j) := by
    intro j _
    simp only [ψ]
    congr 2
    rw [hu]; push_cast; field_simp; ring
  rw [sum_congr rfl h1, sum_range_periodic_shift ψ r hψ n]
  have h2 : ∀ j ∈ range r, ψ j = (1 / (r : ℝ) ^ 2) * (j : ℝ) ^ 2 + ((2 * w - r) / (r : ℝ) ^ 2) * j +
      (w ^ 2 / (r : ℝ) ^ 2 - w / r + 1 / 6) := by
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ r := by exact_mod_cast (mem_range.1 hj)
    simp only [ψ]
    rw [Int.fract_eq_self.2 ⟨by push_cast; positivity, by
      push_cast; rw [div_lt_one hr0]; linarith⟩]
    unfold B2
    push_cast
    field_simp
    ring
  rw [sum_congr rfl h2, sum_range_quad]
  unfold B2
  field_simp
  ring

/-- `∑_{i<g m} χ(i) = g ∑_{i<m} χ(i)` for an `m`-periodic `χ`. -/
lemma sum_range_mul_periodic (χ : ℕ → ℝ) (m : ℕ) (hχ : ∀ i, χ (i + m) = χ i) (g : ℕ) :
    ∑ i ∈ range (g * m), χ i = g * ∑ i ∈ range m, χ i := by
  have hk : ∀ k i, χ (k * m + i) = χ i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro i; rw [show (k + 1) * m + i = (k * m + i) + m by ring, hχ, ih]
  induction g with
  | zero => simp
  | succ g ih =>
    rw [show (g + 1) * m = g * m + m by ring, sum_range_add, ih]
    simp only [hk]
    push_cast; ring

/-- `χ (i % m) = χ i` for an `m`-periodic `χ`. -/
lemma periodic_mod (χ : ℕ → ℝ) (m : ℕ) (hχ : ∀ i, χ (i + m) = χ i) (i : ℕ) :
    χ (i % m) = χ i := by
  have hk : ∀ k i, χ (i + m * k) = χ i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro i; rw [show i + m * (k + 1) = (i + m * k) + m by ring, hχ, ih]
  conv_rhs => rw [← Nat.mod_add_div i m]
  rw [hk]

/-- Multiplication by a unit permutes the residues. -/
lemma sum_range_mul_unit (χ : ℕ → ℝ) {m a : ℕ} (hχ : ∀ i, χ (i + m) = χ i)
    (ha : Nat.Coprime a m) :
    ∑ i ∈ range m, χ (a * i) = ∑ i ∈ range m, χ i := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hinj : Set.InjOn (fun i => a * i % m) (range m : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    have h : a * i ≡ a * j [MOD m] := hij
    have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact ha) h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  have himg : (range m).image (fun i => a * i % m) = range m := by
    refine eq_of_subset_of_card_le (fun k hk => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hk
      exact mem_range.2 (Nat.mod_lt _ hm)
    · rw [card_image_of_injOn hinj]
  calc ∑ i ∈ range m, χ (a * i) = ∑ i ∈ range m, χ (a * i % m) :=
        sum_congr rfl fun i _ => (periodic_mod χ m hχ _).symm
    _ = ∑ k ∈ (range m).image (fun i => a * i % m), χ k := (sum_image hinj).symm
    _ = ∑ i ∈ range m, χ i := by rw [himg]

/-- `∑_{i<q} B₂({r i / q}) = gcd(r, q)² / (6 q)`. -/
lemma sum_B2_fract_mul_div (r : ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ i ∈ range q, B2 (Int.fract ((r : ℝ) * i / q)) = (Nat.gcd r q : ℝ) ^ 2 / (6 * q) := by
  set g := Nat.gcd r q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r hq
  obtain ⟨r', hr'⟩ : g ∣ r := Nat.gcd_dvd_left r q
  obtain ⟨q', hq'⟩ : g ∣ q := Nat.gcd_dvd_right r q
  have hq'0 : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h, mul_zero] at hq'; omega
    · exact h
  have hcop : Nat.Coprime r' q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := r) (n := q) hg0
    rw [← hg] at this
    rwa [hr', hq', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  set χ : ℕ → ℝ := fun i => B2 (Int.fract ((r' : ℝ) * i / q'))
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'0
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hχ : ∀ i, χ (i + q') = χ i := by
    intro i
    simp only [χ]
    congr 1
    rw [show (r' : ℝ) * ((i + q' : ℕ) : ℝ) / q' = (r' : ℝ) * i / q' + (r' : ℕ) by
      push_cast; field_simp, Int.fract_add_natCast]
  have h1 : ∀ i ∈ range q, B2 (Int.fract ((r : ℝ) * i / q)) = χ i := by
    intro i _
    simp only [χ]
    congr 2
    rw [hr', hq']; push_cast; field_simp
  rw [sum_congr rfl h1, hq', sum_range_mul_periodic χ q' hχ g]
  set φ : ℕ → ℝ := fun i => B2 (Int.fract ((i : ℝ) / q'))
  have hφ : ∀ i, φ (i + q') = φ i := by
    intro i
    simp only [φ]
    congr 1
    rw [show (((i + q' : ℕ) : ℝ)) / q' = (i : ℝ) / q' + (1 : ℕ) by
      push_cast; field_simp, Int.fract_add_natCast]
  have h2 : ∑ i ∈ range q', χ i = ∑ i ∈ range q', φ i := by
    rw [← sum_range_mul_unit φ hφ hcop]
    refine sum_congr rfl fun i _ => ?_
    simp only [χ, φ]
    push_cast
    ring_nf
  have h3 : ∑ i ∈ range q', φ i = 1 / (6 * q') := by
    have := sum_B2_fract_add_div 0 hq'0
    simp only [zero_add, mul_zero, Int.fract_zero] at this
    simp only [φ]
    rw [this]; unfold B2; field_simp; ring
  rw [h2, h3]
  push_cast
  field_simp

end Mertens
