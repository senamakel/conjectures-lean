import LLS.Thm11.Boxes
import LLS.Thm11.Tail
import LLS.Thm11.Rough
import LLS.Statement

/-!
# LLS Theorem 1.1 under GRH, with the paper's `B(q)`

For `q ≥ 3000`, `L = log q`, `X = (L + B(q))²` and `x = ⌊X⌋`: if every prime `ℓ ≤ x` prime to
`q` lay in the proper subgroup `H`, a character `χ ≠ 1` trivial on `H` would be `1` on every
`n ≤ x` prime to `q`, and the budget would be `≤ 0` (`LLS.Thm11.budget11`). The elimination of
`ω(q)` and `σ(q)` (`LLS.Thm11.phi_pos`) and the one-variable bounds `F₁ > 0`, `F₂ > 0`
(`LLS/Thm11/Boxes.lean` for `x < 10^16`, `LLS/Thm11/Tail.lean` beyond) show it is `> 0`.
No finite computation over `q` is needed.
-/

namespace LLS.Thm11

open Real

theorem F1_pos (x : ℕ) (hx : 64 ≤ x) : 0 < F1 x := by
  rcases lt_or_ge x (10 ^ 16) with h | h
  · exact Box.f1_range x hx h
  · exact F1_tail x h

theorem R5_all (x : ℕ) (hx : 64 ≤ x) : R5OK x := by
  rcases lt_or_ge x (10 ^ 16) with h | h
  · exact Box.r5_range x hx h
  · exact R5_tail x h

theorem F2_pos (x : ℕ) (hx : 64 ≤ x) (hM : 8 ≤ nu x - 3 - 2 * Real.log 8) :
    0 < F2 x 8 ∧ 0 < F2 x (nu x - 3 - 2 * Real.log 8) := by
  have hx228 : 228 ≤ x := by
    by_contra h
    push Not at h
    have hx' : (x : ℝ) ≤ 227 := by exact_mod_cast Nat.lt_succ_iff.1 h
    have hs8 := sqrt_ge_eight (by exact_mod_cast hx : (64 : ℝ) ≤ x)
    have hs : √(x : ℝ) ≤ 15.07 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have h1 : 1 / (2 * √(x : ℝ)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h8 : Real.log 8 = 3 * Real.log 2 := log8_eq
    have := Real.log_two_gt_d9
    unfold nu at hM
    linarith
  rcases lt_or_ge x (10 ^ 16) with h | h
  · exact ⟨Box.f2a_range x hx228 h, Box.f2b_range x hx228 h⟩
  · exact ⟨F2a_tail x h, F2b_tail x h⟩

lemma log_3000 : (8 : ℝ) ≤ Real.log 3000 := by
  have := log_ge_of_pow 3000 739 64 (by norm_num) (by decide +kernel)
  norm_num at this ⊢
  linarith

/-- **LLS Theorem 1.1 (1) under GRH.** -/
theorem leastPrimeOutsideSubgroup_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    LeastPrimeOutsideSubgroup := by
  intro q hq H hH
  have : NeZero q := ⟨by omega⟩
  set L := Real.log q with hL_def
  have hL8 : 8 ≤ L := log_3000.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
  have hBeq : LLS.B q = Bf L (q.primeFactors.card : ℝ) (sig q) := by
    unfold LLS.B LLS.A Bf sig; rfl
  set Bq := LLS.B q
  have hB0 : 0 ≤ Bq := le_max_left _ _
  set X := (L + Bq) ^ 2 with hX
  set x := ⌊X⌋₊ with hx_def
  have hX0 : 0 ≤ X := sq_nonneg _
  have hxX : (x : ℝ) ≤ X := Nat.floor_le hX0
  have hXx : X < x + 1 := Nat.lt_floor_add_one X
  have hx64 : 64 ≤ x := by
    have : (64 : ℝ) ≤ X := by rw [hX]; nlinarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hBlt : L + Bf L (q.primeFactors.card : ℝ) (sig q) < √((x : ℝ) + 1) := by
    rw [← hBeq]
    have h0 : 0 ≤ L + Bq := by linarith
    rw [show L + Bq = √X from (Real.sqrt_sq h0).symm]
    exact Real.sqrt_lt_sqrt hX0 hXx
  by_contra hcon
  push Not at hcon
  have hprime : ∀ ℓ ≤ x, ℓ.Prime → ∀ hc : ℓ.Coprime q, ZMod.unitOfCoprime ℓ hc ∈ H := by
    intro ℓ hℓx hℓ hc
    by_contra hmem
    have h1 := hcon ℓ hℓ hc hmem
    have h2 : (ℓ : ℝ) ≤ x := by exact_mod_cast hℓx
    linarith
  obtain ⟨χ, hχ, hval⟩ := exists_char_of_primes_mem H hH x hprime
  have hbud := budget11 hGRH χ hχ x hx64 hval (PcF x) (PcF_le hGRH x hx64) (R5_all x hx64)
  have hpos := phi_pos x hx64 L (sig q) (q.primeFactors.card : ℝ) hL8 (Nat.cast_nonneg _) hBlt
    (F1_pos x hx64) (F2_pos x hx64)
  linarith

end LLS.Thm11
