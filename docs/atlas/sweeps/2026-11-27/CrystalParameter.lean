import FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents

/-!
# Crystal uniqueness at a fixed recurrence parameter

The total product and parameter from Proposition 1 of arXiv:1601.03081
determine the unordered crystal components. The general conjecture
still requires ruling out collisions between distinct parameters.
-/

open Finset

theorem crystal_same_parameter {n a b c d w : ℕ}
    (hn₁ : n = a * b) (hn₂ : n = c * d)
    (h₁ : (a + b)^2 = w * ((a + 1) * (b + 1)))
    (h₂ : (c + d)^2 = w * ((c + 1) * (d + 1))) :
    ({a, b} : Finset ℕ) = {c, d} := by
  have hn₁' : (n : ℤ) = a * b := by exact_mod_cast hn₁
  have hn₂' : (n : ℤ) = c * d := by exact_mod_cast hn₂
  have h₁' : ((a : ℤ) + b)^2 = w * ((n : ℤ) + (a + b) + 1) := by
    have h : ((a : ℤ) + b)^2 = w * ((a + 1) * (b + 1)) := by exact_mod_cast h₁
    rw [hn₁']
    convert h using 1; ring
  have h₂' : ((c : ℤ) + d)^2 = w * ((n : ℤ) + (c + d) + 1) := by
    have h : ((c : ℤ) + d)^2 = w * ((c + 1) * (d + 1)) := by exact_mod_cast h₂
    rw [hn₂']
    convert h using 1; ring
  let x : ℤ := a + b
  let y : ℤ := c + d
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  change x^2 = w * ((n : ℤ) + x + 1) at h₁'
  change y^2 = w * ((n : ℤ) + y + 1) at h₂'
  have hz : (x - y) * ((x + y) * ((n : ℤ) + 1) + x * y) = 0 := by
    calc
      _ = x^2 * ((n : ℤ) + y + 1) - y^2 * ((n : ℤ) + x + 1) := by ring
      _ = 0 := by rw [h₁', h₂']; ring
  have hxy : x = y := by
    by_contra h
    have hs : 0 < x + y := by omega
    have hh : 0 < (x + y) * ((n : ℤ) + 1) + x * y := by positivity
    exact (mul_ne_zero (sub_ne_zero.mpr h) hh.ne') hz
  have hsum : (a : ℤ) + b = c + d := hxy
  have hprod : (a : ℤ) * b = c * d := hn₁'.symm.trans hn₂'
  have hroot : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    calc
      _ = (a : ℤ)^2 - a * (c + d) + c * d := by ring
      _ = 0 := by rw [← hsum, ← hprod]; ring
  rcases mul_eq_zero.mp hroot with h | h
  · have hac : a = c := by exact_mod_cast sub_eq_zero.mp h
    subst c
    have hbd : b = d := by omega
    simp [hbd]
  · have had : a = d := by exact_mod_cast sub_eq_zero.mp h
    subst d
    have hbc : b = c := by omega
    simp [hbc, Finset.pair_comm]

#print axioms crystal_same_parameter

open Arxiv.«1601.03081»

theorem crystals_eq_of_same_parameter {n a b c d : ℕ}
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d)
    (hw : (a + b)^2 / ((a + 1) * (b + 1)) =
      (c + d)^2 / ((c + 1) * (d + 1))) :
    ({a, b} : Finset ℕ) = {c, d} := by
  obtain ⟨_, _, _, hnab, hdab⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n a b).mp hab
  obtain ⟨_, _, _, hncd, hdcd⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n c d).mp hcd
  refine crystal_same_parameter hnab hncd (Nat.div_mul_cancel hdab).symm ?_
  rw [hw, Nat.div_mul_cancel hdcd]

#print axioms crystals_eq_of_same_parameter
