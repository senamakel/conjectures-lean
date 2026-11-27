import Mathlib

/-! Bounds for the shared-divisor normalization with fixed gcd and smaller
coprime component. -/

namespace CrystalSharedBounds

theorem largeComponent_dvd (a b : ℕ)
    (h : (a+1)*(b+1) ∣ (a+b)^2) : (b : ℤ)+1 ∣ ((a : ℤ)-1)^2 := by
  have hs : b+1 ∣ (a+b)^2 := (dvd_mul_left (b+1) (a+1)).trans h
  have hs' : (b : ℤ)+1 ∣ ((a : ℤ)+b)^2 := by exact_mod_cast hs
  have hrewrite : ((a : ℤ)-1)^2 =
      ((a : ℤ)+b)^2 - ((b : ℤ)+1)*(2*(a : ℤ)+b-1) := by ring
  rw [hrewrite]
  exact dvd_sub hs' (dvd_mul_right _ _)

theorem normalized_bounds {g x y z : ℕ}
    (hg : 1 < g) (hx : 0 < x) (horder : g*y ≤ x*z)
    (hdiv : (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2) :
    y*z ≤ g*x*(g*x-2) ∧ y^2 ≤ x^2*(g*x-2) := by
  have hgx : 2 ≤ g*x := by
    have := Nat.mul_le_mul_left g (show 1 ≤ x by omega)
    omega
  obtain ⟨k,hk⟩ := largeComponent_dvd (g*x) (y*z) hdiv
  push_cast at hk
  have hdpos : (0 : ℤ) < (y : ℤ)*z+1 := by positivity
  have hnpos : (0 : ℤ) < (((g : ℤ)*x)-1)^2 := by
    have hgx' : (2 : ℤ) ≤ (g : ℤ)*x := by exact_mod_cast hgx
    exact pow_pos (by omega) _
  have hkpos : 0 < k := by
    by_contra he
    have hm := mul_nonpos_of_nonneg_of_nonpos hdpos.le (le_of_not_gt he)
    rw [← hk] at hm
    exact hnpos.not_ge hm
  have hle : (y : ℤ)*z+1 ≤ (((g : ℤ)*x)-1)^2 := by
    rw [hk]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ k by omega) hdpos.le)
  have hu : y*z ≤ g*x*(g*x-2) := by
    have hcast : ((g*x-2 : ℕ) : ℤ) = (g : ℤ)*x-2 := by
      rw [Nat.cast_sub hgx]
      push_cast
      rfl
    exact_mod_cast (show (y : ℤ)*z ≤ ((g : ℤ)*x)*((g*x-2 : ℕ) : ℤ) by
      rw [hcast]
      linarith only [hle,
        show ((g : ℤ)*x-1)^2-1 = ((g : ℤ)*x)*((g : ℤ)*x-2) by ring])
  refine ⟨hu, ?_⟩
  have ht : g*y^2 ≤ g*(x^2*(g*x-2)) := by
    calc
      g*y^2 = (g*y)*y := by ring
      _ ≤ (x*z)*y := Nat.mul_le_mul_right y horder
      _ = x*(y*z) := by ring
      _ ≤ x*(g*x*(g*x-2)) := Nat.mul_le_mul_left x hu
      _ = g*(x^2*(g*x-2)) := by ring
  exact Nat.le_of_mul_le_mul_left ht (by omega)

theorem one_component_bounds {g y z : ℕ}
    (hg : 1 < g) (horder : g*y ≤ z)
    (hdiv : (g+1)*(y*z+1) ∣ (g+y*z)^2) :
    y*z ≤ g*(g-2) ∧ y^2+2 ≤ g := by
  obtain ⟨hz,hy⟩ := normalized_bounds hg (show 0 < 1 by decide)
    (by simpa using horder) (by simpa using hdiv)
  simp at hz hy
  exact ⟨hz, by omega⟩

#print axioms normalized_bounds
#print axioms one_component_bounds

end CrystalSharedBounds
