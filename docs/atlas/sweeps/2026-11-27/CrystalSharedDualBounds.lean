import Mathlib

/-! Both complete crystal quotients constrain the common divisor in the
shared-divisor normalization. -/

namespace CrystalSharedDualBounds

theorem partner_congruence {a b q r : ℤ} (hb : b+1 ≠ 0)
    (hq : (a+b)^2 = (a+1)*(b+1)*q)
    (hr : (b+1)*r = (a-1)^2) :
    a+1 ∣ r+b-3 := by
  refine ⟨q-2, ?_⟩
  apply mul_left_cancel₀ hb
  linear_combination hr+hq

theorem shifted_square_dvd {a b q : ℤ}
    (hq : (a+b)^2 = (a+1)*(b+1)*q) :
    a+1 ∣ (b-1)^2 := by
  refine ⟨(b+1)*q-(a+2*b-1), ?_⟩
  linear_combination hq

theorem component_dvd_square {g x y z r s p : ℤ}
    (hz : y*z+1 ≠ 0)
    (hp : (y*z+1)*r = (g*x-1)^2)
    (hq : (x*z+1)*s = (g*y-1)^2)
    (hquot : (g*x+y*z)^2 = (g*x+1)*(y*z+1)*p) :
    let d := x^3*s-y^3*r
    g*x+1 ∣ ((x+y)*(d+(y-x)*y*(x+2*y)))^2 := by
  let A := g*x+1
  let d := x^3*s-y^3*r
  let C := (x+y)*(d+(y-x)*y*(x+2*y))
  let u := y*z-1
  let K := x*d-(y-x)*y^3
  change A ∣ C^2
  have hu : A ∣ u^2 := shifted_square_dvd hquot
  have hr : A ∣ r+u-2 := by
    rw [show r+u-2 = r+y*z-3 by dsimp [u]; ring]
    exact partner_congruence hz hquot hp
  have hd : (x*z+1)*d = (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
    dsimp [d]
    linear_combination x^3*hq-y^2*x*hp
  have hE : A ∣ d*(x*u+x+y)+(y-x)*y*(x^2+3*x*y+y^2*r) :=
    ⟨2*x*y^2*(y-x), by
      dsimp [A,u]
      linear_combination y*hd⟩
  have hLin : A ∣ C+K*u := by
    rw [show C+K*u =
        d*(x*u+x+y)+(y-x)*y*(x^2+3*x*y+y^2*r)-
          ((y-x)*y^3)*(r+u-2) by dsimp [C,K]; ring]
    exact dvd_sub hE (dvd_mul_of_dvd_right hr ((y-x)*y^3))
  rw [show C^2 = (C+K*u)*(C-K*u)+K^2*u^2 by ring]
  exact dvd_add (dvd_mul_of_dvd_left hLin (C-K*u))
    (dvd_mul_of_dvd_right hu (K^2))

theorem dual_divisor_bounds {g x y z r s p q : ℤ}
    (hxz : x*z+1 ≠ 0) (hyz : y*z+1 ≠ 0)
    (hr : (y*z+1)*r = (g*x-1)^2)
    (hs : (x*z+1)*s = (g*y-1)^2)
    (hp : (g*x+y*z)^2 = (g*x+1)*(y*z+1)*p)
    (hq : (g*y+x*z)^2 = (g*y+1)*(x*z+1)*q) :
    let d := x^3*s-y^3*r
    (g*x+1 ∣ ((x+y)*(d+(y-x)*y*(x+2*y)))^2) ∧
      (g*y+1 ∣ ((x+y)*(d+(y-x)*x*(y+2*x)))^2) := by
  dsimp only
  refine ⟨component_dvd_square hyz hr hs hp, ?_⟩
  have he :
      ((x+y)*(x^3*s-y^3*r+(y-x)*x*(y+2*x)))^2 =
      ((y+x)*(y^3*r-x^3*s+(x-y)*x*(y+2*x)))^2 := by ring
  rw [he]
  exact component_dvd_square hxz hs hr hq

theorem denominator_offset_dvd (g x y : ℤ) {d : ℤ}
    (hx : d ∣ g*x+1) (hy : d ∣ g*y+1) : d ∣ y-x := by
  rw [show y-x = y*(g*x+1)-x*(g*y+1) by ring]
  exact dvd_sub (dvd_mul_of_dvd_right hx y) (dvd_mul_of_dvd_right hy x)

#print axioms dual_divisor_bounds
#print axioms denominator_offset_dvd

end CrystalSharedDualBounds
