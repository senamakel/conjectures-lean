import Mathlib

/-! A uniform bound on the difference between scaled Vieta partners in
the normalized shared-divisor crystal equations. -/

namespace CrystalSharedPartners

theorem difference_bounds {g x y z r s : ℤ} (hg : 2 ≤ g)
    (hx : 1 ≤ x) (hxy : x < y) (ho : g*y ≤ x*z)
    (hr : 0 < r)
    (hp : (y*z+1)*r = (g*x-1)^2)
    (hq : (x*z+1)*s = (g*y-1)^2) :
    0 < x^3*s-y^3*r ∧ x^3*s-y^3*r < 2*x^2*(y-x) := by
  have hy : 1 ≤ y := by omega
  have hgz : 0 < g*y := by positivity
  have hz : 0 < z := by
    by_contra! hn
    exact hgz.not_ge (ho.trans (mul_nonpos_of_nonneg_of_nonpos (by omega) hn))
  have hrBound : y^2*r < g*x^3 := by
    have h₁ : (g*y)*y*r ≤ (x*z)*y*r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ho (by omega)) hr.le
    have h₂ : ((x : ℤ)*(g*x-1)^2) < g*(g*x^3) := by
      have hgx : 2 ≤ g*x := by nlinarith [mul_nonneg (show 0 ≤ g-2 by omega) (show 0 ≤ x-1 by omega)]
      have hsq : (g*x-1)^2 < (g*x)^2 := by nlinarith only [hgx]
      calc
        x*(g*x-1)^2 < x*(g*x)^2 := mul_lt_mul_of_pos_left hsq (by omega)
        _ = g*(g*x^3) := by ring
    have h₃ : (x*z)*y*r ≤ x*(g*x-1)^2 := by
      calc
        (x*z)*y*r = x*(y*z*r) := by ring
        _ ≤ x*((y*z+1)*r) :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hr]) (by omega)
        _ = x*(g*x-1)^2 := by rw [hp]
    have hm : g*(y^2*r) < g*(g*x^3) := by
      calc
        g*(y^2*r) = (g*y)*y*r := by ring
        _ ≤ (x*z)*y*r := h₁
        _ ≤ x*(g*x-1)^2 := h₃
        _ < g*(g*x^3) := h₂
    exact lt_of_mul_lt_mul_left hm (by omega)
  have id : (x*z+1)*(x^3*s-y^3*r) =
      (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
    linear_combination x^3*hq-y^2*x*hp
  have hCore : 0 < 2*g*x^2*y-x^2-x*y-y^2*r := by
    have hMid : x^2+x*y ≤ g*x^2*y := by
      have hxx : x ≤ x*x := by nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ x-1 by omega)]
      have hyy : x ≤ y := by omega
      have h₁ := mul_le_mul_of_nonneg_left hyy (show 0 ≤ x by omega)
      have h₂ := mul_le_mul_of_nonneg_right hxx (show 0 ≤ y by omega)
      have h₃ : 2*(x*x*y) ≤ g*(x*x*y) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      nlinarith only [h₁,h₂,h₃]
    have hBig : g*x^3 ≤ g*x^2*y :=
      (show g*x^3 = (g*x^2)*x by ring) ▸
        mul_le_mul_of_nonneg_left hxy.le (by positivity)
    linarith only [hrBound, hMid, hBig]
  have hden : 0 < x*z+1 := by positivity
  constructor
  · by_contra! hn
    have hnon := mul_nonpos_of_nonneg_of_nonpos hden.le hn
    rw [id] at hnon
    exact (mul_pos (sub_pos.mpr hxy) hCore).not_ge hnon
  · have hLower : g*y < x*z+1 := by omega
    have hSmall : 2*g*x^2*y-x^2-x*y-y^2*r < 2*x^2*(x*z+1) := by
      have h₁ := mul_lt_mul_of_pos_left hLower (show 0 < 2*x^2 by positivity)
      have h₂ : 0 < x^2+x*y+y^2*r := by positivity
      nlinarith only [h₁,h₂]
    have hProduct :
        (x*z+1)*(x^3*s-y^3*r) < (x*z+1)*(2*x^2*(y-x)) := by
      rw [id]
      calc
        (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) < (y-x)*(2*x^2*(x*z+1)) :=
          mul_lt_mul_of_pos_left hSmall (sub_pos.mpr hxy)
        _ = (x*z+1)*(2*x^2*(y-x)) := by ring
    exact lt_of_mul_lt_mul_left hProduct hden.le

theorem partner_discriminant {g x y z r s : ℤ} (hg : 2 ≤ g)
    (hx : 1 ≤ x) (hxy : x < y) (ho : g*y ≤ x*z) (hr : 0 < r)
    (hp : (y*z+1)*r = (g*x-1)^2)
    (hq : (x*z+1)*s = (g*y-1)^2) :
    let d := x^3*s-y^3*r
    d < x*y*(y-x) ∧
      (d*(g*x-1)-y^2*r*(y-x))^2 = x^2*(y-x)*r*s*(x*y*(y-x)-d) := by
  let d := x^3*s-y^3*r
  change d < x*y*(y-x) ∧ _
  have hgypos : 0 < g*y := mul_pos (by omega) (by omega)
  have hden : 0 < x*z+1 := by omega
  have hy : 0 < y := by omega
  have hgx : 1 < g*x := by
    have h := mul_le_mul_of_nonneg_left hx (show 0 ≤ g by omega)
    simpa using (show 1 < g*1 from by omega).trans_le h
  have hgy : 1 < g*y :=
    hgx.trans (mul_lt_mul_of_pos_left hxy (by omega))
  have hs : 0 < s := by
    by_contra! hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hden.le hn
    rw [hq] at hm
    exact (pow_pos (sub_pos.mpr hgy) 2).not_ge hm
  have hd : (x*z+1)*d = (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
    dsimp [d]
    linear_combination x^3*hq-y^2*x*hp
  have hquad : d*(x*(g*x-1)^2+(y-x)*r) =
      y*r*(y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
    rw [show x*(g*x-1)^2+(y-x)*r = y*r*(x*z+1) by linear_combination -x*hp]
    linear_combination (y*r)*hd
  have hsquare :
      (d*(g*x-1)-y^2*r*(y-x))^2 = x^2*(y-x)*r*s*(x*y*(y-x)-d) := by
    apply mul_left_cancel₀ (show x ≠ 0 by omega)
    dsimp [d] at hquad ⊢
    linear_combination (x^3*s-y^3*r)*hquad
  refine ⟨?_, hsquare⟩
  have hc : 0 < x^2*(y-x)*r*s := by positivity
  have hle : d ≤ x*y*(y-x) := by
    by_contra! hn
    have hneg := mul_neg_of_pos_of_neg hc (sub_neg.mpr hn)
    rw [← hsquare] at hneg
    exact (sq_nonneg _).not_gt hneg
  refine lt_of_le_of_ne hle ?_
  intro he
  have hzero : (d*(g*x-1)-y^2*r*(y-x))^2 = 0 := by
    rw [hsquare, he, sub_self, mul_zero]
  have hlin : d*(g*x-1)-y^2*r*(y-x) = 0 := by
    simpa only [pow_two, mul_eq_zero, or_self] using hzero
  rw [he] at hlin
  have hfactor : (y*(y-x))*(x*(g*x-1)-y*r) = 0 := by
    linear_combination hlin
  have hcancel : x*(g*x-1) = y*r := by
    have hpos : 0 < y*(y-x) := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hpos.ne')
  have hfactor' : (g*x-1)*(y*(g*x-1)-x*(y*z+1)) = 0 := by
    linear_combination -y*hp-(y*z+1)*hcancel
  have hlin' : y*(g*x-1)-x*(y*z+1) = 0 :=
    (mul_eq_zero.mp hfactor').resolve_left (sub_pos.mpr hgx).ne'
  have hgz : g < z := by
    apply lt_of_mul_lt_mul_left (a := x) _ (by omega)
    calc
      x*g = g*x := by ring
      _ < g*y := mul_lt_mul_of_pos_left hxy (by omega)
      _ ≤ x*z := ho
  have hpos : 0 < x*y*(z-g) := by positivity
  nlinarith only [hlin', hpos, hx, hy]

theorem component_dvd_bound {g x y z r s : ℤ}
    (hp : (y*z+1)*r = (g*x-1)^2)
    (hq : (x*z+1)*s = (g*y-1)^2)
    (hu2 : g*x+1 ∣ (y*z-1)^2) :
    let d := x^3*s-y^3*r
    let C := (x+y)*(d+(y-x)*y*(x+2*y))
    g*x+1 ∣ 16*C^2 := by
  let A := g*x+1
  let d := x^3*s-y^3*r
  let C := (x+y)*(d+(y-x)*y*(x+2*y))
  let u := y*z-1
  let K := x*d-(y-x)*y^3
  change A ∣ 16*C^2
  change A ∣ u^2 at hu2
  have hp' : A ∣ (u+2)*r-4 := ⟨g*x-3, by
    dsimp [A,u]
    linear_combination hp⟩
  have hr' : A ∣ 4*r+4*u-8 := by
    rw [show 4*r+4*u-8 = u^2*r-(u-2)*((u+2)*r-4) by ring]
    exact dvd_sub (dvd_mul_of_dvd_left hu2 r) (dvd_mul_of_dvd_right hp' (u-2))
  have hd : (x*z+1)*d = (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
    dsimp [d]
    linear_combination x^3*hq-y^2*x*hp
  have hE : A ∣ d*(x*u+x+y)+(y-x)*y*(x^2+3*x*y+y^2*r) :=
    ⟨2*x*y^2*(y-x), by
      dsimp [A,u]
      linear_combination y*hd⟩
  have hLin : A ∣ 4*(C+K*u) := by
    rw [show 4*(C+K*u) =
        4*(d*(x*u+x+y)+(y-x)*y*(x^2+3*x*y+y^2*r))-
          ((y-x)*y^3)*(4*r+4*u-8) by dsimp [C,K]; ring]
    exact dvd_sub (dvd_mul_of_dvd_right hE 4)
      (dvd_mul_of_dvd_right hr' ((y-x)*y^3))
  rw [show 16*C^2 = (4*(C+K*u))*(4*(C-K*u))+(16*K^2)*u^2 by ring]
  exact dvd_add (dvd_mul_of_dvd_left hLin (4*(C-K*u)))
    (dvd_mul_of_dvd_right hu2 (16*K^2))

#print axioms difference_bounds
#print axioms partner_discriminant
#print axioms component_dvd_bound

end CrystalSharedPartners
