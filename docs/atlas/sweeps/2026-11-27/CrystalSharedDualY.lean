import Mathlib

/-! Exact finite covers for small odd reduced components. -/

namespace CrystalSharedDualY

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

def factoredProduct (fs : List (ℕ × ℕ)) : ℕ :=
  fs.foldr (fun (p,e) n => p^e*n) 1

def factoredDivisors (fs : List (ℕ × ℕ)) : List ℕ :=
  fs.foldr (fun (p,e) ds =>
    (List.range (e+1)).flatMap fun k => ds.map fun a => p^k*a) [1]

theorem mem_factoredDivisors {fs : List (ℕ × ℕ)} {a : ℕ}
    (hp : ∀ p ∈ fs, p.1.Prime) (hd : a ∣ factoredProduct fs) :
    a ∈ factoredDivisors fs := by
  induction fs generalizing a with
  | nil => simp [factoredProduct, factoredDivisors] at hd ⊢; exact hd
  | cons f fs ih =>
    obtain ⟨p,e⟩ := f
    change a ∣ p^e * factoredProduct fs at hd
    obtain ⟨b,c,hb,hc,rfl⟩ := Nat.dvd_mul.mp hd
    obtain ⟨k,hk,rfl⟩ := Nat.dvd_prime_pow (hp (p,e) (by simp)) |>.mp hb
    have hm := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hc
    change p^k*c ∈ (List.range (e+1)).flatMap (fun j =>
      (factoredDivisors fs).map fun v => p^j*v)
    exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨c,hm,rfl⟩⟩

def discriminant (y d a : ℕ) : ℤ :=
  let Y : ℤ := y
  let D : ℤ := d
  let G : ℤ := (a : ℤ)-1
  ((Y-1)*(D+Y*(Y+1)-2*G*Y^2))^2 - 4*Y^3*(Y-1)*D*(G-1)^2

def firstConstant (y d : ℕ) : ℕ :=
  ((y+1)*(d+(y-1)*y*(1+2*y)))^2

def secondConstant (y d : ℕ) : ℕ :=
  ((y+1)*(d+(y-1)*(y+2)))^2

def excludesRow (y d : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  (factoredDivisors fs).all fun a =>
    let g := (a-1)/y
    let v := discriminant y d (g+1)
    decide (a % (2*y) ≠ y+1 ∨ a < y*(y*y+2)+1 ∨
      ¬ (g+1 ∣ firstConstant y d) ∨ v.natAbs.sqrt^2 ≠ v.natAbs)

theorem nonsquare_of_row {y d g : ℕ} {fs : List (ℕ × ℕ)}
    (hy : 3 ≤ y) (hodd : Odd g)
    (hprod : factoredProduct fs = secondConstant y d)
    (hprime : ∀ p ∈ fs, p.1.Prime) (hcheck : excludesRow y d fs = true)
    (hdvd₁ : g+1 ∣ firstConstant y d) (hdvd₂ : g*y+1 ∣ secondConstant y d)
    (hle : y*y+2 ≤ g) :
    ∀ t : ℤ, discriminant y d (g+1) ≠ t^2 := by
  intro t ht
  have hm := mem_factoredDivisors hprime (hprod ▸ hdvd₂ : g*y+1 ∣ factoredProduct fs)
  have hc := of_decide_eq_true (List.all_eq_true.mp hcheck (g*y+1) hm)
  have hypos : 0 < y := by omega
  have hgfun : (g*y+1-1)/y = g := by simp [Nat.mul_div_cancel _ hypos]
  change (g*y+1) % (2*y) ≠ y+1 ∨ g*y+1 < y*(y*y+2)+1 ∨
    ¬ ((g*y+1-1)/y+1 ∣ firstConstant y d) ∨
      (discriminant y d ((g*y+1-1)/y+1)).natAbs.sqrt^2 ≠
        (discriminant y d ((g*y+1-1)/y+1)).natAbs at hc
  rw [hgfun] at hc
  rcases hc with h | h | h | h
  · apply h
    obtain ⟨k,hk⟩ := hodd
    rw [show g*y+1=(y+1)+(2*y)*k by rw [hk]; ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · exact h.not_ge (Nat.add_le_add_right
      (by simpa only [mul_comm y] using Nat.mul_le_mul_right y hle) 1)
  · exact h hdvd₁
  · apply h
    rw [ht, Int.natAbs_pow, Nat.sqrt_eq']

theorem even_partner (a b : ℕ) (ha : Odd a) (hb : Odd b)
    (hd : (a+1)*(b+1) ∣ (a+b)^2)
    {r : ℤ} (hr : ((b : ℤ)+1)*r = ((a : ℤ)-1)^2) : ∃ j : ℤ, r = 2*j := by
  obtain ⟨q,hq⟩ := hd
  have hq' : ((a : ℤ)+b)^2 = (a+1)*(b+1)*q := by exact_mod_cast hq
  have hV : r = ((q : ℤ)-2)*(a+1)+4-(b+1) := by
    apply mul_left_cancel₀ (show ((b : ℤ)+1) ≠ 0 by positivity)
    linear_combination hr+hq'
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := hb
  have hu' : (a : ℤ) = 2*(u : ℤ)+1 := by exact_mod_cast hu
  have hv' : (b : ℤ) = 2*(v : ℤ)+1 := by exact_mod_cast hv
  refine ⟨((q : ℤ)-2)*(u+1)+2-(v+1), ?_⟩
  rw [hV, hu', hv']
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certified_rows (y d : ℕ) (hy : 3 ≤ y) (hy31 : y ≤ 31) (hyo : y % 2 = 1)
    (hd : 0 < d) (hdhi : d < 2*(y-1)) (hde : d % 2 = 0) :
    ∃ fs : List (ℕ × ℕ), factoredProduct fs = secondConstant y d ∧
      (∀ p ∈ fs, p.1.Prime) ∧ excludesRow y d fs = true := by
  interval_cases y <;> interval_cases d <;> first | omega | skip
  · refine ⟨[(2, 8), (3, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (5, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (29, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (5, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 18)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (5, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 2), (47, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (5, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 2), (7, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 4), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (67, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (5, 2), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (71, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (73, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (7, 4), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (7, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (7, 2), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (47, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 2), (7, 2), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 2), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (7, 2), (97, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (7, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (5, 4), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (7, 2), (101, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 16), (3, 2), (5, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (11, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (61, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (5, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 4), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (127, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 24)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (43, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (5, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (131, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 8), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (7, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (5, 2), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 6), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (157, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (79, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 6), (53, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 4), (5, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (7, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 12)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (163, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 4), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 6), (5, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (83, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (167, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (5, 4), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (191, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 18), (3, 2), (5, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (193, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (5, 2), (97, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 4), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (5, 2), (7, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (197, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 4), (5, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (199, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (5, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 2), (67, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (5, 2), (101, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (7, 2), (29, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (5, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 4), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (5, 2), (103, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (7, 2), (11, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (11, 2), (29, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (11, 2), (233, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (11, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 2), (11, 2), (47, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (11, 2), (59, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (11, 2), (79, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (11, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (11, 2), (239, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (5, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (11, 2), (241, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (11, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 10), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (11, 2), (61, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 2), (7, 4), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (11, 2), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (11, 2), (13, 2), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (11, 2), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (11, 2), (83, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 4), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (277, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (139, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 6), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 2), (5, 2), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (281, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 4), (47, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (283, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (71, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 4), (5, 2), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (11, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (7, 2), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 18), (3, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (17, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (5, 2), (29, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 4), (97, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (73, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (293, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 4), (7, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (5, 2), (59, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 4), (13, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (13, 2), (163, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (13, 2), (109, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (13, 2), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (7, 2), (13, 2), (47, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 2), (11, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (13, 2), (331, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (13, 2), (83, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (13, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (13, 2), (167, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (5, 2), (13, 2), (67, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (7, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (13, 2), (337, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (13, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (13, 2), (113, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (5, 2), (13, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (11, 2), (13, 2), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (13, 2), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (7, 6), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (13, 2), (43, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (13, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (13, 2), (173, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (13, 2), (347, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 6), (7, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (379, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (5, 2), (7, 2), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (7, 2), (127, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (7, 2), (191, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (383, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 20), (3, 2), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (7, 4), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (7, 2), (193, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (7, 2), (43, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (7, 2), (97, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (389, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (5, 2), (7, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (17, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (7, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (7, 2), (131, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (7, 2), (197, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (5, 2), (7, 2), (79, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 4), (7, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (397, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (7, 2), (199, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (7, 4), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (5, 4), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (7, 2), (401, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (7, 2), (67, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (5, 4), (29, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (5, 2), (109, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (19, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 4), (5, 2), (73, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (439, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 2), (5, 4), (11, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 6), (5, 2), (7, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 2), (13, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (443, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 4), (5, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 4), (89, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 2), (223, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (5, 2), (149, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 16), (3, 2), (5, 2), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (449, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 6), (5, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (11, 2), (41, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (5, 2), (113, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 4), (5, 2), (151, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 2), (227, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 4), (7, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 10), (3, 4), (5, 2), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (457, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 6), (3, 2), (5, 2), (229, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 8), (5, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 8), (3, 2), (5, 4), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 4), (3, 2), (5, 2), (461, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 20), (31, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (7, 2), (71, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 2), (83, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (499, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 16), (5, 6)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (167, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (251, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (503, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 18), (3, 4), (7, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (5, 2), (101, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (11, 2), (23, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (13, 4)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 16), (127, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (509, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 2), (5, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (7, 2), (73, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 30)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 6), (19, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (257, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (5, 2), (103, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 16), (3, 2), (43, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (11, 2), (47, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (7, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (3, 2), (173, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 18), (5, 2), (13, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (521, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 14), (3, 4), (29, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 12), (523, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num
  · refine ⟨[(2, 16), (131, 2)], by decide, ?_, by decide +kernel⟩
    simp [List.mem_cons]
    try norm_num

theorem no_y_through31 {g y z : ℕ}
    (hg : 1 < g) (hy : 3 ≤ y) (hy31 : y ≤ 31) (hgo : Odd g)
    (hyo : Odd y) (hzo : Odd z) (ho : g*y ≤ z)
    (hf : (g+1)*(y*z+1) ∣ (g+y*z)^2)
    (hh : (g*y+1)*(z+1) ∣ (g*y+z)^2) : False := by
  obtain ⟨_, hybound⟩ := one_component_bounds hg ho hf
  obtain ⟨r, hr'⟩ := largeComponent_dvd g (y*z) hf
  obtain ⟨s, hs'⟩ := largeComponent_dvd (g*y) z hh
  have hr := hr'.symm
  have hs := hs'.symm
  have hrpos : 0 < r := by
    have hden : 0 < (((y*z : ℕ) : ℤ)+1) := by positivity
    have hn : 0 < ((g : ℤ)-1)^2 := by
      have hg' : (1 : ℤ) < g := by exact_mod_cast hg
      exact pow_pos (sub_pos.mpr hg') _
    by_contra! hle
    exact hn.not_ge (hr ▸ mul_nonpos_of_nonneg_of_nonpos hden.le hle)
  obtain ⟨u,hu⟩ := even_partner g (y*z) hgo (hyo.mul hzo) hf hr
  obtain ⟨v,hv⟩ := even_partner (g*y) z (hgo.mul hyo) hzo hh hs
  push_cast at hr hs
  have ho' : (g : ℤ)*y ≤ z := by exact_mod_cast ho
  have hg' : (2 : ℤ) ≤ g := by exact_mod_cast (show 2 ≤ g by omega)
  have hy' : (1 : ℤ) < y := by exact_mod_cast (show 1 < y by omega)
  let d := s-(y : ℤ)^3*r
  have hd : (0 : ℤ) < d ∧ d < 2*((y : ℤ)-1) := by
    simpa [d] using difference_bounds (g := (g : ℤ)) (x := 1)
      hg' (by decide) hy' (by simpa using ho') hrpos (by simpa using hr)
      (by simpa using hs)
  let D := d.toNat
  have hD : (D : ℤ) = d := Int.toNat_of_nonneg hd.1.le
  have hDb : 0 < D ∧ D < 2*(y-1) := by
    have hy0 : 1 ≤ y := by omega
    have hd' : (0 : ℤ) < D ∧ (D : ℤ) < 2*(((y-1 : ℕ) : ℤ)) := by
      rw [hD, Nat.cast_sub hy0]
      simpa using hd
    exact_mod_cast hd'
  have hDe : D % 2 = 0 := by
    have hf : d = 2*(v-(y : ℤ)^3*u) := by
      dsimp [d]
      rw [hu,hv]
      ring
    omega
  have hyo' : y % 2 = 1 := by obtain ⟨k,hk⟩ := hyo; omega
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hh
  have hp' : ((g : ℤ)+y*z)^2 = (g+1)*(y*z+1)*(p : ℤ) := by exact_mod_cast hp
  have hq' : ((g : ℤ)*y+z)^2 = (g*y+1)*(z+1)*(q : ℤ) := by exact_mod_cast hq
  have hmain := dual_divisor_bounds (x := 1) (z := (z : ℤ)) (y := (y : ℤ))
    (g := (g : ℤ)) (by positivity) (by positivity) (by simpa using hr) (by simpa using hs)
    (by simpa using hp') (by simpa using hq')
  have hdiv₁ : g+1 ∣ firstConstant y D := by
    apply Int.natCast_dvd_natCast.mp
    have hy0 : 1 ≤ y := by omega
    simp only [firstConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_sub hy0, Nat.cast_one, hD]
    simpa [d, add_comm 1 (y : ℤ)] using hmain.1
  have hdiv₂ : g*y+1 ∣ secondConstant y D := by
    apply Int.natCast_dvd_natCast.mp
    have hy0 : 1 ≤ y := by omega
    simp only [secondConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_sub hy0, Nat.cast_one, hD]
    simpa [d, add_comm 1 (y : ℤ)] using hmain.2
  obtain ⟨fs,hprod,hprime,hrow⟩ := certified_rows y D hy hy31 hyo' hDb.1 hDb.2 hDe
  have hdiscr := nonsquare_of_row hy hgo hprod hprime hrow hdiv₁ hdiv₂ (by simpa [pow_two] using hybound)
  have hdelta : ((z : ℤ)+1)*d =
      ((y : ℤ)-1)*(2*(g : ℤ)*y-y-1-(y : ℤ)^2*r) := by
    dsimp [d]
    linear_combination hs - (y : ℤ)^2*hr
  have hquad : d*(((g : ℤ)-1)^2+((y : ℤ)-1)*r) =
      (y : ℤ)*r*((y : ℤ)-1)*(2*(g : ℤ)*y-y-1-(y : ℤ)^2*r) := by
    rw [show ((g : ℤ)-1)^2+((y : ℤ)-1)*r = y*r*(z+1) by linear_combination -hr]
    linear_combination ((y : ℤ)*r)*hdelta
  let A : ℤ := (y : ℤ)^3*((y : ℤ)-1)
  let B : ℤ := ((y : ℤ)-1)*(d+(y : ℤ)*(y+1)-2*(g : ℤ)*y^2)
  apply hdiscr (2*A*r+B)
  dsimp [discriminant,A,B]
  rw [hD]
  linear_combination (-4*(y : ℤ)^3*((y : ℤ)-1))*hquad

#print axioms no_y_through31

end CrystalSharedDualY
