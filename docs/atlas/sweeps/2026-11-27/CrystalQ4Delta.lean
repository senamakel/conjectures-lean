import Mathlib

/-! Kernel certificates for bounded partner differences in the quotient-four branch. -/

namespace CrystalQ4Delta

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

def firstConstant (y d : ℕ) : ℕ :=
  ((y+1)*(d+(y-1)*y*(1+2*y)))^2

def secondConstant (y d : ℕ) : ℕ :=
  ((y+1)*(d+(y-1)*(y+2)))^2

def norm (d : ℕ) : ℕ := (d-3)^2-8

def noCandidate (y d : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  (factoredDivisors fs).all fun a =>
    decide (a % (2*y) ≠ y+1 ∨ a < y*(y*y+2)+1 ∨
      ¬ ((a-1)/y+1 ∣ firstConstant y d))

def checkedRows (d : ℕ) (fs : List (ℕ × ℕ))
    (table : List (ℕ × List (ℕ × ℕ))) : Bool :=
  (factoredDivisors fs).all fun y =>
    if y < 33 then true else
      let row := ((table.find? fun q => q.1 == y).getD (y,[])).2
      decide (factoredProduct row = secondConstant y d) &&
        noCandidate y d row

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate (d : ℕ) (h₁ : 10 ≤ d) (h₂ : d ≤ 64) (he : d % 2 = 0) :
    ∃ fs : List (ℕ × ℕ), ∃ table : List (ℕ × List (ℕ × ℕ)),
      factoredProduct fs = norm d ∧ (∀ p ∈ fs, p.1.Prime) ∧
        (∀ row ∈ table, ∀ p ∈ row.2, p.1.Prime) ∧ checkedRows d fs table = true := by
  interval_cases d <;> first | omega | skip
  · refine ⟨[(41,1)], [(41, [(2,4), (3,2), (5,2), (7,2), (173,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(73,1)], [(73, [(2,6), (3,2), (11,2), (37,2), (41,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(113,1)], [(113, [(2,4), (3,4), (7,2), (19,2), (307,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (23,1)], [(161, [(2,10), (3,8), (7,2), (233,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (31,1)], [(217, [(2,4), (3,4), (11,2), (109,2), (239,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(281,1)], [(281, [(2,6), (3,4), (5,2), (47,2), (1321,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(353,1)], [(353, [(2,4), (3,2), (11,2), (13,2), (19,2), (23,2), (59,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(433,1)], [(433, [(2,8), (3,2), (7,2), (31,2), (41,2), (191,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(521,1)], [(521, [(2,4), (3,6), (11,2), (13,2), (29,2), (317,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(617,1)], [(617, [(2,6), (3,2), (7,2), (103,2), (13619,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (103,1)], [(103, [(2,10), (3,2), (5,2), (13,2), (179,2)]), (721, [(2,4), (3,2), (5,2), (7,2), (19,4), (37,2), (67,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,2), (17,1)], [(49, [(2,10), (5,6), (31,2)]), (119, [(2,8), (3,8), (5,4), (53,2)]), (833, [(2,12), (3,4), (139,2), (7237,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(953,1)], [(953, [(2,4), (3,4), (11,4), (13,2), (17,4), (53,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(23,1), (47,1)], [(47, [(2,10), (3,2), (5,2), (229,2)]), (1081, [(2,6), (3,4), (541,2), (32491,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(1217,1)], [(1217, [(2,4), (3,4), (7,2), (19,2), (29,2), (13003,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(1361,1)], [(1361, [(2,8), (3,2), (5,2), (11,4), (227,2), (383,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(17,1), (89,1)], [(89, [(2,4), (3,4), (5,6), (7,2), (23,2)]), (1513, [(2,4), (3,2), (7,2), (757,2), (54541,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (239,1)], [(239, [(2,10), (3,8), (5,2), (1063,2)]), (1673, [(2,6), (3,8), (7,4), (11,2), (31,2), (433,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (263,1)], [(263, [(2,10), (3,2), (11,4), (1579,2)]), (1841, [(2,4), (3,2), (23,2), (307,2), (73721,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(2017,1)], [(2017, [(2,10), (3,2), (11,2), (13,2), (593,2), (1009,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(31,1), (71,1)], [(71, [(2,12), (3,6), (5,2), (43,2)]), (2201, [(2,4), (3,4), (5,4), (79,2), (367,2), (409,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(2393,1)], [(2393, [(2,6), (3,4), (7,2), (13,2), (19,2), (29,4), (131,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(2593,1)], [(2593, [(2,4), (3,6), (1297,2), (124561,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(2801,1)], [(2801, [(2,8), (3,4), (7,2), (11,2), (31,2), (137,2), (467,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (431,1)], [(431, [(2,14), (3,6), (31,2), (751,2)]), (3017, [(2,4), (3,2), (7,2), (29,2), (41,2), (503,2), (547,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(7,1), (463,1)], [(463, [(2,10), (3,2), (5,2), (13,2), (19,2), (29,4)]), (3241, [(2,6), (3,2), (5,2), (13,2), (19,2), (709,2), (1621,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(23,1), (151,1)], [(151, [(2,10), (11,2), (19,2), (523,2)]), (3473, [(2,4), (3,6), (11,2), (31,2), (193,2), (5897,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine ⟨[(47,1), (79,1)], [(47, [(2,10), (3,2), (19,2), (61,2)]), (79, [(2,10), (5,2), (3191,2)]), (3713, [(2,14), (3,2), (619,2), (215471,2)])], by decide, ?_, ?_, by decide +kernel⟩
    · simp [List.mem_cons]
      try norm_num
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl | rfl
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> norm_num
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem no_delta_through64 {g y d : ℕ}
    (hy : 33 ≤ y) (hd : 10 ≤ d) (hd64 : d ≤ 64) (he : d % 2 = 0)
    (hgo : Odd g) (hgb : y*y+2 ≤ g)
    (hn : (y : ℤ) ∣ ((d : ℤ)-3)^2-8)
    (hx : g+1 ∣ firstConstant y d) (hz : g*y+1 ∣ secondConstant y d) :
    False := by
  have hn' : y ∣ norm d := by
    apply Int.natCast_dvd_natCast.mp
    have hd3 : 3 ≤ d := by omega
    have hd8 : 8 ≤ (d-3)^2 := by
      have ht := Nat.pow_le_pow_left (show 7 ≤ d-3 by omega) 2
      omega
    simpa only [norm, Nat.cast_sub hd8, Nat.cast_pow, Nat.cast_sub hd3,
      Nat.cast_ofNat] using hn
  obtain ⟨fs,table,hfs,hprime,htable,hcheck⟩ := certificate d hd hd64 he
  have hyMem := mem_factoredDivisors hprime (hfs ▸ hn' : y ∣ factoredProduct fs)
  have hyCheck := List.all_eq_true.mp hcheck y hyMem
  let row := ((table.find? fun q => q.1 == y).getD (y,[])).2
  change (if y < 33 then true else
    decide (factoredProduct row = secondConstant y d) &&
      noCandidate y d row) = true at hyCheck
  simp only [if_neg (not_lt.mpr hy), Bool.and_eq_true] at hyCheck
  obtain ⟨hprod,hrow⟩ := hyCheck
  have hrowPrime : ∀ p ∈ row, p.1.Prime := by
    cases heq : table.find? (fun q => q.1 == y) with
    | none => simp [row,heq]
    | some a => simpa [row,heq] using htable a (List.mem_of_find?_eq_some heq)
  have haMem := mem_factoredDivisors hrowPrime
    ((of_decide_eq_true hprod) ▸ hz : g*y+1 ∣ factoredProduct row)
  have hc := of_decide_eq_true (List.all_eq_true.mp hrow (g*y+1) haMem)
  have hypos : 0 < y := by omega
  have hgfun : (g*y+1-1)/y = g := by simp [Nat.mul_div_cancel _ hypos]
  change (g*y+1) % (2*y) ≠ y+1 ∨ g*y+1 < y*(y*y+2)+1 ∨
    ¬ ((g*y+1-1)/y+1 ∣ firstConstant y d) at hc
  rw [hgfun] at hc
  rcases hc with h | h | h
  · apply h
    obtain ⟨k,hk⟩ := hgo
    rw [show g*y+1=(y+1)+(2*y)*k by rw [hk]; ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · exact h.not_ge (Nat.add_le_add_right
      (by simpa only [mul_comm y] using Nat.mul_le_mul_right y hgb) 1)
  · exact h hx

#print axioms no_delta_through64

end CrystalQ4Delta
