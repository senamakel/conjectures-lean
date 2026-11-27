/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.Basic
import OeisA245211.Dominance
import OeisA245211.Families

/-!
# OEIS A245211: Multiplicativity, General Parity Obstruction, and Sharpened Dominance

This module develops the multiplicative structure of `tau` and `fullMoment`,
establishes the odd prime-power parity congruence, proves the General Parity
Obstruction Theorem for fixed points of OEIS A245211, and proves the sharpened
dominance bound `e * tau m < p` for exact prime-power factorizations `n = p^e * m`.
-/

namespace OeisA245211

/-! ## Multiplicativity of `sumDiv` on Coprime Arguments -/

section Multiplicativity

/-- Product decomposition for divisors of `u * v` when `Nat.Coprime u v`. -/
theorem dvd_mul_coprime_unique {u v d : Nat} (hcop : Nat.Coprime u v)
    (hu : 0 < u) (hv : 0 < v) (_hd1 : 1 ≤ d) (hdvd : d ∣ u * v) :
    ∃ a b : Nat, 1 ≤ a ∧ a ≤ u ∧ a ∣ u ∧ 1 ≤ b ∧ b ≤ v ∧ b ∣ v ∧ d = a * b := by
  refine ⟨Nat.gcd d u, Nat.gcd d v, ?_, ?_, Nat.gcd_dvd_right d u, ?_, ?_, Nat.gcd_dvd_right d v, ?_⟩
  · exact Nat.gcd_pos_of_pos_right d hu
  · exact Nat.le_of_dvd hu (Nat.gcd_dvd_right d u)
  · exact Nat.gcd_pos_of_pos_right d hv
  · exact Nat.le_of_dvd hv (Nat.gcd_dvd_right d v)
  · have hcop_ab : Nat.Coprime (Nat.gcd d u) (Nat.gcd d v) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right d u)).coprime_dvd_right (Nat.gcd_dvd_right d v)
    have h1 : Nat.gcd d u ∣ d := Nat.gcd_dvd_left d u
    have h2 : Nat.gcd d v ∣ d := Nat.gcd_dvd_left d v
    have hmul_dvd : Nat.gcd d u * Nat.gcd d v ∣ d := hcop_ab.mul_dvd_of_dvd_of_dvd h1 h2
    obtain ⟨q, hq⟩ := h1
    have hu_pos : 0 < Nat.gcd d u := Nat.gcd_pos_of_pos_right d hu
    obtain ⟨u', hu'⟩ := Nat.gcd_dvd_right d u
    have hcop_qu' : Nat.Coprime q u' := by
      have hgcd_eq : Nat.gcd (Nat.gcd d u * q) (Nat.gcd d u * u') = Nat.gcd d u := by
        rw [← hq, ← hu']
      rw [Nat.gcd_mul_left] at hgcd_eq
      have hmul1 : Nat.gcd d u * Nat.gcd q u' = Nat.gcd d u * 1 := by
        simpa [Nat.mul_one] using hgcd_eq
      exact Nat.eq_of_mul_eq_mul_left hu_pos hmul1
    have hd_dvd : Nat.gcd d u * q ∣ (Nat.gcd d u * u') * v := by
      rw [← hq, ← hu']
      exact hdvd
    have hq_dvd_u'v : q ∣ u' * v := by
      rw [Nat.mul_assoc] at hd_dvd
      exact Nat.dvd_of_mul_dvd_mul_left hu_pos hd_dvd
    have hq_dvd_v : q ∣ v := hcop_qu'.dvd_of_dvd_mul_left hq_dvd_u'v
    have hq_dvd_d : q ∣ d := ⟨Nat.gcd d u, by rw [Nat.mul_comm]; exact hq⟩
    have hq_dvd_gcdv : q ∣ Nat.gcd d v := Nat.dvd_gcd hq_dvd_d hq_dvd_v
    have hd_dvd_mul : d ∣ Nat.gcd d u * Nat.gcd d v := by
      calc d = Nat.gcd d u * q := hq
        _ ∣ Nat.gcd d u * Nat.gcd d v := Nat.mul_dvd_mul_left (Nat.gcd d u) hq_dvd_gcdv
    exact Nat.dvd_antisymm hd_dvd_mul hmul_dvd

theorem dvd_mul_coprime_pair_unique {u v a b a' b' : Nat} (hcop : Nat.Coprime u v)
    (ha : a ∣ u) (hb : b ∣ v) (ha' : a' ∣ u) (hb' : b' ∣ v)
    (heq : a * b = a' * b') : a = a' ∧ b = b' := by
  have hcop_ab' : Nat.Coprime a b' :=
    (hcop.coprime_dvd_left ha).coprime_dvd_right hb'
  have hcop_a'b : Nat.Coprime a' b :=
    (hcop.coprime_dvd_left ha').coprime_dvd_right hb
  have ha_dvd : a ∣ a' :=
    hcop_ab'.dvd_of_dvd_mul_right ⟨b, heq.symm⟩
  have ha'_dvd : a' ∣ a :=
    hcop_a'b.dvd_of_dvd_mul_right ⟨b', heq⟩
  have h_a : a = a' := Nat.dvd_antisymm ha_dvd ha'_dvd
  have hcop_ba' : Nat.Coprime b a' := hcop_a'b.symm
  have hcop_b'a : Nat.Coprime b' a := hcop_ab'.symm
  have hb_dvd : b ∣ b' :=
    hcop_ba'.dvd_of_dvd_mul_left ⟨a, by grind⟩
  have hb'_dvd : b' ∣ b :=
    hcop_b'a.dvd_of_dvd_mul_left ⟨a', by grind⟩
  exact ⟨h_a, Nat.dvd_antisymm hb_dvd hb'_dvd⟩

/-- `sumList` over a `List.flatMap` equals the nested `sumList`. -/
theorem sumList_flatMap {α : Type} (xs : List α) (g : α → List Nat) (w : Nat → Nat) :
    sumList (xs.flatMap g) w =
      sumList (xs.map (fun x => sumList (g x) w)) id := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_cons, sumList_append, sumList, id]
    rw [ih]

/-- `sumList (ys.map (fun b => a * b)) w` when `w` is multiplicative on `a` and elements of `ys`. -/
theorem sumList_map_mul (a : Nat) (ys : List Nat) (w : Nat → Nat)
    (hw : ∀ b ∈ ys, w (a * b) = w a * w b) :
    sumList (ys.map (fun b => a * b)) w = w a * sumList ys w := by
  induction ys with
  | nil => simp [sumList]
  | cons y ys ih =>
    simp only [List.map_cons, sumList]
    have hy : w (a * y) = w a * w y := hw y List.mem_cons_self
    have hys : sumList (ys.map (fun b => a * b)) w = w a * sumList ys w :=
      ih (fun b hb => hw b (List.mem_cons_of_mem y hb))
    rw [hy, hys, Nat.mul_add]

theorem sumList_cons (x : Nat) (xs : List Nat) (w : Nat → Nat) :
    sumList (x :: xs) w = w x + sumList xs w := rfl

theorem sumList_erase {x : Nat} {xs : List Nat} (hx : x ∈ xs) (w : Nat → Nat) :
    sumList xs w = w x + sumList (xs.erase x) w := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    by_cases hxy : y = x
    · subst hxy
      simp [List.erase_cons_head, sumList]
    · have hne : ¬ ((y == x) = true) := by simp [hxy]
      rw [List.erase_cons_tail hne]
      have hx' : x ∈ ys := by
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact absurd rfl hxy
        · exact hmem
      simp only [sumList]
      rw [ih hx']
      omega

theorem sumList_eq_of_nodup_equiv {xs ys : List Nat} (hx : xs.Nodup) (hy : ys.Nodup)
    (hequiv : ∀ d, d ∈ xs ↔ d ∈ ys) (w : Nat → Nat) :
    sumList xs w = sumList ys w := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y _ =>
      have := (hequiv y).mpr List.mem_cons_self
      contradiction
  | cons x xs ih =>
    have hx_mem_ys : x ∈ ys := (hequiv x).mp List.mem_cons_self
    have hx_not_xs : x ∉ xs := (List.nodup_cons.mp hx).1
    have hx_nodup : xs.Nodup := (List.nodup_cons.mp hx).2
    have hys_erase_nodup : (ys.erase x).Nodup := hy.erase x
    have hequiv' : ∀ d, d ∈ xs ↔ d ∈ ys.erase x := by
      intro d
      constructor
      · intro hd
        have hd_ne : d ≠ x := fun h => hx_not_xs (h ▸ hd)
        exact (List.mem_erase_of_ne hd_ne).mpr ((hequiv d).mp (List.mem_cons_of_mem x hd))
      · intro hd
        have hd_ne : d ≠ x := by
          intro h
          subst h
          exact hy.not_mem_erase hd
        have hd_ys : d ∈ ys := List.mem_of_mem_erase hd
        rcases List.mem_cons.mp ((hequiv d).mpr hd_ys) with rfl | hd_xs
        · exact absurd rfl hd_ne
        · exact hd_xs
    rw [sumList_cons, sumList_erase hx_mem_ys w, ih hx_nodup hys_erase_nodup hequiv']

theorem sumList_const_one (xs : List Nat) :
    sumList xs (fun _ => 1) = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp only [sumList, List.length_cons, ih]
    omega

/-- Length of a `Nodup` list is invariant under membership equivalence. -/
theorem length_eq_of_nodup_equiv {xs ys : List Nat} (hx : xs.Nodup) (hy : ys.Nodup)
    (hequiv : ∀ d, d ∈ xs ↔ d ∈ ys) :
    xs.length = ys.length := by
  rw [← sumList_const_one xs, ← sumList_const_one ys]
  exact sumList_eq_of_nodup_equiv hx hy hequiv (fun _ => 1)

/-- Helper: `Nodup` for `flatMap` over pairwise disjoint mapped lists. -/
theorem nodup_flatMap_of_disjoint {α : Type} {xs : List α} {g : α → List Nat}
    (hxs : xs.Nodup)
    (hg_nodup : ∀ a ∈ xs, (g a).Nodup)
    (hdisj : ∀ a1 ∈ xs, ∀ a2 ∈ xs, a1 ≠ a2 → ∀ d, d ∈ g a1 → d ∈ g a2 → False) :
    (xs.flatMap g).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.flatMap_cons, List.nodup_append]
    rw [List.nodup_cons] at hxs
    refine ⟨hg_nodup x List.mem_cons_self,
      ih hxs.2 (fun a ha => hg_nodup a (List.mem_cons_of_mem x ha))
        (fun a1 ha1 a2 ha2 => hdisj a1 (List.mem_cons_of_mem x ha1) a2 (List.mem_cons_of_mem x ha2)),
      ?_⟩
    intro d hd1 y hy rfl
    rw [List.mem_flatMap] at hy
    rcases hy with ⟨z, hz_rest, hdz⟩
    have hne : x ≠ z := fun h => hxs.1 (h ▸ hz_rest)
    exact hdisj x List.mem_cons_self z (List.mem_cons_of_mem x hz_rest) hne d hd1 hdz

/-- Product list of divisors `divisors u` and `divisors v`. -/
def mulDivisorList (u v : Nat) : List Nat :=
  (divisors u).flatMap (fun a => (divisors v).map (fun b => a * b))

theorem mem_mulDivisorList_iff {u v d : Nat} (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v) :
    d ∈ mulDivisorList u v ↔ d ∈ divisors (u * v) := by
  unfold mulDivisorList
  rw [List.mem_flatMap, mem_divisors_iff]
  constructor
  · rintro ⟨a, ha, ha_map⟩
    rw [List.mem_map] at ha_map
    rcases ha_map with ⟨b, hb, rfl⟩
    rw [mem_divisors_iff] at ha hb
    exact ⟨Nat.mul_pos ha.1 hb.1, Nat.mul_le_mul ha.2.1 hb.2.1, Nat.mul_dvd_mul ha.2.2 hb.2.2⟩
  · rintro ⟨hd1, _, hdvd⟩
    obtain ⟨a, b, ha1, hau, had, hb1, hbv, hbd, rfl⟩ :=
      dvd_mul_coprime_unique hcop hu hv hd1 hdvd
    refine ⟨a, (mem_divisors_iff u a).mpr ⟨ha1, hau, had⟩, ?_⟩
    rw [List.mem_map]
    exact ⟨b, (mem_divisors_iff v b).mpr ⟨hb1, hbv, hbd⟩, rfl⟩

theorem nodup_map_mul {a : Nat} (ha : 0 < a) (xs : List Nat) (hxs : xs.Nodup) :
    (xs.map (fun b => a * b)).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.nodup_cons] at hxs
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hxs.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨y, hy, heq⟩
    have : y = x := Nat.eq_of_mul_eq_mul_left ha heq
    exact hxs.1 (this ▸ hy)

theorem nodup_mulDivisorList {u v : Nat} (_hu : 0 < u) (_hv : 0 < v) (hcop : Nat.Coprime u v) :
    (mulDivisorList u v).Nodup := by
  unfold mulDivisorList
  apply nodup_flatMap_of_disjoint (divisors_nodup u)
  · intro a ha
    have ha_pos : 0 < a := ((mem_divisors_iff u a).mp ha).1
    exact nodup_map_mul ha_pos (divisors v) (divisors_nodup v)
  · intro a1 ha1 a2 ha2 hne x hx1 hx2
    rw [List.mem_map] at hx1 hx2
    rcases hx1 with ⟨b1, hb1, rfl⟩
    rcases hx2 with ⟨b2, hb2, heq⟩
    have ha1_d : a1 ∣ u := ((mem_divisors_iff u a1).mp ha1).2.2
    have hb1_d : b1 ∣ v := ((mem_divisors_iff v b1).mp hb1).2.2
    have ha2_d : a2 ∣ u := ((mem_divisors_iff u a2).mp ha2).2.2
    have hb2_d : b2 ∣ v := ((mem_divisors_iff v b2).mp hb2).2.2
    have ⟨heq_a, _⟩ := dvd_mul_coprime_pair_unique hcop ha1_d hb1_d ha2_d hb2_d heq.symm
    exact hne heq_a

/-- **Multiplicativity of `tau`**: if `Nat.Coprime u v` (with `0 < u`, `0 < v`), then
    `tau (u * v) = tau u * tau v`. -/
theorem tau_mul_of_coprime {u v : Nat} (hcop : Nat.Coprime u v) (hu : 0 < u) (hv : 0 < v) :
    tau (u * v) = tau u * tau v := by
  rw [tau_eq_length_divisors, tau_eq_length_divisors, tau_eq_length_divisors]
  have heq_len : (divisors (u * v)).length = (mulDivisorList u v).length :=
    length_eq_of_nodup_equiv (divisors_nodup (u * v)) (nodup_mulDivisorList hu hv hcop)
      (fun d => (mem_mulDivisorList_iff hu hv hcop).symm)
  rw [heq_len]
  unfold mulDivisorList
  rw [List.length_flatMap]
  have hsum_const : ∀ (xs : List Nat),
      (xs.map (fun a => ((divisors v).map (fun b => a * b)).length)).sum = xs.length * (divisors v).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_map]
      have hlen_map : ((divisors v).map (fun b => a * b)).length = (divisors v).length :=
        List.length_map _
      have hrest : (List.map (fun x => (divisors v).length) rest).sum = rest.length * (divisors v).length := by
        simpa [List.length_map] using ih
      rw [hrest, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  exact hsum_const (divisors u)

/-- Multiplicativity of `tau` in `Nat.gcd u v = 1` form. -/
theorem tau_mul_eq_mul_of_gcd_one {u v : Nat} (hgcd : Nat.gcd u v = 1) :
    tau (u * v) = tau u * tau v := by
  by_cases hu : u = 0
  · subst hu; simp [tau, sumDiv, sumDivUpTo]
  · by_cases hv : v = 0
    · subst hv; simp [tau, sumDiv, sumDivUpTo]
    · exact tau_mul_of_coprime hgcd (Nat.pos_of_ne_zero hu) (Nat.pos_of_ne_zero hv)

/-- General multiplicativity of `sumDiv` for any multiplicative weight `w`. -/
theorem sumDiv_mul_of_coprime {u v : Nat} (hcop : Nat.Coprime u v) (hu : 0 < u) (hv : 0 < v)
    (w : Nat → Nat)
    (hw : ∀ a b : Nat, 1 ≤ a → 1 ≤ b → a ∣ u → b ∣ v → w (a * b) = w a * w b) :
    sumDiv (u * v) w = sumDiv u w * sumDiv v w := by
  have heq_u : sumDiv u w = sumList (divisors u) w := (sumList_divisorsUpTo_eq u w u).symm
  have heq_v : sumDiv v w = sumList (divisors v) w := (sumList_divisorsUpTo_eq v w v).symm
  have heq_uv : sumDiv (u * v) w = sumList (divisors (u * v)) w :=
    (sumList_divisorsUpTo_eq (u * v) w (u * v)).symm
  rw [heq_uv, heq_u, heq_v]
  have heq_list : sumList (divisors (u * v)) w = sumList (mulDivisorList u v) w :=
    sumList_eq_of_nodup_equiv (divisors_nodup (u * v)) (nodup_mulDivisorList hu hv hcop)
      (fun d => (mem_mulDivisorList_iff hu hv hcop).symm) w
  rw [heq_list]
  unfold mulDivisorList
  rw [sumList_flatMap]
  have hinner : ∀ a ∈ divisors u,
      sumList ((divisors v).map (fun b => a * b)) w = w a * sumList (divisors v) w := by
    intro a ha
    have ha_info := (mem_divisors_iff u a).mp ha
    exact sumList_map_mul a (divisors v) w (fun b hb => by
      have hb_info := (mem_divisors_iff v b).mp hb
      exact hw a b ha_info.1 hb_info.1 ha_info.2.2 hb_info.2.2)
  have hsum_fold : ∀ (xs : List Nat),
      (∀ a ∈ xs, sumList ((divisors v).map (fun b => a * b)) w = w a * sumList (divisors v) w) →
      sumList (xs.map (fun a => sumList ((divisors v).map (fun b => a * b)) w)) id =
        sumList xs w * sumList (divisors v) w := by
    intro xs hxs
    induction xs with
    | nil => simp [sumList]
    | cons a rest ih =>
      simp only [List.map_cons, sumList, id]
      rw [hxs a List.mem_cons_self]
      rw [ih (fun x hx => hxs x (List.mem_cons_of_mem a hx))]
      rw [Nat.add_mul]
  exact hsum_fold (divisors u) hinner

/-- **Multiplicativity of `fullMoment`**: if `Nat.gcd u v = 1`, then
    `fullMoment (u * v) = fullMoment u * fullMoment v`. -/
theorem fullMoment_mul_of_coprime {u v : Nat} (hgcd : Nat.gcd u v = 1) :
    fullMoment (u * v) = fullMoment u * fullMoment v := by
  by_cases hu : u = 0
  · subst hu; simp [fullMoment, sumDiv, sumDivUpTo]
  · by_cases hv : v = 0
    · subst hv; simp [fullMoment, sumDiv, sumDivUpTo]
    · unfold fullMoment
      apply sumDiv_mul_of_coprime hgcd (Nat.pos_of_ne_zero hu) (Nat.pos_of_ne_zero hv)
      intro a b ha1 hb1 hau hbv
      have hcop_ab : Nat.Coprime a b :=
        (Nat.Coprime.coprime_dvd_left hau hgcd).coprime_dvd_right hbv
      rw [tau_mul_of_coprime hcop_ab ha1 hb1]
      grind

end Multiplicativity

/-! ## Prime-Power Exact Formulas and Odd Parity Congruence -/

section PrimePowerParity

/-- Explicit list of divisors of `p ^ e` in increasing order: `[1, p, p^2, ..., p^e]`. -/
def primePowDivisors (p : Nat) : Nat → List Nat
  | 0 => [1]
  | e + 1 => primePowDivisors p e ++ [p ^ (e + 1)]

theorem mem_primePowDivisors_iff {p : Nat} (hp : IsPrime p) :
    ∀ e d, d ∈ primePowDivisors p e ↔ ∃ j, j ≤ e ∧ d = p ^ j
  | 0, d => by
    simp [primePowDivisors]
  | e + 1, d => by
    simp only [primePowDivisors, List.mem_append, List.mem_singleton, mem_primePowDivisors_iff hp e d]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, by omega, rfl⟩
      · exact ⟨e + 1, Nat.le_refl _, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hje : j ≤ e
      · exact Or.inl ⟨j, hje, rfl⟩
      · have hj' : j = e + 1 := by omega
        subst hj'
        exact Or.inr rfl

theorem primePowDivisors_nodup {p : Nat} (hp : IsPrime p) :
    ∀ e, (primePowDivisors p e).Nodup
  | 0 => by simp [primePowDivisors]
  | e + 1 => by
    rw [primePowDivisors, List.nodup_append]
    refine ⟨primePowDivisors_nodup hp e, List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
    intro d hd x hx
    rw [List.mem_singleton] at hx
    subst hx
    obtain ⟨j, hj, rfl⟩ := (mem_primePowDivisors_iff hp e d).mp hd
    have hp2 : 2 ≤ p := hp.1
    have hlt : p ^ j < p ^ (e + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

/-- Every divisor of `p ^ e` is `p ^ j` for some `j ≤ e`. -/
theorem dvd_prime_pow_iff {p : Nat} (hp : IsPrime p) :
    ∀ e d, d ∣ p ^ e ↔ ∃ j, j ≤ e ∧ d = p ^ j
  | 0, d => by
    simp only [Nat.pow_zero, Nat.dvd_one]
    constructor
    · rintro rfl; exact ⟨0, Nat.le_refl 0, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have : j = 0 := by omega
      subst this; rfl
  | e + 1, d => by
    constructor
    · intro hdvd
      by_cases hd1 : d = 1
      · exact ⟨0, Nat.zero_le _, hd1⟩
      · have hp2 : 2 ≤ p := hp.1
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pow_pos (by omega))
        have hd_gt1 : 1 < d := by omega
        have hp_dvd_d : p ∣ d := dvd_of_dvd_prime_pow hp hd_gt1 hdvd
        obtain ⟨k, rfl⟩ := hp_dvd_d
        have hk_dvd : k ∣ p ^ e := by
          rw [Nat.pow_succ'] at hdvd
          exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
        obtain ⟨j, hj, rfl⟩ := (dvd_prime_pow_iff hp e k).mp hk_dvd
        refine ⟨j + 1, by omega, ?_⟩
        rw [Nat.pow_succ']
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.exists_eq_add_of_le hj with ⟨m, hm⟩
      rw [hm, Nat.pow_add]
      exact Nat.dvd_mul_right (p ^ j) (p ^ m)

theorem mem_divisors_prime_pow_iff {p : Nat} (hp : IsPrime p) (e d : Nat) :
    d ∈ divisors (p ^ e) ↔ d ∈ primePowDivisors p e := by
  have hp2 : 2 ≤ p := hp.1
  have hpe_pos : 0 < p ^ e := Nat.pow_pos (by omega)
  rw [mem_divisors_iff, mem_primePowDivisors_iff hp]
  constructor
  · rintro ⟨_, _, hdvd⟩
    exact (dvd_prime_pow_iff hp e d).mp hdvd
  · rintro ⟨j, hj, rfl⟩
    refine ⟨Nat.pow_pos (by omega), Nat.pow_le_pow_right (by omega) hj, ?_⟩
    exact (dvd_prime_pow_iff hp e (p ^ j)).mpr ⟨j, hj, rfl⟩

/-- Exact formula `tau (p ^ e) = e + 1` for every prime `p`. -/
theorem tau_prime_pow {p : Nat} (hp : IsPrime p) (e : Nat) :
    tau (p ^ e) = e + 1 := by
  rw [tau_eq_length_divisors]
  have hlen : (divisors (p ^ e)).length = (primePowDivisors p e).length :=
    length_eq_of_nodup_equiv (divisors_nodup (p ^ e)) (primePowDivisors_nodup hp e)
      (fun d => mem_divisors_prime_pow_iff hp e d)
  rw [hlen]
  clear hlen
  induction e with
  | zero => rfl
  | succ k ih =>
    simp [primePowDivisors, ih]

/-- Recursive formula for `fullMoment (p ^ e)` for prime `p`. -/
theorem fullMoment_prime_pow_zero (p : Nat) :
    fullMoment (p ^ 0) = 1 := by
  rw [Nat.pow_zero]
  decide

theorem fullMoment_prime_pow_succ {p : Nat} (hp : IsPrime p) (e : Nat) :
    fullMoment (p ^ (e + 1)) = fullMoment (p ^ e) + (e + 2) * p ^ (e + 1) := by
  rw [fullMoment_eq_sumList_divisors, fullMoment_eq_sumList_divisors]
  have h1 : sumList (divisors (p ^ (e + 1))) (fun d => d * tau d) =
      sumList (primePowDivisors p (e + 1)) (fun d => d * tau d) :=
    sumList_eq_of_nodup_equiv (divisors_nodup (p ^ (e + 1))) (primePowDivisors_nodup hp (e + 1))
      (fun d => mem_divisors_prime_pow_iff hp (e + 1) d) _
  have h2 : sumList (divisors (p ^ e)) (fun d => d * tau d) =
      sumList (primePowDivisors p e) (fun d => d * tau d) :=
    sumList_eq_of_nodup_equiv (divisors_nodup (p ^ e)) (primePowDivisors_nodup hp e)
      (fun d => mem_divisors_prime_pow_iff hp e d) _
  rw [h1, h2, primePowDivisors, sumList_append]
  have hlast : sumList [p ^ (e + 1)] (fun d => d * tau d) = (e + 2) * p ^ (e + 1) := by
    simp [sumList, tau_prime_pow hp (e + 1)]
    rw [Nat.mul_comm]
  rw [hlast]

/-- **Odd Prime-Power Parity Congruence**: For every odd prime `p` and `e : Nat`,
    `fullMoment (p ^ e) % 2 = ((e + 1) * (e + 2) / 2) % 2`. -/
theorem fullMoment_prime_pow_mod_two {p : Nat} (hp : IsPrime p) (hp_odd : p % 2 = 1) (e : Nat) :
    fullMoment (p ^ e) % 2 = ((e + 1) * (e + 2) / 2) % 2 := by
  induction e with
  | zero =>
    rw [fullMoment_prime_pow_zero]
  | succ k ih =>
    rw [fullMoment_prime_pow_succ hp k]
    have hpow_odd : p ^ (k + 1) % 2 = 1 := by
      clear ih
      induction k + 1 with
      | zero => rfl
      | succ m ihm =>
        rw [Nat.pow_succ, Nat.mul_mod, ihm, hp_odd]
    have htri : (k + 2) * (k + 3) / 2 = (k + 1) * (k + 2) / 2 + (k + 2) := by
      have h2 : (k + 1) * (k + 2) + 2 * (k + 2) = (k + 2) * (k + 3) := by grind
      omega
    rw [htri]
    have h1 : (fullMoment (p ^ k) + (k + 2) * p ^ (k + 1)) % 2 =
        (fullMoment (p ^ k) % 2 + ((k + 2) % 2 * (p ^ (k + 1) % 2)) % 2) % 2 := by
      rw [Nat.add_mod, Nat.mul_mod]
    rw [h1, ih, hpow_odd, Nat.mul_one, Nat.mod_mod]
    omega

/-- Helper for triangular number parity mod 4. -/
private theorem tri_div_two_mod_two (e : Nat) :
    ((e + 1) * (e + 2) / 2) % 2 = if e % 4 = 0 ∨ e % 4 = 1 then 1 else 0 := by
  have he : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm
  have hmod : e % 4 < 4 := Nat.mod_lt e (by decide)
  have h0123 : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
  rcases h0123 with hr | hr | hr | hr
  · have hprod : (e + 1) * (e + 2) = 2 * (2 * (4 * (e / 4) * (e / 4) + 3 * (e / 4)) + 1) := by
      rw [he, hr]; grind
    have hdiv : (e + 1) * (e + 2) / 2 = 2 * (4 * (e / 4) * (e / 4) + 3 * (e / 4)) + 1 := by
      rw [hprod]; exact Nat.mul_div_right _ (by decide)
    rw [hdiv, hr]
    simp
  · have hprod : (e + 1) * (e + 2) = 2 * (2 * (4 * (e / 4) * (e / 4) + 5 * (e / 4) + 1) + 1) := by
      rw [he, hr]; grind
    have hdiv : (e + 1) * (e + 2) / 2 = 2 * (4 * (e / 4) * (e / 4) + 5 * (e / 4) + 1) + 1 := by
      rw [hprod]; exact Nat.mul_div_right _ (by decide)
    rw [hdiv, hr]
    simp
  · have hprod : (e + 1) * (e + 2) = 2 * (2 * (4 * (e / 4) * (e / 4) + 7 * (e / 4) + 3)) := by
      rw [he, hr]; grind
    have hdiv : (e + 1) * (e + 2) / 2 = 2 * (4 * (e / 4) * (e / 4) + 7 * (e / 4) + 3) := by
      rw [hprod]; exact Nat.mul_div_right _ (by decide)
    rw [hdiv, hr]
    simp
  · have hprod : (e + 1) * (e + 2) = 2 * (2 * (4 * (e / 4) * (e / 4) + 9 * (e / 4) + 5)) := by
      rw [he, hr]; grind
    have hdiv : (e + 1) * (e + 2) / 2 = 2 * (4 * (e / 4) * (e / 4) + 9 * (e / 4) + 5) := by
      rw [hprod]; exact Nat.mul_div_right _ (by decide)
    rw [hdiv, hr]
    simp

/-- Direct corollary of the odd prime-power parity congruence:
    `fullMoment (p ^ e)` is odd if and only if `e % 4 = 0 ∨ e % 4 = 1`. -/
theorem fullMoment_prime_pow_odd_iff {p : Nat} (hp : IsPrime p) (hp_odd : p % 2 = 1) (e : Nat) :
    fullMoment (p ^ e) % 2 = 1 ↔ e % 4 = 0 ∨ e % 4 = 1 := by
  rw [fullMoment_prime_pow_mod_two hp hp_odd e, tri_div_two_mod_two e]
  split <;> simp_all

end PrimePowerParity

/-! ## Exact Prime-Power Decomposition, General Parity Obstruction, and Sharpened Dominance -/

section GeneralParityAndDominance

/-- If `IsPrime p`, `p ^ e ∣ n`, and `¬ (p ^ (e + 1) ∣ n)`, then writing `n = p ^ e * m` gives
    `Nat.gcd (p ^ e) m = 1`. -/
theorem coprime_pow_cofactor_of_exact_dvd {p e n m : Nat} (hp : IsPrime p)
    (hndvd : ¬ (p ^ (e + 1) ∣ n)) (hnm : n = p ^ e * m) :
    Nat.gcd (p ^ e) m = 1 := by
  have hp_not_dvd_m : ¬ (p ∣ m) := by
    intro hpm
    rcases hpm with ⟨k, rfl⟩
    apply hndvd
    rw [hnm, Nat.pow_succ]
    exact ⟨k, by grind⟩
  have hcop_pm : Nat.Coprime p m := by
    rcases coprime_or_dvd_of_isPrime (d := m) hp with hcop | hdvd
    · exact hcop.symm
    · exact absurd hdvd hp_not_dvd_m
  exact hcop_pm.pow_left e

/-- **General Parity Obstruction Theorem**:
    If `IsFixedPoint n` and `tau n % 2 = 0` (equivalently, `n` is not a perfect square),
    then for every prime `p` and exponent `e` satisfying `p ^ e ∣ n` and `¬ (p ^ (e + 1) ∣ n)`,
    we must have `e % 4 = 0 ∨ e % 4 = 1`.
    In particular, no non-square fixed point can have any prime dividing it to an exponent
    congruent to `2` or `3` modulo `4`. -/
theorem exact_exponent_mod_four_of_isFixedPoint {n p e : Nat}
    (hfp : IsFixedPoint n) (htau_even : tau n % 2 = 0)
    (hp : IsPrime p) (hdvd : p ^ e ∣ n) (hndvd : ¬ (p ^ (e + 1) ∣ n)) :
    e % 4 = 0 ∨ e % 4 = 1 := by
  by_cases he0 : e = 0
  · subst he0
    exact Or.inl rfl
  · have hn_odd : n % 2 = 1 := odd_of_isFixedPoint hfp
    have hp_odd : p % 2 = 1 := by
      have he_eq : e = (e - 1) + 1 := by omega
      have hp_dvd_pe : p ∣ p ^ e := by
        rw [he_eq, Nat.pow_succ]
        exact Nat.dvd_mul_left p (p ^ (e - 1))
      have hp_dvd_n : p ∣ n := Nat.dvd_trans hp_dvd_pe hdvd
      rcases hp_dvd_n with ⟨k, rfl⟩
      have h2 : (p * k) % 2 = (p % 2 * (k % 2)) % 2 := Nat.mul_mod p k 2
      rw [hn_odd] at h2
      have hp2lt : p % 2 < 2 := Nat.mod_lt p (by decide)
      have hk2lt : k % 2 < 2 := Nat.mod_lt k (by decide)
      by_cases hp0 : p % 2 = 0
      · rw [hp0] at h2; omega
      · omega
    obtain ⟨m, hnm⟩ := hdvd
    have hcop : Nat.gcd (p ^ e) m = 1 :=
      coprime_pow_cofactor_of_exact_dvd hp hndvd hnm
    have hS_eq : fullMoment n = n * (tau n + 1) :=
      ((isFixedPoint_iff_fullMoment n).mp hfp).2
    have hS_odd : fullMoment n % 2 = 1 := by
      rw [hS_eq, Nat.mul_mod, hn_odd, Nat.add_mod, htau_even]
    have hS_mul : fullMoment n = fullMoment (p ^ e) * fullMoment m := by
      rw [hnm]
      exact fullMoment_mul_of_coprime hcop
    have hSpe_odd : fullMoment (p ^ e) % 2 = 1 := by
      rw [hS_mul, Nat.mul_mod] at hS_odd
      have h1 : fullMoment (p ^ e) % 2 < 2 := Nat.mod_lt _ (by decide)
      have h2 : fullMoment m % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases h0 : fullMoment (p ^ e) % 2 = 0
      · rw [h0] at hS_odd; omega
      · omega
    exact (fullMoment_prime_pow_odd_iff hp hp_odd e).mp hSpe_odd

/-- Corollary: No non-square fixed point can have a prime `p` dividing it to exact exponent
    `e` with `e % 4 = 2` or `e % 4 = 3`. -/
theorem not_isFixedPoint_of_exact_exponent_mod_four_ge_two {n p e : Nat}
    (htau_even : tau n % 2 = 0) (hp : IsPrime p)
    (hdvd : p ^ e ∣ n) (hndvd : ¬ (p ^ (e + 1) ∣ n))
    (hbad : e % 4 = 2 ∨ e % 4 = 3) :
    ¬ IsFixedPoint n := by
  intro hfp
  have hgood := exact_exponent_mod_four_of_isFixedPoint hfp htau_even hp hdvd hndvd
  omega

/-- Exact lower bound on `fullMoment (p ^ e)` for prime `p` and `e ≥ 1`:
    `(e + 1) * p ^ e + e * p ^ (e - 1) ≤ fullMoment (p ^ e)`. -/
theorem fullMoment_prime_pow_gt {p : Nat} (hp : IsPrime p) :
    ∀ e : Nat, 1 ≤ e → (e + 1) * p ^ e + e * p ^ (e - 1) ≤ fullMoment (p ^ e)
  | 0, he => by omega
  | 1, _ => by
    rw [fullMoment_prime_pow_succ hp 0, fullMoment_prime_pow_zero]
    simp
    omega
  | k + 2, _ => by
    have ih := fullMoment_prime_pow_gt hp (k + 1) (by omega)
    rw [fullMoment_prime_pow_succ hp (k + 1)]
    have hp2 : 2 ≤ p := hp.1
    have hpow_le : p ^ k ≤ p ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : (k + 2) * p ^ k ≤ (k + 2) * p ^ (k + 1) := Nat.mul_le_mul_left (k + 2) hpow_le
    have hsub1 : k + 1 - 1 = k := by omega
    have hsub2 : k + 2 - 1 = k + 1 := by omega
    rw [hsub1] at ih
    rw [hsub2]
    have heq2 : (k + 1 + 1) * p ^ (k + 1) = (k + 2) * p ^ (k + 1) := by grind
    have hge : (k + 2) * p ^ (k + 1) ≤ fullMoment (p ^ (k + 1)) := by
      rw [← heq2]; omega
    have hadd : (k + 2 + 1) * p ^ (k + 2) + (k + 2) * p ^ (k + 1) ≤
        fullMoment (p ^ (k + 1)) + (k + 1 + 2) * p ^ (k + 1 + 1) := by
      have heq1 : (k + 2 + 1) * p ^ (k + 2) = (k + 1 + 2) * p ^ (k + 1 + 1) := by grind
      omega
    exact hadd

/-- **Sharpened Dominance Bound**: For any prime `p`, exponent `e ≥ 1`, and `m > 1`
    with `n = p ^ e * m` and `Nat.gcd (p ^ e) m = 1`, `IsFixedPoint n → e * tau m < p`. -/
theorem sharpened_dominance_bound {n p e m : Nat} (hp : IsPrime p) (he : 1 ≤ e) (hm : 1 < m)
    (hnm : n = p ^ e * m) (hcop : Nat.gcd (p ^ e) m = 1) (hfp : IsFixedPoint n) :
    e * tau m < p := by
  by_cases hlt : e * tau m < p
  · exact hlt
  · exfalso
    have hple : p ≤ e * tau m := by omega
    have hp2 : 2 ≤ p := hp.1
    have hpe_eq : p ^ e = p * p ^ (e - 1) := by
      have he' : e = (e - 1) + 1 := by omega
      calc p ^ e = p ^ ((e - 1) + 1) := by rw [← he']
        _ = p ^ (e - 1) * p := Nat.pow_succ p (e - 1)
        _ = p * p ^ (e - 1) := Nat.mul_comm _ _
    have hn_split : n = p * (p ^ (e - 1) * m) := by
      rw [hnm, hpe_eq, Nat.mul_assoc]
    have hm'_gt1 : 1 < p ^ (e - 1) * m := by
      have hpow_pos : 1 ≤ p ^ (e - 1) := Nat.one_le_pow (e - 1) p (by omega)
      have hmul_le : 1 * m ≤ p ^ (e - 1) * m := Nat.mul_le_mul_right m hpow_pos
      omega
    have hcop_sub : Nat.Coprime (p ^ (e - 1)) m := by
      have hdvd_pow : p ^ (e - 1) ∣ p ^ e := by
        rw [hpe_eq]
        exact Nat.dvd_mul_left (p ^ (e - 1)) p
      exact Nat.Coprime.coprime_dvd_left hdvd_pow hcop
    have htau_m' : tau (p ^ (e - 1) * m) = e * tau m := by
      have hpow_pos : 0 < p ^ (e - 1) := Nat.pow_pos (by omega)
      rw [tau_mul_of_coprime hcop_sub hpow_pos (by omega), tau_prime_pow hp (e - 1)]
      have he1 : e - 1 + 1 = e := by omega
      rw [he1]
    have hnot := not_isFixedPoint_of_dvd_le_tau hn_split (by omega) hm'_gt1 (htau_m'.symm ▸ hple)
    exact hnot hfp

/-- Variant of the sharpened dominance bound in terms of `1 ≤ e` and `m > 1` with `p ^ e ∣ n`
    and `¬ (p ^ (e + 1) ∣ n)`. -/
theorem exact_prime_pow_tau_lt_prime {n p e m : Nat} (hp : IsPrime p) (he : 1 ≤ e) (hm : 1 < m)
    (_hdvd : p ^ e ∣ n) (hndvd : ¬ (p ^ (e + 1) ∣ n)) (hnm : n = p ^ e * m)
    (hfp : IsFixedPoint n) :
    e * tau m < p :=
  sharpened_dominance_bound hp he hm hnm (coprime_pow_cofactor_of_exact_dvd hp hndvd hnm) hfp

end GeneralParityAndDominance

end OeisA245211
