import BachCorollaries.Statement

/-!
# Miller's reduction of factoring to a multiple of `λ(n)`, from Bach's subgroup bound

Let `n = a b` be odd with `a, b > 2` coprime, and let `M = 2^s t` (`t` odd) satisfy `u^M = 1`
for every unit `u` mod `n`. Let `r₀ < s` be the largest `r` for which some unit has
`w^(2^r t) ≠ 1` (`r = 0` qualifies through `w = -1`). Every unit then has `y = u^(2^{r₀} t)`
with `y² = 1`, and

* the units with `y = ±1` form a subgroup `H`, proper by the Chinese remainder theorem;
* if `y ≠ ±1` then `y - 1` is neither `0` nor a unit (as `(y - 1)(y + 1) = 0`), so
  `gcd(u^(2^{r₀} t) - 1, n)` is a proper factor of `n`.

`Ankeny.BachSubgroupBound c` gives a unit outside `H` of residue `≤ c log² n`.
Miller (1976) for the reduction; Bach (1990) for the explicit constant.
-/

namespace BachCorollaries

/-- An odd `n > 1` that is not a prime power is a product of two coprime factors `> 2`. -/
theorem exists_coprime_factors {n : ℕ} (hn : Odd n) (h1 : 1 < n) (hpp : ¬ IsPrimePow n) :
    ∃ a b : ℕ, a.Coprime b ∧ 2 < a ∧ 2 < b ∧ n = a * b := by
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hn0 : n ≠ 0 := by omega
  have hk : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn0).mp hpn
  refine ⟨p ^ n.factorization p, n / p ^ n.factorization p,
    (Nat.coprime_ordCompl hp hn0).pow_left _, ?_, ?_, (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  · have hp2 : 2 < p := by
      have := Nat.odd_iff.mp (Odd.of_dvd_nat hn hpn)
      have := hp.two_le
      omega
    exact lt_of_lt_of_le hp2 (Nat.le_self_pow (by omega) p)
  · set B := n / p ^ n.factorization p
    have hBn : B ∣ n := Nat.ordCompl_dvd n p
    have hBo : Odd B := Odd.of_dvd_nat hn hBn
    have hB0 : B ≠ 0 := by rintro h; rw [h] at hBn; exact hn0 (Nat.eq_zero_of_zero_dvd hBn)
    have hB1 : B ≠ 1 := by
      intro hB
      apply hpp
      rw [isPrimePow_nat_iff]
      refine ⟨p, n.factorization p, hp, hk, ?_⟩
      have := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [show n / p ^ n.factorization p = B from rfl, hB, mul_one] at this
      exact this
    obtain ⟨j, hj⟩ := hBo
    omega

/-- The subgroup lemma: for `n = a b` as above and `M = 2^s t` killing `(ZMod n)ˣ`, there are
`r < s` and a proper subgroup `H` such that every unit `u ∉ H` has `u^(2^r t) - 1` neither zero
nor a unit. -/
theorem exists_subgroup_factoring {a b : ℕ} (hab : a.Coprime b) (ha : 2 < a) (hb : 2 < b)
    {s t : ℕ} (ht : Odd t) (hall : ∀ u : (ZMod (a * b))ˣ, u ^ (2 ^ s * t) = 1) :
    ∃ r < s, ∃ H : Subgroup (ZMod (a * b))ˣ, H ≠ ⊤ ∧ ∀ u : (ZMod (a * b))ˣ, u ∉ H →
      (u : ZMod (a * b)) ^ (2 ^ r * t) ≠ 1 ∧ ¬ IsUnit ((u : ZMod (a * b)) ^ (2 ^ r * t) - 1) := by
  classical
  have : Fact (2 < a * b) := ⟨by nlinarith⟩
  have : Fact (2 < a) := ⟨ha⟩
  have : Fact (2 < b) := ⟨hb⟩
  let P : ℕ → Prop := fun r => ∃ w : (ZMod (a * b))ˣ, w ^ (2 ^ r * t) ≠ 1
  have P0 : P 0 := ⟨-1, by
    rw [pow_zero, one_mul, ht.neg_one_pow]
    intro h
    exact ZMod.neg_one_ne_one (congrArg Units.val h)⟩
  have hPs : ¬ P s := fun ⟨w, hw⟩ => hw (hall w)
  set r₀ := Nat.findGreatest P s with hr₀def
  obtain ⟨w, hw⟩ : P r₀ := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hr₀s : r₀ < s := by
    rcases (Nat.findGreatest_le (P := P) s).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ (⟨w, hw⟩ : P r₀)) hPs
  have hsq : ∀ u : (ZMod (a * b))ˣ, (u ^ (2 ^ r₀ * t)) ^ 2 = 1 := by
    intro u
    by_contra hne
    have : ¬ P (r₀ + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self r₀) (by omega)
    exact this ⟨u, by rw [show 2 ^ (r₀ + 1) * t = 2 ^ r₀ * t * 2 by ring, pow_mul]; exact hne⟩
  let H : Subgroup (ZMod (a * b))ˣ :=
    { carrier := {u | u ^ (2 ^ r₀ * t) = 1 ∨ u ^ (2 ^ r₀ * t) = -1}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy) <;> simp [mul_pow, hx, hy]
      one_mem' := by simp
      inv_mem' := by
        rintro x (hx | hx) <;> simp [inv_pow, hx] }
  refine ⟨r₀, hr₀s, H, ?_, ?_⟩
  · intro htop
    by_cases hwm : w ^ (2 ^ r₀ * t) = -1
    · -- the CRT unit `(w mod a, 1)`
      let cr := ZMod.chineseRemainder hab
      obtain ⟨x, hxdef⟩ : ∃ x, x = (cr (w : ZMod (a * b))).1 := ⟨_, rfl⟩
      have hx : IsUnit x := hxdef ▸ (Prod.isUnit_iff.mp (w.isUnit.map cr)).1
      have hv : IsUnit (cr.symm (x, 1)) := by
        apply IsUnit.map
        exact Prod.isUnit_iff.mpr ⟨hx, isUnit_one⟩
      have hxe : x ^ (2 ^ r₀ * t) = -1 := by
        have := congrArg (fun z : (ZMod (a * b))ˣ => (cr (z : ZMod (a * b))).1) hwm
        simpa [hxdef] using this
      have key : cr ((hv.unit : ZMod (a * b)) ^ (2 ^ r₀ * t)) = (-1, 1) := by
        rw [IsUnit.unit_spec, map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk, hxe, one_pow]
      have hmem : hv.unit ∈ H := htop ▸ Subgroup.mem_top _
      rcases hmem with h | h
      · rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at h
        rw [h, map_one] at key
        exact ZMod.neg_one_ne_one (congrArg Prod.fst key).symm
      · rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
        rw [h, map_neg, map_one] at key
        exact ZMod.neg_one_ne_one (congrArg Prod.snd key)
    · have hmem : w ∈ H := htop ▸ Subgroup.mem_top _
      rcases hmem with h | h
      · exact hw h
      · exact hwm h
  · intro u hu
    have hy2 := congrArg Units.val (hsq u)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_one] at hy2
    set y := (u : ZMod (a * b)) ^ (2 ^ r₀ * t) with hy
    have hy1 : y ≠ 1 := by
      intro h
      apply hu
      left
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
      exact h
    refine ⟨hy1, fun hunit => hu (Or.inr ?_)⟩
    have hfac : (y - 1) * (y + 1) = 0 := by linear_combination hy2
    have hy' : y + 1 = 0 := hunit.mul_right_eq_zero.mp hfac
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    exact eq_neg_of_add_eq_zero_left hy'

/-- **Miller's factoring reduction from Bach's bound.** -/
theorem millerFactoring_of_bach {c : ℝ} (h : Ankeny.BachSubgroupBound c) :
    MillerFactoringStatement c := by
  intro n M hn h1 hpp hM hall
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := exists_coprime_factors hn h1 hpp
  set s := M.factorization 2
  set t := M / 2 ^ s
  have hMst : 2 ^ s * t = M := Nat.ordProj_mul_ordCompl_eq_self M 2
  have ht : Odd t := by
    have := Nat.coprime_ordCompl Nat.prime_two hM.ne'
    exact Nat.odd_iff.mpr (by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h0
      · exact absurd (Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mod_eq_zero h0) this)
          (by norm_num)
      · exact h0)
  have hall' : ∀ u : (ZMod (a * b))ˣ, u ^ (2 ^ s * t) = 1 := fun u => hMst ▸ hall u
  obtain ⟨r, hrs, H, hH, hsplit⟩ := exists_subgroup_factoring hab ha hb ht hall'
  have : NeZero (a * b) := ⟨by positivity⟩
  have : Nontrivial (ZMod (a * b)) := ZMod.nontrivial_iff.mpr (by nlinarith)
  obtain ⟨u, huH, huc⟩ := h (a * b) H hH
  obtain ⟨hne1, hnu⟩ := hsplit u huH
  set A := (u : ZMod (a * b)).val
  have hA0 : 0 < A := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero)
  have hcast : ((A ^ (2 ^ r * t) - 1 : ℕ) : ZMod (a * b)) =
      (u : ZMod (a * b)) ^ (2 ^ r * t) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hA0), Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one]
  refine ⟨A, hA0, huc, r, hrs.le, ?_, ?_⟩
  · have hg0 : 0 < Nat.gcd (A ^ (2 ^ r * t) - 1) (a * b) := Nat.gcd_pos_of_pos_right _ (by positivity)
    have hg1 : Nat.gcd (A ^ (2 ^ r * t) - 1) (a * b) ≠ 1 := by
      intro hg
      apply hnu
      rw [← hcast]
      exact (ZMod.isUnit_iff_coprime _ _).mpr hg
    omega
  · have hle := Nat.gcd_le_right (m := A ^ (2 ^ r * t) - 1) (n := a * b) (by positivity)
    refine lt_of_le_of_ne hle fun hg => hne1 ?_
    have hdvd : a * b ∣ A ^ (2 ^ r * t) - 1 := hg ▸ Nat.gcd_dvd_left _ _
    rw [← sub_eq_zero, ← hcast, ZMod.natCast_eq_zero_iff]
    exact hdvd

end BachCorollaries
