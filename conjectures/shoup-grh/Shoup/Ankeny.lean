import Shoup.Statement
import Erdos985.Indicator
import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.Principal

/-!
# The exponential-in-`ω` bound `g(p) ≤ 1089 (2^{ω(p-1)} log p)²` under GRH

This is the plain character expansion of the primitive-root indicator, already carried out in
erdos-985 (`Erdos985.principal_le_of_no_prime_primitive_root`), combined with Bach's weighted
prime-sum bounds under GRH (`Erdos985.Analytic.bach_nonprincipal_of_GRH`,
`Erdos985.Analytic.bach_principal_of_GRH`; McGown–Treviño–Trudgian, Lemma 1).

If no prime `q < x ≤ p` is a primitive root, then with `S = Σ_{n<x} Λ(n)(1 - n/x)`,
`W = 2^{ω(p-1)} - 1`, `L = log p` and `s = √x`:

* `x/2 - s/20 - 3 ≤ S` (principal part),
* `S ≤ W · c(p,x) · s · L` (indicator expansion), and `c(p,x) ≤ 13` for `p ≥ 3`, `x ≥ 1`,

so `s² / 2 ≤ 13 W L s + s/20 + 3`, whence `s ≤ 33 W L` and `x ≤ 1089 (W L)²`.
-/

namespace Shoup

open ArithmeticFunction Real Erdos985
open scoped ArithmeticFunction.omega

/-- Crude uniform bound on the constant of MTT Lemma 1: `c(p, x) ≤ 13` for `p ≥ 3`, `x ≥ 1`. -/
lemma bachC_le_thirteen (p x : ℕ) (hp : 3 ≤ p) (hx : 1 ≤ x) : bachC p x ≤ 13 := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hL : 1 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hs : 1 ≤ √(x : ℝ) := Real.one_le_sqrt.mpr hxR
  have hs0 : 0 < √(x : ℝ) := by linarith
  have h1 : 2 / √(x : ℝ) ≤ 2 := div_le_self (by norm_num) hs
  have hr : (1 : ℝ) ≤ (x : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hxR (by norm_num)
  have h2 : 3 / (x : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := div_le_self (by norm_num) hr
  have h3 : (5 / 3) / Real.log p ≤ 5 / 3 := div_le_self (by norm_num) hL
  have h3' : 0 ≤ (5 / 3) / Real.log p := by positivity
  have hlog : Real.log x ≤ 2 * √(x : ℝ) - 2 := by
    have hsq : Real.log x = 2 * Real.log √(x : ℝ) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have := Real.log_le_sub_one_of_pos hs0
    linarith
  have h4 : (Real.log x + 2) / (√(x : ℝ) * Real.log p) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hA : 0 ≤ 1 + 2 / √(x : ℝ) + 3 / (x : ℝ) ^ (3 / 2 : ℝ) := by positivity
  unfold bachC
  have : (1 + 2 / √(x : ℝ) + 3 / (x : ℝ) ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p)
      ≤ 6 * (8 / 3) := by
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  nlinarith

/-- `ω(p - 1) ≥ 1` for an odd prime `p`. -/
lemma one_le_card_primeFactors (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ (p - 1).primeFactors.card := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))

/-- **Key inequality.** Under GRH, if no prime `q < x` is a primitive root modulo the odd prime
`p`, where `1 ≤ x ≤ p`, then `x ≤ 1089 (2^{ω(p-1)} log p)²`. -/
theorem le_of_no_prime_primitive_root_lt (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ q, q.Prime → q < x → orderOf (q : ZMod p) ≠ p - 1) :
    (x : ℝ) ≤ 1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have key := principal_le_of_no_prime_primitive_root p hp2 x hxp
    (bachC p x * √(x : ℝ) * Real.log p)
    (fun χ hχ => Analytic.bach_nonprincipal_of_GRH hGRH p χ hχ x hx1) hno
  have hprin := (abs_le.mp (Analytic.bach_principal_of_GRH hGRH x hx1)).1
  rw [cardDistinctFactors_eq_card_primeFactors]
  set r := (p - 1).primeFactors.card with hr
  have hr1 : 1 ≤ r := one_le_card_primeFactors p hp hp2
  have h2r : (2 : ℝ) ≤ 2 ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr1
  set W : ℝ := 2 ^ r - 1 with hW
  have hW1 : 1 ≤ W := by linarith
  set L := Real.log p with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    linarith
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  set s := √(x : ℝ) with hsdef
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr hxR
  have hss : s * s = x := Real.mul_self_sqrt (by linarith)
  have hc := bachC_le_thirteen p x h3 hx1
  have hWL : 1 ≤ W * L := by nlinarith
  -- `S ≤ W · c · s · L ≤ 13 W s L`
  have hup : (∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)) ≤ 13 * (W * L) * s := by
    refine key.trans ?_
    have : 0 ≤ W * s * L := by positivity
    calc W * (bachC p x * s * L) = bachC p x * (W * s * L) := by ring
      _ ≤ 13 * (W * s * L) := mul_le_mul_of_nonneg_right hc this
      _ = 13 * (W * L) * s := by ring
  -- `s² / 2 ≤ 13 W L s + s/20 + 3`, so `s ≤ 33 W L`
  have hsb : s ≤ 33 * (W * L) := by nlinarith
  have hx : (x : ℝ) ≤ 1089 * (W * L) ^ 2 := by nlinarith
  have hWle : W * L ≤ 2 ^ r * L := by nlinarith
  calc (x : ℝ) ≤ 1089 * (W * L) ^ 2 := hx
    _ ≤ 1089 * (2 ^ r * L) ^ 2 := by gcongr

/-- Every prime has a primitive root `g` with `0 < g < p`. -/
lemma exists_primitiveRoot_lt (p : ℕ) [hp : Fact p.Prime] :
    ∃ g : ℕ, 0 < g ∧ g < p ∧ orderOf (g : ZMod p) = p - 1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf u = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units]
  refine ⟨(u : ZMod p).val, ZMod.val_pos.mpr u.ne_zero, ZMod.val_lt _, ?_⟩
  rw [ZMod.natCast_zmod_val, orderOf_units, hord]

/-- Under GRH, every odd prime `p` with `1089 (2^{ω(p-1)} log p)² < p` has a *prime* primitive
root `q ≤ 1089 (2^{ω(p-1)} log p)²`. -/
theorem prime_primitive_root_le_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : 1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2 < p) :
    HasPrimePrimitiveRootLE p (1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2) := by
  set B := 1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set X := ⌊B⌋₊ + 1 with hX
  have hXp : X ≤ p := by
    have : ⌊B⌋₊ < p := (Nat.floor_lt hB0).mpr hlt
    omega
  by_contra hcon
  have hno : ∀ q, q.Prime → q < X → orderOf (q : ZMod p) ≠ p - 1 := by
    intro q hq hqX hord
    apply hcon
    refine ⟨q, hq, ?_, hord⟩
    have : q ≤ ⌊B⌋₊ := by omega
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hB0)
  have := le_of_no_prime_primitive_root_lt hGRH p hp hp2 X (by omega) hXp hno
  have hlt' : B < (X : ℝ) := by
    rw [hX]; push_cast; exact Nat.lt_floor_add_one B
  linarith

/-- **Main theorem (exponential-in-`ω` form).** Under GRH, every odd prime `p` has a primitive
root `g` with `0 < g ≤ 1089 (2^{ω(p-1)} log p)²`. -/
theorem leastPrimitiveRoot_le_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hlt : 1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2 < p
  · obtain ⟨q, hq, hqB, hord⟩ := prime_primitive_root_le_of_GRH hGRH p hp hp2 hlt
    exact ⟨q, hq.pos, hqB, hord⟩
  · obtain ⟨g, hg0, hgp, hord⟩ := exists_primitiveRoot_lt p
    refine ⟨g, hg0, ?_, hord⟩
    have : (g : ℝ) < p := by exact_mod_cast hgp
    linarith

/-- `AnkenyTypeStatement` holds under GRH, with `C = 1089`. -/
theorem ankenyType_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : AnkenyTypeStatement :=
  ⟨1089, fun p hp hp2 => leastPrimitiveRoot_le_of_GRH hGRH p hp hp2⟩

end Shoup
