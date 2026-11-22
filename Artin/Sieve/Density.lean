import Artin.Sieve.PrimitiveRoot

/-!
# From an asymptotic for `N(x)` to `HasDensity` (blueprint B7)

`Set.HasDensity` (in `Artin/Statement.lean`) measures `S a` against the primes `p < b`, that is
against `π' b = π(b - 1)`, while the sieve naturally produces `N(x) / π(x)` with `π(x)` counting
primes `≤ x`. The two differ by at most one prime, and `π → ∞`, so the limits agree.
Primes dividing `a` are not in `S a` (there `a = 0` in `ZMod p`, of order `0 ≠ p - 1`), so
`primRootCount a x` is exactly the number of elements of `S a` below `x`;
`hasDensity_of_tendsto_of_bounded` absorbs any other convention that differs from it by `O(1)`,
such as also counting the finitely many primes dividing `a`.
-/

namespace Artin

open ArtinPrimitiveRootsConjecture Filter Finset
open scoped Topology

/-- The partial density of `S a` among the primes, at `b`, is `N(b) / π'(b)`. -/
lemma partialDensity_S_eq (a : ℤ) (b : ℕ) :
    (S a).partialDensity {p | p.Prime} b =
      (primRootCount a b : ℝ) / (Nat.primeCounting' b : ℝ) := by
  classical
  have h1 : (S a ∩ {p | p.Prime}) ∩ Set.Iio b =
      ↑((range b).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1) := by
    ext p
    simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, coe_filter, mem_range]
    tauto
  have h2 : {p : ℕ | p.Prime} ∩ Set.Iio b = ↑(Nat.primesBelow b) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Nat.primesBelow, coe_filter,
      mem_range]
    tauto
  rw [Set.partialDensity, h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Nat.primesBelow_card_eq_primeCounting', primRootCount]

/-- `π(b) ≤ π'(b) + 1`: the primes `≤ b` are the primes `< b` and possibly `b`. -/
lemma primeCounting_le_primeCounting'_add_one (b : ℕ) :
    Nat.primeCounting b ≤ Nat.primeCounting' b + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

/-- `π(b) / π'(b) → 1`. -/
lemma tendsto_primeCounting_div_primeCounting' :
    Tendsto (fun b : ℕ => (Nat.primeCounting b : ℝ) / Nat.primeCounting' b) atTop (𝓝 1) := by
  have hinv : Tendsto (fun b : ℕ => ((Nat.primeCounting' b : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting')
  have hupper : Tendsto (fun b : ℕ => 1 + ((Nat.primeCounting' b : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using hinv.const_add 1
  have hpos : ∀ᶠ b : ℕ in atTop, 0 < (Nat.primeCounting' b : ℝ) := by
    filter_upwards [Nat.tendsto_primeCounting'.eventually_gt_atTop 0] with b hb
    exact_mod_cast hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hpos] with b hb
    rw [le_div_iff₀ hb, one_mul]
    exact_mod_cast Nat.monotone_primeCounting' (Nat.le_succ b)
  · filter_upwards [hpos] with b hb
    rw [div_le_iff₀ hb, add_mul, one_mul, inv_mul_cancel₀ hb.ne']
    exact_mod_cast primeCounting_le_primeCounting'_add_one b

/-- **Density assembly (blueprint B7).** If `N(x) / π(x) → δ`, where `N(x) = primRootCount a x`
counts the primes `p < x` with `a` a primitive root mod `p`, then `S a` has density `δ` among
the primes. -/
theorem hasDensity_of_tendsto (a : ℤ) (δ : ℝ)
    (h : Tendsto (fun x : ℕ => (primRootCount a x : ℝ) / Nat.primeCounting x) atTop (𝓝 δ)) :
    (S a).HasDensity δ {p | p.Prime} := by
  unfold Set.HasDensity
  have hlim := h.mul tendsto_primeCounting_div_primeCounting'
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Nat.tendsto_primeCounting.eventually_gt_atTop 0] with b hb
  rw [partialDensity_S_eq]
  have hb' : (Nat.primeCounting b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

/-- **Density assembly, robust form.** Any count `N'` within `O(1)` of `primRootCount a` (for
instance one that also counts the finitely many primes dividing `a`, or counts `p ≤ x` instead
of `p < x`) with `N'(x) / π(x) → δ` also gives density `δ`. -/
theorem hasDensity_of_tendsto_of_bounded (a : ℤ) (δ : ℝ) (N : ℕ → ℝ) (C : ℝ)
    (hN : ∀ᶠ x : ℕ in atTop, |N x - primRootCount a x| ≤ C)
    (h : Tendsto (fun x : ℕ => N x / Nat.primeCounting x) atTop (𝓝 δ)) :
    (S a).HasDensity δ {p | p.Prime} := by
  refine hasDensity_of_tendsto a δ ?_
  have hinv : Tendsto (fun b : ℕ => C * ((Nat.primeCounting b : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting)).const_mul C
  have hdiff : Tendsto (fun x : ℕ => ((primRootCount a x : ℝ) - N x) / Nat.primeCounting x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [hN, Nat.tendsto_primeCounting.eventually_gt_atTop 0] with x hx hpos
    have hposR : (0 : ℝ) < Nat.primeCounting x := by exact_mod_cast hpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hposR, abs_sub_comm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hx (inv_nonneg.mpr hposR.le)
  have := h.add hdiff
  rw [add_zero] at this
  refine this.congr fun x => ?_
  rw [← add_div]
  ring_nf

end Artin
