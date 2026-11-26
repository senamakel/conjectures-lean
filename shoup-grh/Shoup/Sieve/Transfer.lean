import Shoup.Sieve.Rep
import Erdos985.Indicator

/-!
# From monomials in power-residue indicators to character sums

Fix a character `ψ` of order `N = p - 1` modulo the prime `p`. For a prime `ℓ ∣ N`, `n` is an
`ℓ`-th power residue iff `ψ(n)^{N/ℓ} = 1`; `ind ψ n ℓ ∈ {0, 1}` records this. For a set `U` of
prime divisors of `N` with product `d`,

`|Σ_{n<x} Λ(n)(1 - n/x) ∏_{ℓ∈U} ind ψ n ℓ - S(x)/d| ≤ B`,

where `B` bounds every non-principal weighted sum `bachSum χ x` (`sum_ind_sub_le`). This uses
erdos-985's `norm_W_le`. By linearity, any combination `F` of such monomials of mass `M` satisfies
`|Σ_{n<x} Λ(n)(1 - n/x) F(ind ψ n) - S(x) F(1/ℓ)| ≤ M B` (`transfer`).
-/

namespace Shoup.Sieve

open ArithmeticFunction Finset Erdos985 Erdos985.Indicator

variable {p : ℕ} [Fact p.Prime]

/-- `1` if `ψ(n)^{(p-1)/ℓ} = 1` (`n` is an `ℓ`-th power residue), else `0`. -/
noncomputable def ind (ψ : DirichletCharacter ℂ p) (n : ℕ) (ℓ : ℕ) : ℝ :=
  if ψ n ^ ((p - 1) / ℓ) = 1 then 1 else 0

/-- The weights `Λ(n)(1 - n/x)`. -/
noncomputable def wt (x n : ℕ) : ℝ := (Λ n : ℝ) * (1 - (n : ℝ) / x)

/-- The reciprocal weights `1/ℓ`. -/
noncomputable def recip (ℓ : ℕ) : ℝ := 1 / (ℓ : ℝ)

lemma ind_cast (ψ : DirichletCharacter ℂ p) {n : ℕ} (hn : (n : ZMod p) ≠ 0) {ℓ : ℕ}
    (hℓ : ℓ ∈ (p - 1).primeFactors) :
    ((ind ψ n ℓ : ℝ) : ℂ) = (1 + ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))) / ℓ := by
  obtain ⟨hℓp, hℓd, _⟩ := Nat.mem_primeFactors.mp hℓ
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
  have hN : ψ n ^ (p - 1) = 1 := by
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one hn, map_one]
  set ζ := ψ n ^ ((p - 1) / ℓ) with hζ
  have hζℓ : ζ ^ ℓ = 1 := by rw [hζ, ← pow_mul, Nat.div_mul_cancel hℓd, hN]
  have hsum : 1 + ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) = ∑ i ∈ range ℓ, ζ ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hℓp.pos, pow_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_mul']
  rw [hsum]
  unfold ind
  by_cases h1 : ζ = 1
  · rw [if_pos h1, h1]; simp [hℓ0]
  · rw [if_neg h1, geom_sum_eq h1, hζℓ]; simp

lemma natCast_ne_zero_of_vonMangoldt {x n : ℕ} (hxp : x ≤ p) (hn : n < x) (hΛ : Λ n ≠ 0) :
    (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have hn0 : n ≠ 0 := by rintro rfl; simp at hΛ
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h
  omega

/-- The weighted count of `d`-th power residues, `d = ∏ U`, is `S/d` up to `B`. -/
theorem sum_ind_sub_le (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1) (x : ℕ)
    (hxp : x ≤ p) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (U : Finset ℕ) (hU : U ⊆ (p - 1).primeFactors) :
    |∑ n ∈ range x, wt x n * ∏ ℓ ∈ U, ind ψ n ℓ
      - (∑ n ∈ range x, wt x n) * ∏ ℓ ∈ U, recip ℓ| ≤ B := by
  classical
  set A : ℕ → ℕ → ℂ := fun ℓ n => ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) with hA
  have hℓpos : ∀ ℓ ∈ U, (0 : ℝ) < ℓ := fun ℓ h =>
    by exact_mod_cast (Nat.mem_primeFactors.mp (hU h)).1.pos
  set d : ℝ := ∏ ℓ ∈ U, (ℓ : ℝ) with hd
  have hdpos : 0 < d := Finset.prod_pos hℓpos
  have hrec : ∏ ℓ ∈ U, recip ℓ = 1 / d := by
    simp only [recip, hd, Finset.prod_div_distrib, Finset.prod_const_one]
  -- pointwise expansion
  have hpt : ∀ n ∈ range x, ((wt x n * ∏ ℓ ∈ U, ind ψ n ℓ : ℝ) : ℂ) =
      (1 / (d : ℂ)) * ∑ t ∈ U.powerset,
        (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ t, A ℓ n := by
    intro n hn
    by_cases hΛ : Λ n = 0
    · simp [wt, hΛ]
    have hn0 := natCast_ne_zero_of_vonMangoldt hxp (mem_range.mp hn) hΛ
    have : ((∏ ℓ ∈ U, ind ψ n ℓ : ℝ) : ℂ) = (∏ ℓ ∈ U, (1 + A ℓ n)) / (d : ℂ) := by
      push_cast
      rw [Finset.prod_congr rfl fun ℓ h => ind_cast ψ hn0 (hU h), Finset.prod_div_distrib]
      simp [hd, hA]
    rw [Complex.ofReal_mul, this, Finset.prod_one_add, ← Finset.mul_sum]
    simp only [wt]; push_cast; ring
  have hsumC : ((∑ n ∈ range x, wt x n * ∏ ℓ ∈ U, ind ψ n ℓ : ℝ) : ℂ) =
      (1 / (d : ℂ)) * ∑ t ∈ U.powerset, W p ψ x t := by
    push_cast
    rw [Finset.sum_congr rfl fun n hn => by exact_mod_cast hpt n hn, ← Finset.mul_sum,
      Finset.sum_comm]
    simp only [W, hA, Complex.ofReal_div, Complex.ofReal_one]
  have hW0 : W p ψ x ∅ = ((∑ n ∈ range x, wt x n : ℝ) : ℂ) := by
    simp [W, wt]
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset U), hW0] at hsumC
  -- the error term
  set R := ∑ t ∈ U.powerset.erase ∅, W p ψ x t with hR
  have hdiff : ((∑ n ∈ range x, wt x n * ∏ ℓ ∈ U, ind ψ n ℓ
      - (∑ n ∈ range x, wt x n) * ∏ ℓ ∈ U, recip ℓ : ℝ) : ℂ) = (1 / (d : ℂ)) * R := by
    rw [Complex.ofReal_sub, hsumC, hrec]; push_cast; ring
  have hRle : ‖R‖ ≤ (d - 1) * B := by
    calc ‖R‖ ≤ ∑ t ∈ U.powerset.erase ∅, ‖W p ψ x t‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ U.powerset.erase ∅, (∏ ℓ ∈ t, ((ℓ : ℝ) - 1)) * B := by
          refine Finset.sum_le_sum fun t ht => ?_
          have htU := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
          exact norm_W_le p ψ hψ x B hB t (htU.trans hU)
            (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht))
      _ = (d - 1) * B := by
          rw [← Finset.sum_mul]
          congr 1
          have h1 : ∑ t ∈ U.powerset, ∏ ℓ ∈ t, ((ℓ : ℝ) - 1) = d := by
            rw [← Finset.prod_one_add, hd]
            exact Finset.prod_congr rfl fun ℓ _ => by ring
          rw [Finset.sum_erase_eq_sub (Finset.empty_mem_powerset U), h1, Finset.prod_empty]
  have : |∑ n ∈ range x, wt x n * ∏ ℓ ∈ U, ind ψ n ℓ
      - (∑ n ∈ range x, wt x n) * ∏ ℓ ∈ U, recip ℓ| = ‖R‖ / d := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff, norm_mul, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hdpos]
    ring
  rw [this, div_le_iff₀ hdpos]
  nlinarith

/-- **Transfer.** A combination `F` of monomials of mass `M` over prime divisors of `p - 1`. -/
theorem transfer (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1) (x : ℕ)
    (hxp : x ≤ p) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    {F : (ℕ → ℝ) → ℝ} {M : ℝ} (hF : IsRep F (p - 1).primeFactors M) :
    |∑ n ∈ range x, wt x n * F (ind ψ n) - (∑ n ∈ range x, wt x n) * F recip| ≤ M * B := by
  obtain ⟨L, hL, hM, hFL⟩ := hF
  simp_rw [hFL]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hM hB0)
  clear hFL hM
  induction L with
  | nil => simp [ev, mass]
  | cons q L ih =>
    have ih' := ih fun r h => hL r (List.mem_cons_of_mem _ h)
    have hq := sum_ind_sub_le ψ hψ x hxp B hB0 hB q.1 (hL q List.mem_cons_self)
    simp only [ev, mass, List.map_cons, List.sum_cons] at ih' ⊢
    have : ∑ n ∈ range x, wt x n * (q.2 * ∏ ℓ ∈ q.1, ind ψ n ℓ +
          (List.map (fun q => q.2 * ∏ ℓ ∈ q.1, ind ψ n ℓ) L).sum)
        - (∑ n ∈ range x, wt x n) * (q.2 * ∏ ℓ ∈ q.1, recip ℓ +
          (List.map (fun q => q.2 * ∏ ℓ ∈ q.1, recip ℓ) L).sum)
        = q.2 * (∑ n ∈ range x, wt x n * ∏ ℓ ∈ q.1, ind ψ n ℓ
            - (∑ n ∈ range x, wt x n) * ∏ ℓ ∈ q.1, recip ℓ)
          + (∑ n ∈ range x, wt x n * (List.map (fun q => q.2 * ∏ ℓ ∈ q.1, ind ψ n ℓ) L).sum
            - (∑ n ∈ range x, wt x n) *
              (List.map (fun q => q.2 * ∏ ℓ ∈ q.1, recip ℓ) L).sum) := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [show ∑ n ∈ range x, wt x n * (q.2 * ∏ ℓ ∈ q.1, ind ψ n ℓ) =
          q.2 * ∑ n ∈ range x, wt x n * ∏ ℓ ∈ q.1, ind ψ n ℓ from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring]
      ring
    rw [this]
    calc _ ≤ |q.2 * (∑ n ∈ range x, wt x n * ∏ ℓ ∈ q.1, ind ψ n ℓ
            - (∑ n ∈ range x, wt x n) * ∏ ℓ ∈ q.1, recip ℓ)| + _ := abs_add_le _ _
      _ ≤ |q.2| * B + (List.map (fun q => |q.2|) L).sum * B := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hq (abs_nonneg _)) ih'
      _ = _ := by ring

end Shoup.Sieve
