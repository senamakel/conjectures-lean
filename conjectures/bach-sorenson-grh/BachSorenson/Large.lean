import BachSorenson.Statement
import BachSorenson.Orthogonality
import BachSorenson.PrimePowers

/-!
# Step 5: one modulus, given the numerical inequality

Let `x = ⌊c (q log q)²⌋`. If no prime `p < x` lies in the class of `a`, then every `n < x` with
`n ≡ a` and `Λ(n) ≠ 0` is a prime power that is not prime, so `T(a, x) ≤ ppSum x ≤ ppBound x`.
With `φ(q) ≤ q`, step 3 then gives

`x/2 − √x/20 − 3 − ω(q) log x ≤ q (B(q, x) + ppBound x)`,

which `NumericOK c q` rules out.
-/

namespace BachSorenson

open ArithmeticFunction Finset Erdos985

/-- `x = ⌊c (q log q)²⌋`. -/
noncomputable def xOf (c : ℝ) (q : ℕ) : ℕ := ⌊c * ((q : ℝ) * Real.log q) ^ 2⌋₊

/-- The numerical condition at modulus `q`: the GRH lower bound for `φ(q) T(a, x)` exceeds the
upper bound coming from prime powers. -/
def NumericOK (c : ℝ) (q : ℕ) : Prop :=
  144 ≤ xOf c q ∧
    (q : ℝ) * (charBound q (xOf c q) + ppBound (xOf c q)) + √(xOf c q : ℝ) / 20 + 3
        + q.primeFactors.card * Real.log (xOf c q)
      < (xOf c q : ℝ) / 2

lemma classSum_le_ppSum {q : ℕ} (a x : ℕ)
    (hno : ∀ p < x, p.Prime → ¬ p ≡ a [MOD q]) :
    classSum q (a : ZMod q) x ≤ ppSum x := by
  unfold classSum ppSum
  rw [sum_filter, sum_filter]
  refine sum_le_sum fun n hn => ?_
  have hnx := mem_range.1 hn
  obtain ⟨hw0, hw1⟩ := Ankeny.weight_mem hnx
  have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  by_cases ha : (n : ZMod q) = a
  · have hnp : ¬ n.Prime := fun hp => hno n hnx hp ((ZMod.natCast_eq_natCast_iff n a q).1 ha)
    simp only [ha, hnp, not_false_eq_true, ite_true]
    nlinarith
  · simp only [ha, ite_false]
    split_ifs <;> linarith

theorem exists_prime_of_numericOK (hGRH : DirichletLNonvanishingRightOfHalf) {c : ℝ} {q : ℕ}
    (hq : 2 ≤ q) (hnum : NumericOK c q) (a : ℕ) (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ p < xOf c q := by
  have : NeZero q := ⟨by omega⟩
  set x := xOf c q with hxdef
  by_contra hcon
  have hno : ∀ p < x, p.Prime → ¬ p ≡ a [MOD q] := fun p hp hpp hpa => hcon ⟨p, hpp, hpa, hp⟩
  have hunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hlow := totient_mul_classSum_ge hGRH hunit x hnum.1
  have hup := classSum_le_ppSum a x hno
  have hx2 : 2 ≤ x := le_trans (by norm_num) hnum.1
  have hpp := ppSum_le x hx2
  have hpp0 := ppSum_nonneg x
  have hB0 := charBound_nonneg q x (by omega) (by omega)
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφ1 : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.2 (by omega : 0 < q)
  have h1 : (q.totient : ℝ) * classSum q a x ≤ q * ppBound x := by
    calc (q.totient : ℝ) * classSum q a x ≤ q.totient * ppSum x := by gcongr
      _ ≤ q * ppBound x := by
          apply mul_le_mul hφ hpp hpp0 (by positivity)
  have h2 : ((q.totient : ℝ) - 1) * charBound q x ≤ q * charBound q x := by
    gcongr; linarith
  have h3 := hnum.2
  rw [← hxdef] at h3
  nlinarith

lemma xOf_le (c : ℝ) (q : ℕ) (hc : 0 ≤ c) : (xOf c q : ℝ) ≤ c * ((q : ℝ) * Real.log q) ^ 2 :=
  Nat.floor_le (by positivity)

/-- From the numerical inequality at every `q ≥ 2` to the Bach–Sorenson statement. -/
theorem bachSorenson_of_numericOK (hGRH : DirichletLNonvanishingRightOfHalf) {c : ℝ} (hc : 0 ≤ c)
    {q a : ℕ} (hq : 2 ≤ q) (hnum : NumericOK c q) (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * ((q : ℝ) * Real.log q) ^ 2 := by
  obtain ⟨p, hp, hpa, hpx⟩ := exists_prime_of_numericOK hGRH hq hnum a ha
  refine ⟨p, hp, hpa, ?_⟩
  have : (p : ℝ) < xOf c q := by exact_mod_cast hpx
  linarith [xOf_le c q hc]

end BachSorenson
