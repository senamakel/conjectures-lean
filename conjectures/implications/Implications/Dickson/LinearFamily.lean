import Implications.Dickson.Linear

/-!
# Dickson's conjecture for a finite family of linear forms

`infinite_linear_of_dickson`: if `a i > 0` for every `i ∈ s` and the forms `a i * n + b i`
satisfy the Schinzel condition (for every prime `p` some `n` makes no value divisible by `p`),
then Dickson's conjecture gives infinitely many `n` at which every form is `±` a prime. The
coprimality of `a i` and `b i` that `BunyakovskyCondition` needs follows from the Schinzel
condition: a prime dividing both would divide every value.
-/

open Polynomial

namespace Implications.Dickson

/-- Dickson's conjecture for the family of forms `a i * n + b i`, `i ∈ s`. -/
theorem infinite_linear_of_dickson (hD : DicksonConjecture) {ι : Type*} (s : Finset ι)
    (a b : ι → ℤ) (ha : ∀ i ∈ s, 0 < a i)
    (hS : ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i ∈ s, ¬ (p : ℤ) ∣ a i * n + b i) :
    {n : ℕ | ∀ i ∈ s, (a i * n + b i).natAbs.Prime}.Infinite := by
  classical
  have hrel : ∀ i ∈ s, IsRelPrime (b i) (a i) := by
    intro i hi d hdb hda
    by_contra hu
    have h1 : d.natAbs ≠ 1 := fun h => hu (Int.isUnit_iff_natAbs_eq.mpr h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨n, hn⟩ := hS p hp
    apply hn i hi
    have hpd' : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
    exact hpd'.trans (dvd_add (dvd_mul_of_dvd_left hda _) hdb)
  have H := hD (s.image fun i => C (a i) * X + C (b i)) ?_ ?_
  · rw [Set.infinite_coe_iff] at H
    convert H using 1
    ext n
    simp
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact linear_degree_bunyakovsky (ha i hi) (hrel i hi)
  · intro p hp
    obtain ⟨n, hn⟩ := hS p hp
    refine ⟨n, fun f hf => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    simpa using hn i hi

end Implications.Dickson
