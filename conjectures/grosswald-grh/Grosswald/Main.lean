import Grosswald.Tail
import Grosswald.Covered
import Grosswald.First31
import Grosswald.Direct.Main

/-!
# Grosswald's conjecture under GRH

For a prime `p > 10^13` with no prime primitive root below `√p - 2`, GRH gives `NoSieve p`
(`not_sieveIneq_of_GRH`). Then:

* `p ≥ 10^47`: the sieve with `S = ∅` contradicts it (`sieveIneq_of_large`);
* `p < 10^47`: `ω(p-1) ≤ 30`, and Algorithm 1 (`checkNode_sound`, assembled in
  `Grosswald/Covered.lean`) covers every `n = ω(p-1) ∈ [1, 30]`.

The range `409 < p ≤ 10^13` is checked prime by prime (`Grosswald.Direct.direct_range`).
-/

namespace Grosswald

open Alg
open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- `p < 10^47` forces `ω(p - 1) ≤ 30`. -/
lemma card_primeFactors_le_30 {p : ℕ} (hp : p < 10 ^ 47) : (p - 1).primeFactors.card ≤ 30 := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨hL, hprod⟩ := Run.first31_ok
  set L := firstPrimesAvoiding 31 []
  obtain ⟨h1, h2, h3, h4⟩ := LOk_spec hL
  obtain ⟨F, hF, hFc⟩ := Finset.exists_subset_card_eq (show 31 ≤ (p - 1).primeFactors.card by omega)
  have hp1 : p - 1 ≠ 0 := by
    intro h0; rw [h0] at hF
    simp at hF; rw [hF] at hFc; simp at hFc
  have hc' : F.card = L.toFinset.card := by rw [hFc, List.toFinset_card_of_nodup h2, h1]
  have hdom : ∀ q ∈ F, q ∉ L.toFinset → ∀ l ∈ L.toFinset, l < q := by
    intro q hq hqL l hl
    exact h4 q (Nat.mem_primeFactors.mp (hF hq)).1 (by simp) (by simpa using hqL) l (by simpa using hl)
  have hle := Combi.prod_le_prod_of_dominates hc' hdom
  rw [List.prod_toFinset _ h2, List.map_id'] at hle
  have hFle : ∏ q ∈ F, q ≤ ∏ q ∈ (p - 1).primeFactors, q :=
    Finset.prod_le_prod_of_subset_of_one_le hF fun q hq _ =>
      (Nat.mem_primeFactors.mp hq).1.one_lt.le
  have hdvd : ∏ q ∈ (p - 1).primeFactors, q ≤ p - 1 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hp1) (Nat.prod_primeFactors_dvd _)
  omega

/-- **GRH part**: every prime `p > 10^13` has a prime primitive root below `√p - 2`. -/
theorem prime_primitive_root_of_GRH_above (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → 10000000000000 < p → HasSmallPrimePrimitiveRoot p := by
  intro p hp hbig
  by_contra hno
  have hns : NoSieve p := fun S hS hδ => not_sieveIneq_of_GRH hGRH hp (by omega) hno hS hδ
  by_cases hlarge : 10 ^ 47 ≤ p
  · have h := sieveIneq_of_large hlarge
    have hδ : deltaOf ∅ = 1 := by simp [deltaOf]
    refine hns ∅ (Finset.empty_subset _) (by rw [hδ]; norm_num) ?_
    rw [hδ, Finset.card_empty]
    exact h
  · rw [not_le] at hlarge
    have h30 := card_primeFactors_le_30 hlarge
    have h2 : 2 ∣ p - 1 := by
      have hodd := hp.odd_of_ne_two (by omega)
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m, by omega⟩
    have h1 : 1 ≤ (p - 1).primeFactors.card := by
      apply Finset.card_pos.mpr
      exact ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, by omega⟩⟩
    refine hno (covered_root h1 h30 p ⟨hp, hbig, rfl, ?_, by simp⟩ hns)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]; exact h2

/-- MTT Theorem 1, GRH part, with MTT's threshold `2.5·10^15`. -/
theorem prime_primitive_root_of_GRH_large (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → 2500000000000000 < p → HasSmallPrimePrimitiveRoot p :=
  fun p hp h => prime_primitive_root_of_GRH_above hGRH p hp (by omega)

/-- **Grosswald's conjecture under GRH.** -/
theorem grosswald_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : GrosswaldStatement := by
  intro p hp h409
  by_cases hsmall : p < Direct.directEnd
  · exact Direct.direct_range p hp h409 hsmall
  · obtain ⟨q, hq, hlt, hord⟩ :=
      prime_primitive_root_of_GRH_above hGRH p hp (by unfold Direct.directEnd at hsmall; omega)
    exact ⟨q, hq.pos, hlt, hord⟩

/-- The finite range alone, without GRH: `VerifiedUpTo 10^13`. -/
theorem verifiedUpTo_10_13 : VerifiedUpTo 10000000000000 := fun p hp h1 h2 =>
  Direct.direct_range p hp h1 (by unfold Direct.directEnd; omega)

end Grosswald
