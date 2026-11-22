import Grosswald.Tail
import Grosswald.Alg
import Grosswald.Run.Roots
import Grosswald.Run.N12
import Grosswald.Run.N14
import Grosswald.Run.N13A1
import Grosswald.Run.N13A2
import Grosswald.Run.N13B
import Grosswald.Run.N13C
import Grosswald.Run.N13D

/-!
# Grosswald's conjecture under GRH (MTT Theorem 1)

For a prime `p > 2.5·10^15` with no prime primitive root below `√p - 2`, GRH gives
`NoSieve p` (`not_sieveIneq_of_GRH`). Then:

* `p ≥ 10^47`: the sieve with `S = ∅` contradicts it (`sieveIneq_of_large`);
* `p < 10^47`: `ω(p-1) ≤ 30`, and Algorithm 1 (`checkNode_sound`) covers every
  `n = ω(p-1) ∈ [1, 30]`, either by an empty interval (all `n ∉ {12, 13, 14}`) or by recursive
  splitting and enumeration (`n = 12, 13, 14`).

The range `409 < p ≤ 2.5·10^15` is the hypothesis `VerifiedUpTo 2500000000000000`.
-/

namespace Grosswald

open Alg

/-- The primes of a node all have a small prime primitive root (given `NoSieve`). -/
def Covered (n : ℕ) (X Y : List ℕ) : Prop :=
  ∀ p, InClass n X Y p → NoSieve p → HasSmallPrimePrimitiveRoot p

lemma covered_of_check {n : ℕ} {X Y : List ℕ} (h : checkNode n 40 X Y = true) : Covered n X Y :=
  checkNode_sound n 40 X Y h

lemma covered_split {n : ℕ} {X Y : List ℕ} (q : ℕ) (h1 : Covered n (q :: X) Y)
    (h2 : Covered n X (q :: Y)) : Covered n X Y := by
  intro p ⟨hpr, hbig, hn, hX, hY⟩ hns
  by_cases hq : q ∣ p - 1
  · refine h1 p ⟨hpr, hbig, hn, fun r hr => ?_, hY⟩ hns
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; exact hq
    · exact hX r h
  · refine h2 p ⟨hpr, hbig, hn, hX, fun r hr => ?_⟩ hns
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; exact hq
    · exact hY r h

lemma covered_13 : Covered 13 [2] [] := by
  obtain ⟨h3, h5, h7⟩ := Run.n13_small
  refine covered_split 3 ?_ (covered_of_check h3)
  refine covered_split 5 ?_ (covered_of_check h5)
  refine covered_split 7 ?_ (covered_of_check h7)
  refine covered_split 11 ?_ (covered_of_check Run.n13_D)
  refine covered_split 13 ?_ (covered_of_check Run.n13_C)
  refine covered_split 17 ?_ (covered_of_check Run.n13_B)
  exact covered_split 19 (covered_of_check Run.n13_A1) (covered_of_check Run.n13_A2)

lemma covered_root {n : ℕ} (h1 : 1 ≤ n) (h30 : n ≤ 30) : Covered n [2] [] := by
  by_cases h12 : n = 12
  · subst h12; exact covered_of_check Run.n12
  by_cases h13 : n = 13
  · subst h13; exact covered_13
  by_cases h14 : n = 14
  · subst h14; exact covered_of_check Run.n14
  apply covered_of_check
  have h := Run.roots_ok
  rw [List.all_eq_true] at h
  apply h
  simp only [List.mem_filter, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq]
  omega

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
    Finset.prod_le_prod_of_subset_of_one_le' hF fun q hq _ =>
      (Nat.mem_primeFactors.mp hq).1.one_lt.le
  have hdvd : ∏ q ∈ (p - 1).primeFactors, q ≤ p - 1 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hp1) (Nat.prod_primeFactors_dvd _)
  omega

/-- **MTT Theorem 1, GRH part**: every prime `p > 2.5·10^15` has a prime primitive root below
`√p - 2`. -/
theorem prime_primitive_root_of_GRH_large (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → 2500000000000000 < p → HasSmallPrimePrimitiveRoot p := by
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

/-- **Grosswald's conjecture under GRH**, given the computation of Cohen, Oliveira e Silva and
Trudgian for `409 < p ≤ 2.5·10^15`. -/
theorem grosswald_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hcomp : VerifiedUpTo 2500000000000000) : GrosswaldStatement := by
  intro p hp h409
  by_cases hsmall : p ≤ 2500000000000000
  · exact hcomp p hp h409 hsmall
  · obtain ⟨q, hq, hlt, hord⟩ := prime_primitive_root_of_GRH_large hGRH p hp (by omega)
    exact ⟨q, hq.pos, hlt, hord⟩

end Grosswald
