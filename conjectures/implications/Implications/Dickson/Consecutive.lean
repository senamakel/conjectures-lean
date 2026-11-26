import Implications.Dickson.Linear

/-!
# Dickson's conjecture: every admissible pattern occurs as a run of consecutive primes

Under `DicksonConjecture`, for every admissible finite set `hs` of shifts and every bound `H`
with `hs ⊆ [0, H]`, there are infinitely many `n` such that every `n + h` (`h ∈ hs`) is prime and
every other `n + j` with `j ≤ H` is composite (`infinite_consecutive_of_dickson`).

This is the standard deduction (see e.g. the remark after the prime `k`-tuples conjecture in
Hardy–Littlewood's *Partitio Numerorum III*, and its use for consecutive primes in arithmetic
progression; unverified). The construction:

* for every position `j ≤ H` with `j ∉ hs` pick its own prime `q j > H` (here the
  `(H + 1 + j)`-th prime, so the `q j` are distinct);
* by the Chinese remainder theorem pick `a` with `q j ∣ a + j` for each such `j`, and let
  `M = ∏ q j`;
* apply Dickson's conjecture to the forms `M t + (a + h)`, `h ∈ hs`. Since `|h - j| ≤ H < q j`,
  no `q j` divides `a + h`, which gives both `gcd(M, a + h) = 1` (irreducibility) and the
  Schinzel condition at the primes dividing `M` (take `t = 0`). At any other prime `p`, `M` is
  invertible mod `p` and admissibility of `hs` at `p` gives a good `t`;
* for `n = M t + a` with `t ≥ 2`, each unwanted `n + j` is a multiple of `q j` larger than `q j`.

The second half turns such a run into statements about `Nat.nth Nat.Prime`: for the pattern
`0, d, 2d, …, (k - 1) d` with `d = k!`, which is admissible, the primes `n + i d` are the
`(π(n) - 1 + i)`-th primes (`infinite_consecutive_ap_of_dickson`).
-/

open Polynomial Finset

namespace Implications.Dickson

/-- A finite set of shifts is admissible if it does not cover every residue class modulo any
prime. -/
def Admissible (hs : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ hs, ¬ p ∣ r + h

/-- A set of fewer than `p` shifts misses a residue class modulo the prime `p`. -/
theorem exists_not_dvd_of_card_lt {p : ℕ} (hp : p.Prime) (hs : Finset ℕ) (hc : hs.card < p) :
    ∃ r : ℕ, ∀ h ∈ hs, ¬ p ∣ r + h := by
  classical
  haveI := Fact.mk hp
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := hs.image (fun h => -(h : ZMod p))) (t := Finset.univ)
    (by rw [Finset.card_univ, ZMod.card]; exact (Finset.card_image_le).trans_lt hc)
  refine ⟨e.val, fun h hh hd => he ?_⟩
  rw [← ZMod.natCast_eq_zero_iff] at hd
  push_cast at hd
  rw [ZMod.natCast_zmod_val] at hd
  exact Finset.mem_image.2 ⟨h, hh, (eq_neg_of_add_eq_zero_left hd).symm⟩

/-- **Dickson's conjecture gives consecutive prime patterns.** For an admissible set of shifts
`hs ⊆ [0, H]`, there are infinitely many `n` such that `n + h` is prime for every `h ∈ hs` and
`n + j` is not prime for every other `j ≤ H`. -/
theorem infinite_consecutive_of_dickson (hD : DicksonConjecture) (hs : Finset ℕ) (H : ℕ)
    (hH : ∀ h ∈ hs, h ≤ H) (hadm : Admissible hs) :
    {n : ℕ | (∀ h ∈ hs, (n + h).Prime) ∧ ∀ j ≤ H, j ∉ hs → ¬ (n + j).Prime}.Infinite := by
  classical
  set J := (range (H + 1)).filter (· ∉ hs) with hJ
  set q : ℕ → ℕ := fun j => Nat.nth Nat.Prime (H + 1 + j) with hq
  have hqp : ∀ j, (q j).Prime := fun j => Nat.prime_nth_prime _
  have hqH : ∀ j, H < q j := fun j => by
    have := Nat.add_two_le_nth_prime (H + 1 + j)
    simp only [hq]
    omega
  have hqinj : Function.Injective q := fun i j hij => by
    have := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    omega
  set M := ∏ j ∈ J, q j with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun j _ => (hqp j).pos
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun j => q j - j) q J
    (fun j _ => (hqp j).ne_zero)
    (fun i _ j _ hij => (Nat.coprime_primes (hqp i) (hqp j)).2 (hqinj.ne hij))
  have hmemJ : ∀ j, j ∈ J ↔ j ≤ H ∧ j ∉ hs := fun j => by
    simp only [hJ, mem_filter, mem_range]
    omega
  have hdvdJ : ∀ j ∈ J, q j ∣ a + j := fun j hj => by
    have hjq : j ≤ q j := by have := hqH j; have := ((hmemJ j).1 hj).1; omega
    have h1 : a + j ≡ q j - j + j [MOD q j] := Nat.ModEq.add_right j (ha j hj)
    rw [Nat.sub_add_cancel hjq] at h1
    exact (Nat.modEq_zero_iff_dvd).1 (h1.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
  have hndvd : ∀ j ∈ J, ∀ h ∈ hs, ¬ q j ∣ a + h := fun j hj h hh hd => by
    obtain ⟨hjH, hjs⟩ := (hmemJ j).1 hj
    have hhH := hH h hh
    have hne : h ≠ j := fun e => hjs (e ▸ hh)
    have hqj := hqH j
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h2 : q j ∣ (a + j) - (a + h) := Nat.dvd_sub (hdvdJ j hj) hd
      have h3 := Nat.le_of_dvd (by omega) h2
      omega
    · have h2 : q j ∣ (a + h) - (a + j) := Nat.dvd_sub hd (hdvdJ j hj)
      have h3 := Nat.le_of_dvd (by omega) h2
      omega
  have hqM : ∀ j ∈ J, q j ∣ M := fun j hj => Finset.dvd_prod_of_mem q hj
  have hcop : ∀ h ∈ hs, Nat.Coprime (a + h) M := fun h hh =>
    Nat.Coprime.prod_right fun j hj =>
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hqp j)).2 (hndvd j hj h hh))
  let fs : Finset ℤ[X] := hs.image (fun h => C (M : ℤ) * X + C ((a + h : ℕ) : ℤ))
  have Hd := hD fs ?_ ?_
  · rw [Set.infinite_coe_iff] at Hd
    apply Set.infinite_of_forall_exists_gt
    intro b
    obtain ⟨t, ht, htb⟩ := Hd.exists_gt (b + 1)
    have htM : t ≤ M * t := Nat.le_mul_of_pos_left t hM0
    refine ⟨M * t + a, ⟨?_, ?_⟩, by omega⟩
    · intro h hh
      have := ht _ (mem_image_of_mem _ hh)
      simp only [eval_add, eval_mul, eval_C, eval_X] at this
      rw [natAbs_linear] at this
      rwa [add_assoc]
    · intro j hjH hjs hpr
      have hjJ : j ∈ J := (hmemJ j).2 ⟨hjH, hjs⟩
      have hd : q j ∣ M * t + a + j := by
        rw [add_assoc]
        exact dvd_add (dvd_mul_of_dvd_left (hqM j hjJ) t) (hdvdJ j hjJ)
      have he := (Nat.prime_dvd_prime_iff_eq (hqp j) hpr).1 hd
      have hMq := Nat.le_of_dvd hM0 (hqM j hjJ)
      have h2 : M * 2 ≤ M * t := Nat.mul_le_mul_left _ (by omega)
      have := (hqp j).pos
      omega
  · intro f hf
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hf
    exact linear_degree_bunyakovsky (by exact_mod_cast hM0)
      (Nat.isCoprime_iff_coprime.mpr (hcop h hh)).isRelPrime
  · intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨j, hj, hpj⟩ := (Nat.prime_iff.mp hp).exists_mem_finset_dvd hpM
      have hpq := (Nat.prime_dvd_prime_iff_eq hp (hqp j)).1 hpj
      refine ⟨0, ?_⟩
      intro f hf
      obtain ⟨h, hh, rfl⟩ := mem_image.1 hf
      simp only [eval_add, eval_mul, eval_C, eval_X, Nat.cast_zero, mul_zero, zero_add]
      rw [Int.natCast_dvd_natCast, hpq]
      exact hndvd j hj h hh
    · obtain ⟨r, hr⟩ := hadm p hp
      haveI := Fact.mk hp
      have hMne : (M : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      refine ⟨(((r : ZMod p) - (a : ZMod p)) * (M : ZMod p)⁻¹).val, ?_⟩
      intro f hf
      obtain ⟨h, hh, rfl⟩ := mem_image.1 hf
      simp only [eval_add, eval_mul, eval_C, eval_X]
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      have hkey : (M : ZMod p) * (((r : ZMod p) - a) * (M : ZMod p)⁻¹) + (a + h)
          = ((r + h : ℕ) : ZMod p) := by
        rw [mul_comm ((r : ZMod p) - a), ← mul_assoc, mul_inv_cancel₀ hMne]
        push_cast
        ring
      rw [hkey, ZMod.natCast_eq_zero_iff]
      exact hr h hh

/-- Across a gap with no primes, the prime-counting function goes up by exactly one. -/
theorem count_add_gap {m g : ℕ} (hm : m.Prime) (hg : 0 < g)
    (hgap : ∀ x, 0 < x → x < g → ¬ (m + x).Prime) :
    Nat.count Nat.Prime (m + g) = Nat.count Nat.Prime m + 1 := by
  rw [Nat.count_add]
  congr 1
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rw [Nat.count_succ', Nat.count_of_forall_not]
  · simp [hm]
  · intro x hx
    exact hgap (x + 1) (by omega) (by omega)

/-- The pattern `0, k!, 2·k!, …, (k - 1)·k!` is admissible. -/
theorem admissible_ap (k : ℕ) :
    Admissible ((range k).image (fun i => i * k.factorial)) := by
  intro p hp
  by_cases hpk : p ≤ k
  · refine ⟨1, ?_⟩
    intro h hh hd
    obtain ⟨i, -, rfl⟩ := mem_image.1 hh
    have h1 : p ∣ i * k.factorial := dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hpk) i
    have h2 : p ∣ 1 := (Nat.dvd_add_left h1).1 hd
    exact hp.ne_one (Nat.dvd_one.1 h2)
  · exact exists_not_dvd_of_card_lt hp _
      ((card_image_le).trans_lt (by rw [card_range]; omega))

/-- **Consecutive primes in arithmetic progression from Dickson.** For every `k ≥ 1` there are
infinitely many primes `n` such that, with `c = Nat.count Nat.Prime n` (so `n` is the `c`-th
prime, counting from `0`), the `(c + i)`-th prime is `n + i · k!` for every `i < k`. -/
theorem infinite_consecutive_ap_of_dickson (hD : DicksonConjecture) (k : ℕ) (hk : 0 < k) :
    {n : ℕ | n.Prime ∧ ∀ i < k,
      Nat.nth Nat.Prime (Nat.count Nat.Prime n + i) = n + i * k.factorial}.Infinite := by
  classical
  set d := k.factorial with hd
  have hd0 : 0 < d := Nat.factorial_pos k
  set hs := (range k).image (fun i => i * d) with hhs
  have hH : ∀ h ∈ hs, h ≤ (k - 1) * d := fun h hh => by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hh
    exact Nat.mul_le_mul_right _ (by rw [mem_range] at hi; omega)
  refine (infinite_consecutive_of_dickson hD hs ((k - 1) * d) hH (admissible_ap k)).mono ?_
  rintro n ⟨hpr, hcomp⟩
  have hpr' : ∀ i < k, (n + i * d).Prime := fun i hi =>
    hpr _ (mem_image_of_mem _ (mem_range.2 hi))
  have hn : n.Prime := by simpa using hpr' 0 hk
  refine ⟨hn, ?_⟩
  have hcount : ∀ i < k, Nat.count Nat.Prime (n + i * d) = Nat.count Nat.Prime n + i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [show n + (i + 1) * d = (n + i * d) + d by ring,
        count_add_gap (hpr' i (by omega)) hd0, ih (by omega)]
      · ring
      · intro x hx0 hxd hxp
        refine hcomp (i * d + x) ?_ ?_ (by rwa [← add_assoc])
        · have : (i + 1) * d ≤ (k - 1) * d := Nat.mul_le_mul_right _ (by omega)
          rw [add_mul, one_mul] at this
          omega
        · intro hmem
          obtain ⟨i', -, hi'⟩ := mem_image.1 hmem
          have h1 : i * d < i' * d := by omega
          have h2 : i' * d < (i + 1) * d := by rw [add_mul, one_mul]; omega
          have h3 := Nat.lt_of_mul_lt_mul_right h1
          have h4 := Nat.lt_of_mul_lt_mul_right h2
          omega
  intro i hi
  rw [← hcount i hi, Nat.nth_count (hpr' i hi)]

end Implications.Dickson
