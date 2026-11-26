import Grosswald.Direct.Sound
import GrosswaldCompute.Leaf

/-!
# Soundness of the leaf check `GrosswaldCompute.leafOk`

`leafOk_sound`: if `leafOk X Y (∏ X) k0 cnt = true`, `X` is a list of distinct primes and
`p = k ∏ X + 1` is a prime with `k ∈ [k0, k0 + cnt)` and no `q ∈ Y` dividing `p - 1`, then `p`
has a prime primitive root `g < √p - 2`. The argument is the one of `Grosswald/Direct/Sound.lean`
for consecutive `k` instead of odd `n`.
-/

namespace Grosswald.Leaf

open GrosswaldCompute Grosswald.Direct

lemma progOkK_spec (q L : ℕ) (fl : Array (List ℕ)) :
    ∀ (f j : ℕ), progOkK q L fl j f = true → ∀ t, t < f → j + t * q < L →
      q ∈ fl.getD (j + t * q) []
  | 0, _, _, t, ht, _ => by omega
  | f + 1, j, h, t, ht, hL => by
    have hjL : j < L := lt_of_le_of_lt (Nat.le_add_right _ _) hL
    simp only [progOkK, hjL, if_true, Bool.and_eq_true, List.contains_iff_mem] at h
    rcases t with _ | t
    · simpa using h.1
    · have e : j + q + t * q = j + (t + 1) * q := by ring
      have := progOkK_spec q L fl f (j + q) h.2 t (by omega) (by omega)
      rwa [e] at this

lemma progAllK_spec (c L : ℕ) (cw : Array ℕ) (fl : Array (List ℕ)) :
    ∀ (k lo : ℕ), progAllK c L cw fl lo k = true → ∀ q, lo ≤ q → q < lo + k →
      cw.getD q 1 = 0 →
      (q - c % q) % q < q ∧ (c + (q - c % q) % q) % q = 0 ∧
        progOkK q L fl ((q - c % q) % q) (L / q + 1) = true
  | 0, _, _, q, h1, h2, _ => by omega
  | k + 1, lo, h, q, h1, h2, hcw => by
    simp only [progAllK, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · have h1 := h.1
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true,
        decide_eq_true_eq] at h1
      rcases h1 with h1 | ⟨⟨h3, h4⟩, h5⟩
      · exact absurd hcw h1
      · exact ⟨h3, h4, h5⟩
    · exact progAllK_spec c L cw fl k (lo + 1) h.2 q h1 (by omega) hcw

lemma coveredK {c L B : ℕ} {cw : Array ℕ} {fl : Array (List ℕ)}
    (hcw : cwOk cw 2 (B - 2) = true) (hpa : progAllK c L cw fl 2 (B - 2) = true)
    {q i : ℕ} (hq : q.Prime) (hqB : q < B) (hi : i < L) (hd : q ∣ c + i) : q ∈ fl.getD i [] := by
  obtain ⟨hj0, hj0d, hprog⟩ :=
    progAllK_spec c L cw fl _ 2 hpa q hq.two_le (by omega) (cw_prime hcw hq hqB)
  set j0 := (q - c % q) % q
  have hd0 : q ∣ c + j0 := Nat.dvd_of_mod_eq_zero hj0d
  have hij : j0 ≤ i := by
    by_contra hlt
    push Not at hlt
    have : q ∣ j0 - i := by
      have e : c + j0 = (c + i) + (j0 - i) := by omega
      rw [e] at hd0
      exact (Nat.dvd_add_right hd).mp hd0
    have := Nat.le_of_dvd (by omega) this
    omega
  have hdiv : q ∣ i - j0 := by
    have e : c + i = (c + j0) + (i - j0) := by omega
    rw [e] at hd
    exact (Nat.dvd_add_right hd0).mp hd
  obtain ⟨t, ht⟩ := hdiv
  have hiq : i = j0 + t * q := by rw [mul_comm t q]; omega
  have htf : t < L / q + 1 := by
    have : t * q ≤ L := by omega
    have : t ≤ L / q := (Nat.le_div_iff_mul_le hq.pos).mpr this
    omega
  have := progOkK_spec q L fl _ j0 hprog t htf (by omega)
  rwa [← hiq] at this

lemma isPrimeTD_prime {q : ℕ} (h : isPrimeTD q = true) : q.Prime := by
  simp only [isPrimeTD, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hm := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hlt : q.minFac < q := by
    have := Nat.minFac_le (show 0 < q by omega)
    rcases Nat.eq_or_lt_of_le this with h | h
    · exact absurd (h ▸ hm) hnp
    · exact h
  rcases hall _ hlt with (h | h) | h
  · exact absurd hm.two_le (by omega)
  · rw [sq] at hsq; omega
  · exact h (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q))

lemma gPrimes_prime : ∀ q ∈ gPrimes, q.Prime := by
  intro q hq
  simp only [gPrimes, List.mem_filter] at hq
  exact isPrimeTD_prime hq.2

lemma lucasAny_spec (p m s : ℕ) (ts : List ℕ) : ∀ gs : List ℕ, lucasAny p m s ts gs = true →
    ∃ g ∈ gs, g + 3 ≤ s ∧ lucas p m g ts = true
  | [], h => by simp [lucasAny] at h
  | g :: gs, h => by
    simp only [lucasAny, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨g, List.mem_cons_self, h1, h2⟩
    · obtain ⟨g', hg', h3⟩ := lucasAny_spec p m s ts gs h
      exact ⟨g', List.mem_cons_of_mem _ hg', h3⟩

lemma fermat2 {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : Nat.powMod 2 (p - 1) p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← zmod_pow_eq_one_iff' hp.two_le]
  apply ZMod.pow_card_sub_one_eq_one
  intro h0
  rw [show ((2 : ℕ) : ZMod p) = 2 by norm_num, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num,
    ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (by norm_num) h0
  omega

/-- One `k`. -/
lemma candK_sound {X Y fl : List ℕ} {P B s k : ℕ} (h : candK X Y P B s k fl = true)
    (hXp : ∀ x ∈ X, x.Prime) (hP : P = X.prod) (hp : (k * P + 1).Prime) (h3 : 3 ≤ k * P + 1)
    (hY : ∀ q ∈ Y, ¬ q ∣ k * P) (hk0 : 0 < k) (hkB : k < B * B) (hk64 : k < 2 ^ 64)
    (hs : s ≤ Nat.sqrt (k * P + 1))
    (hfl : ∀ l, l.Prime → l < B → l ∣ k → l ∈ fl) :
    Grosswald.HasSmallPrimePrimitiveRoot (k * P + 1) := by
  set p := k * P + 1 with hpdef
  have hpm : p - 1 = P * k := by rw [hpdef]; rw [mul_comm]; omega
  simp only [candK, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, ← hpdef] at h
  rcases h with (((⟨q, hqY, hq⟩ | hF) | ⟨hrange, hl⟩) | ⟨⟨h1, h2⟩, h4⟩)
  · exact absurd (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hq) P) (hY q hqY)
  · exact absurd (fermat2 hp h3) hF
  · have hfs2 : ∀ q ∈ fl, 2 ≤ q := fun q hq => (hrange q hq).1
    obtain ⟨hr0, hrd, hrnd, hrl⟩ := foldl_divOut fl hfs2 k hk0 hk64
    set r := fl.foldl (fun r q => divOut q r 64) k with hr
    have hrbig : ∀ l, l.Prime → l ∣ r → B ≤ l := by
      intro l hl hlr
      by_contra hlt
      exact hrnd l (hfl l hl (by omega) (hlr.trans hrd)) hlr
    have hrprime : 1 < r → r.Prime := by
      intro h1
      by_contra hnp
      have hmf := Nat.minFac_prime (show r ≠ 1 by omega)
      have hB1 := hrbig _ hmf (Nat.minFac_dvd r)
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hrle : r ≤ k := Nat.le_of_dvd hk0 hrd
      have : B * B ≤ r := le_trans (Nat.mul_le_mul hB1 hB1) (by rw [← sq]; exact hsq)
      omega
    set ts := X ++ (if 1 < r then r :: fl else fl) with hts
    have hall : ∀ l, l.Prime → l ∣ p - 1 → l ∈ ts := by
      intro l hl hld
      rw [hpm] at hld
      rcases (Nat.Prime.dvd_mul hl).mp hld with hlP | hlk
      · rw [hP] at hlP
        obtain ⟨x, hx, hlx⟩ := (Prime.dvd_prod_iff (Nat.Prime.prime hl)).mp hlP
        have := (Nat.prime_dvd_prime_iff_eq hl (hXp x hx)).mp hlx
        exact List.mem_append_left _ (this ▸ hx)
      · apply List.mem_append_right
        by_cases hlB : l < B
        · have := hfl l hl hlB hlk
          split_ifs
          · exact List.mem_cons_of_mem _ this
          · exact this
        · push Not at hlB
          have hlr : l ∣ r := by
            apply hrl l hl _ hlk
            intro q hq hlq
            have := Nat.le_of_dvd (by have := hfs2 q hq; omega) hlq
            have := (hrange q hq).2
            omega
          have hr1 : 1 < r := by
            have := Nat.le_of_dvd hr0 hlr; have := hl.two_le; omega
          have := (Nat.prime_dvd_prime_iff_eq hl (hrprime hr1)).mp hlr
          rw [if_pos hr1, this]
          exact List.mem_cons_self
    obtain ⟨g, hg, hgs, hlu⟩ := lucasAny_spec p (p - 1) s ts gPrimes hl
    refine ⟨g, gPrimes_prime g hg, ?_, orderOf_of_lucas hp.two_le hlu hall⟩
    have : g < Grosswald.xOf p := by unfold Grosswald.xOf; omega
    exact Grosswald.lt_sqrt_sub_two_of_lt_xOf this
  · exfalso
    rcases hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h4) with h | h <;> omega

lemma candAll_spec (X Y : List ℕ) (P B s c : ℕ) (fl : Array (List ℕ)) :
    ∀ (k i0 : ℕ), candAll X Y P B s c fl i0 k = true → ∀ i, i0 ≤ i → i < i0 + k →
      candK X Y P B s (c + i) (fl.getD i []) = true
  | 0, _, _, i, h1, h2 => by omega
  | k + 1, i0, h, i, h1, h2 => by
    simp only [candAll, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact candAll_spec X Y P B s c fl k (i0 + 1) h.2 i h1 (by omega)

/-- What a leaf guarantees for the prime `p = k P + 1`. -/
def LeafGood (X Y : List ℕ) (P k : ℕ) : Prop :=
  (k * P + 1).Prime → 3 ≤ k * P + 1 → (∀ q ∈ Y, ¬ q ∣ k * P) → k < 2 ^ 64 →
    Grosswald.HasSmallPrimePrimitiveRoot (k * P + 1)

lemma blockOk_sound {X Y : List ℕ} {P c L : ℕ} (h : blockOk X Y P c L = true)
    (hXp : ∀ x ∈ X, x.Prime) (hP : P = X.prod) (hc : 0 < c) :
    ∀ k, c ≤ k → k < c + L → LeafGood X Y P k := by
  intro k h1 h2 hp h3 hY hk64
  unfold blockOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hcw, hpa⟩, hca⟩ := h
  set B := Nat.sqrt (c + L) + 1
  have hkB : k < B * B := lt_trans h2 (Nat.lt_succ_sqrt (c + L))
  have hi := candAll_spec X Y P B _ c _ L 0 hca (k - c) (Nat.zero_le _) (by omega)
  rw [show c + (k - c) = k by omega] at hi
  refine candK_sound hi hXp hP hp h3 hY (by omega) hkB hk64 ?_ ?_
  · apply Nat.sqrt_le_sqrt
    have : c * P ≤ k * P := Nat.mul_le_mul_right _ h1
    omega
  · intro l hl hlB hlk
    exact coveredK hcw hpa hl hlB (by omega) (by rw [show c + (k - c) = k by omega]; exact hlk)

lemma leafBlocks_sound {X Y : List ℕ} {P : ℕ} (hXp : ∀ x ∈ X, x.Prime) (hP : P = X.prod) :
    ∀ (f c cnt : ℕ), leafBlocks X Y P c cnt f = true → 0 < c →
      ∀ k, c ≤ k → k < c + cnt → LeafGood X Y P k
  | 0, c, cnt, h, _ => by simp [leafBlocks] at h
  | f + 1, c, cnt, h, hc => by
    intro k h1 h2
    unfold leafBlocks at h
    split_ifs at h with hle
    · exact blockOk_sound h hXp hP hc k h1 h2
    · simp only [Bool.and_eq_true] at h
      by_cases hk : k < c + blockLen
      · exact blockOk_sound h.1 hXp hP hc k h1 hk
      · exact leafBlocks_sound hXp hP f _ _ h.2 (by omega) k (by omega) (by omega)

theorem leafOk_sound {X Y : List ℕ} {P k0 cnt : ℕ} (h : leafOk X Y P k0 cnt = true)
    (hXp : ∀ x ∈ X, x.Prime) (hP : P = X.prod) :
    ∀ k, k0 ≤ k → k < k0 + cnt → LeafGood X Y P k := by
  simp only [leafOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact leafBlocks_sound hXp hP _ k0 cnt h.2 h.1

end Grosswald.Leaf
