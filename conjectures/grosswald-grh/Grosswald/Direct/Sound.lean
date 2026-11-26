import Grosswald.Analytic
import GrosswaldCompute

/-!
# Soundness of the segmented checker `GrosswaldCompute.segOk`

If `segOk a L = true`, every prime `p = a + 2 i` (`i < L`) has a primitive root
`g < √p - 2` (`segOk_sound`), and the same for runs of segments (`segsOk_sound`).
The untrusted sieves only produce data; the argument uses the checks alone:

* `cwOk`: every `q < B` with `cw[q] ≠ 0` has a proper divisor, so every prime `q < B` has
  `cw[q] = 0`;
* `progAll`: for each odd such `q`, every `i < L` with `q ∣ a - 1 + 2 i` has a composite witness
  `wit[i] ≠ 0` or `q ∈ fl[i]`;
* `numOk`: a witness really divides `n`, or Lucas' test passes against `2 :: fl[i]` and the
  cofactor `r` left after dividing them out. As every listed number is in `[2, B)` and
  `B² > n`, `r` is `1` or a prime, so the list holds every prime factor of `n - 1`.
-/

namespace Grosswald.Direct

open GrosswaldCompute

/-! ### `cwOk` -/

lemma cwOk_spec (cw : Array ℕ) : ∀ (k lo : ℕ), cwOk cw lo k = true → ∀ q, lo ≤ q → q < lo + k →
    cw.getD q 1 = 0 ∨ (1 < cw.getD q 1 ∧ cw.getD q 1 < q ∧ q % cw.getD q 1 = 0)
  | 0, _, _, q, h1, h2 => by omega
  | k + 1, lo, h, q, h1, h2 => by
    simp only [cwOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rcases h.1 with h | ⟨⟨h3, h4⟩, h5⟩
      · exact Or.inl h
      · exact Or.inr ⟨h3, h4, h5⟩
    · exact cwOk_spec cw k (lo + 1) h.2 q h1 (by omega)

lemma cw_prime {cw : Array ℕ} {B : ℕ} (h : cwOk cw 2 (B - 2) = true) {q : ℕ} (hq : q.Prime)
    (hqB : q < B) : cw.getD q 1 = 0 := by
  rcases cwOk_spec cw _ 2 h q hq.two_le (by omega) with h | ⟨h1, h2, h3⟩
  · exact h
  · exfalso
    have hd : cw.getD q 1 ∣ q := Nat.dvd_of_mod_eq_zero h3
    rcases hq.eq_one_or_self_of_dvd _ hd with h | h <;> omega

/-! ### `progOk` and `progAll` -/

lemma progOk_spec (q L : ℕ) (wit : Array ℕ) (fl : Array (List ℕ)) :
    ∀ (f j : ℕ), progOk q L wit fl j f = true → ∀ t, t < f → j + t * q < L →
      wit.getD (j + t * q) 0 ≠ 0 ∨ q ∈ fl.getD (j + t * q) []
  | 0, _, _, t, ht, _ => by omega
  | f + 1, j, h, t, ht, hL => by
    have hjL : j < L := lt_of_le_of_lt (Nat.le_add_right _ _) hL
    simp only [progOk, hjL, if_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      List.contains_iff_mem] at h
    rcases t with _ | t
    · simpa using h.1
    · have := progOk_spec q L wit fl f (j + q) h.2 t (by omega) (by
        have : j + q + t * q = j + (t + 1) * q := by ring
        omega)
      have e : j + q + t * q = j + (t + 1) * q := by ring
      rwa [e] at this

lemma progAll_spec (a L : ℕ) (cw wit : Array ℕ) (fl : Array (List ℕ)) :
    ∀ (k lo : ℕ), progAll a L cw wit fl lo k = true → ∀ q, lo ≤ q → q < lo + k → q % 2 = 1 →
      cw.getD q 1 = 0 →
      start (a - 1) q < q ∧ (a - 1 + 2 * start (a - 1) q) % q = 0 ∧
        progOk q L wit fl (start (a - 1) q) (L / q + 1) = true
  | 0, _, _, q, h1, h2, _, _ => by omega
  | k + 1, lo, h, q, h1, h2, hodd, hcw => by
    simp only [progAll, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · have h1 := h.1
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true,
        decide_eq_true_eq] at h1
      rcases h1 with (h1 | h1) | ⟨⟨h3, h4⟩, h5⟩
      · omega
      · exact absurd hcw h1
      · exact ⟨h3, h4, h5⟩
    · exact progAll_spec a L cw wit fl k (lo + 1) h.2 q h1 (by omega) hodd hcw

/-- Every odd prime `q < B` dividing `a - 1 + 2 i` is in `fl[i]`, unless `wit[i] ≠ 0`. -/
lemma covered {a L B : ℕ} {cw wit : Array ℕ} {fl : Array (List ℕ)} (ha : 1 ≤ a)
    (hcw : cwOk cw 2 (B - 2) = true) (hpa : progAll a L cw wit fl 3 (B - 3) = true)
    {q i : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqB : q < B) (hi : i < L) (hd : q ∣ a - 1 + 2 * i) :
    wit.getD i 0 ≠ 0 ∨ q ∈ fl.getD i [] := by
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have h3 : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨hj0, hj0d, hprog⟩ :=
    progAll_spec a L cw wit fl _ 3 hpa q h3 (by omega) hodd (cw_prime hcw hq hqB)
  set j0 := start (a - 1) q
  have hcop : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).mpr hq2
  have hd0 : q ∣ a - 1 + 2 * j0 := Nat.dvd_of_mod_eq_zero hj0d
  -- `i ≡ j0 (mod q)`
  have hij : j0 ≤ i := by
    by_contra hlt
    push Not at hlt
    have : q ∣ 2 * (j0 - i) := by
      have e : a - 1 + 2 * j0 = (a - 1 + 2 * i) + 2 * (j0 - i) := by omega
      rw [e] at hd0
      exact (Nat.dvd_add_right hd).mp hd0
    have := hcop.dvd_of_dvd_mul_left this
    have := Nat.le_of_dvd (by omega) this
    omega
  have hdiv : q ∣ i - j0 := by
    have : q ∣ 2 * (i - j0) := by
      have e : a - 1 + 2 * i = (a - 1 + 2 * j0) + 2 * (i - j0) := by omega
      rw [e] at hd
      exact (Nat.dvd_add_right hd0).mp hd
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨t, ht⟩ := hdiv
  have hiq : i = j0 + t * q := by rw [mul_comm t q]; omega
  have htf : t < L / q + 1 := by
    have : t * q ≤ L := by omega
    have : t ≤ L / q := (Nat.le_div_iff_mul_le (by omega)).mpr this
    omega
  have := progOk_spec q L wit fl _ j0 hprog t htf (by omega)
  rwa [← hiq] at this

/-! ### Dividing out -/

lemma divOut_dvd (q : ℕ) : ∀ (f r : ℕ), divOut q r f ∣ r
  | 0, r => by simp [divOut]
  | f + 1, r => by
    unfold divOut
    split_ifs with h
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact (divOut_dvd q f (r / q)).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h.1))
    · exact dvd_rfl

lemma divOut_pos (q : ℕ) : ∀ (f r : ℕ), 0 < r → 0 < divOut q r f
  | 0, r, h => by simpa [divOut] using h
  | f + 1, r, h => by
    unfold divOut
    split_ifs with h'
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
      have hq : q ∣ r := Nat.dvd_of_mod_eq_zero h'.1
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq; omega)
      exact divOut_pos q f _ (Nat.div_pos (Nat.le_of_dvd h hq) hq0)
    · exact h

lemma not_dvd_divOut {q : ℕ} (hq : 2 ≤ q) : ∀ (f r : ℕ), 0 < r → r < 2 ^ f → ¬ q ∣ divOut q r f
  | 0, r, h0, h => by simp at h; omega
  | f + 1, r, h0, h => by
    unfold divOut
    split_ifs with h'
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
      have hqr : q ∣ r := Nat.dvd_of_mod_eq_zero h'.1
      obtain ⟨c, rfl⟩ := hqr
      rw [Nat.mul_div_cancel_left _ (by omega)]
      have hc0 : 0 < c := by rcases Nat.eq_zero_or_pos c with h | h <;> simp_all
      apply not_dvd_divOut hq f c hc0
      rw [pow_succ] at h
      nlinarith
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and] at h'
      intro hd
      exact h' (Nat.mod_eq_zero_of_dvd hd) h0

lemma dvd_divOut {q l : ℕ} (hl : l.Prime) (hlq : ¬ l ∣ q) : ∀ (f r : ℕ), l ∣ r → l ∣ divOut q r f
  | 0, r, h => by simpa [divOut] using h
  | f + 1, r, h => by
    unfold divOut
    split_ifs with h'
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h'.1
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hc; omega)
      apply dvd_divOut hl hlq f
      rw [hc, Nat.mul_div_cancel_left _ hq0]
      rw [hc] at h
      exact (hl.dvd_mul.mp h).resolve_left hlq
    · exact h

/-- Facts about `fs.foldl (fun r q => divOut q r 64) m`. -/
lemma foldl_divOut (fs : List ℕ) (hfs : ∀ q ∈ fs, 2 ≤ q) : ∀ m, 0 < m → m < 2 ^ 64 →
    let r := fs.foldl (fun r q => divOut q r 64) m
    0 < r ∧ r ∣ m ∧ (∀ q ∈ fs, ¬ q ∣ r) ∧ ∀ l, l.Prime → (∀ q ∈ fs, ¬ l ∣ q) → l ∣ m → l ∣ r := by
  induction fs with
  | nil => intro m h0 _; simp [h0]
  | cons q fs ih =>
    intro m h0 h64
    simp only [List.foldl_cons]
    have hq := hfs q (by simp)
    have hfs' : ∀ q ∈ fs, 2 ≤ q := fun q hq => hfs q (by simp [hq])
    set m' := divOut q m 64 with hm'
    have h0' : 0 < m' := divOut_pos q 64 m h0
    have hle : m' ≤ m := Nat.le_of_dvd h0 (divOut_dvd q 64 m)
    obtain ⟨r0, rd, rnd, rl⟩ := ih hfs' m' h0' (by omega)
    refine ⟨r0, rd.trans (divOut_dvd q 64 m), ?_, ?_⟩
    · intro q' hq' hd
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact not_dvd_divOut hq 64 m h0 h64 (hd.trans rd)
      · exact rnd q' hq' hd
    · intro l hl hlq hlm
      exact rl l hl (fun q' hq' => hlq q' (by simp [hq'])) (dvd_divOut hl (hlq q (by simp)) 64 m hlm)

/-! ### `findRoot` and Lucas -/

lemma findRoot_spec (n m s : ℕ) (ts : List ℕ) : ∀ (f g : ℕ), findRoot n m s ts g f = true →
    ∃ g', g ≤ g' ∧ g' + 3 ≤ s ∧ lucas n m g' ts = true
  | 0, g, h => by simp [findRoot] at h
  | f + 1, g, h => by
    simp only [findRoot, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact ⟨g, le_rfl, h1, h2⟩
    · obtain ⟨g', hg', h3, h4⟩ := findRoot_spec n m s ts f (g + 1) h2
      exact ⟨g', by omega, h3, h4⟩

lemma zmod_pow_eq_one_iff' {n : ℕ} (hn : 2 ≤ n) (g e : ℕ) :
    (g : ZMod n) ^ e = 1 ↔ Nat.powMod g e n = 1 := by
  rw [Nat.powMod_def, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq,
    Nat.one_mod_eq_one.mpr (by omega)]

lemma orderOf_of_lucas {n g : ℕ} {ts : List ℕ} (hn : 2 ≤ n) (h : lucas n (n - 1) g ts = true)
    (hts : ∀ l, l.Prime → l ∣ n - 1 → l ∈ ts) : orderOf (g : ZMod n) = n - 1 := by
  simp only [lucas, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨hall, hf⟩ := h
  apply orderOf_eq_of_pow_and_pow_div_prime
  · exact (zmod_pow_eq_one_iff' hn _ _).mpr hf
  · intro l hl hld
    rw [ne_eq, zmod_pow_eq_one_iff' hn]
    rcases hall l (hts l hl hld) with h | h
    · exact absurd (Nat.mod_eq_zero_of_dvd hld) h
    · exact h

/-! ### One number -/

lemma numOk_sound {B s n w : ℕ} {fl : List ℕ} (h : numOk B s n w fl = true) (hp : n.Prime)
    (hn64 : n < 2 ^ 64) (hB : n < B * B) (hs : s ≤ Nat.sqrt n)
    (hfl : w = 0 → ∀ l, l.Prime → l ≠ 2 → l < B → l ∣ n - 1 → l ∈ fl) :
    Grosswald.HasSmallPrimitiveRoot n := by
  have hn2 := hp.two_le
  unfold numOk at h
  split_ifs at h with hw
  · exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases hp.eq_one_or_self_of_dvd w (Nat.dvd_of_mod_eq_zero h3) with h | h <;> omega
  · simp only [bne_iff_ne, ne_eq, not_not] at hw
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨hrange, hfind⟩ := h
    set fs := 2 :: fl with hfs
    have hfs2 : ∀ q ∈ fs, 2 ≤ q := fun q hq => (hrange q hq).1
    obtain ⟨hr0, hrd, hrnd, hrl⟩ := foldl_divOut fs hfs2 (n - 1) (by omega) (by omega)
    set r := fs.foldl (fun r q => divOut q r 64) (n - 1) with hr
    -- every prime factor `< B` of `n - 1` is in `fs`
    have hsmall : ∀ l, l.Prime → l < B → l ∣ n - 1 → l ∈ fs := by
      intro l hl hlB hld
      by_cases h2 : l = 2
      · simp [hfs, h2]
      · exact List.mem_cons_of_mem _ (hfl hw l hl h2 hlB hld)
    -- the cofactor has only prime factors `≥ B`, hence is `1` or prime
    have hrbig : ∀ l, l.Prime → l ∣ r → B ≤ l := by
      intro l hl hlr
      by_contra hlt
      exact hrnd l (hsmall l hl (by omega) (hlr.trans hrd)) hlr
    have hrprime : 1 < r → r.Prime := by
      intro h1
      by_contra hnp
      have hmf := Nat.minFac_prime (show r ≠ 1 by omega)
      have hB1 := hrbig _ hmf (Nat.minFac_dvd r)
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hrle : r ≤ n - 1 := Nat.le_of_dvd (by omega) hrd
      have : B * B ≤ r := by nlinarith
      omega
    set ts := if 1 < r then r :: fs else fs with hts
    have hall : ∀ l, l.Prime → l ∣ n - 1 → l ∈ ts := by
      intro l hl hld
      by_cases hlB : l < B
      · have := hsmall l hl hlB hld
        rw [hts]; split_ifs
        · exact List.mem_cons_of_mem _ this
        · exact this
      · push Not at hlB
        have hlr : l ∣ r := by
          apply hrl l hl _ hld
          intro q hq hlq
          have := Nat.le_of_dvd (by have := hfs2 q hq; omega) hlq
          have := (hrange q hq).2
          omega
        have hr1 : 1 < r := by
          have := Nat.le_of_dvd hr0 hlr; have := hl.two_le; omega
        have := (Nat.prime_dvd_prime_iff_eq hl (hrprime hr1)).mp hlr
        rw [hts, if_pos hr1, this]
        exact List.mem_cons_self
    obtain ⟨g, hg2, hgs, hl⟩ := findRoot_spec n (n - 1) s ts s 2 hfind
    refine ⟨g, by omega, ?_, orderOf_of_lucas hn2 hl hall⟩
    have : g < Grosswald.xOf n := by unfold Grosswald.xOf; omega
    exact Grosswald.lt_sqrt_sub_two_of_lt_xOf this

/-! ### Segments -/

lemma numAll_spec (a B s : ℕ) (wit : Array ℕ) (fl : Array (List ℕ)) :
    ∀ (k i0 : ℕ), numAll a B s wit fl i0 k = true → ∀ i, i0 ≤ i → i < i0 + k →
      numOk B s (a + 2 * i) (wit.getD i 0) (fl.getD i []) = true
  | 0, _, _, i, h1, h2 => by omega
  | k + 1, i0, h, i, h1, h2 => by
    simp only [numAll, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact numAll_spec a B s wit fl k (i0 + 1) h.2 i h1 (by omega)

theorem segOk_sound {a L : ℕ} (h : segOk a L = true) (ha : 1 ≤ a) (h64 : a + 2 * L < 2 ^ 64)
    {i : ℕ} (hi : i < L) (hp : (a + 2 * i).Prime) : Grosswald.HasSmallPrimitiveRoot (a + 2 * i) := by
  unfold segOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hcw, hpa⟩, hnum⟩ := h
  set B := Nat.sqrt (a + 2 * L) + 1 with hB
  have hBB : a + 2 * i < B * B := by
    have := Nat.lt_succ_sqrt (a + 2 * L)
    have : a + 2 * i < a + 2 * L := by omega
    rw [hB]; nlinarith
  apply numOk_sound (numAll_spec _ _ _ _ _ L 0 hnum i (Nat.zero_le _) (by omega)) hp (by omega)
    hBB (Nat.sqrt_le_sqrt (by omega))
  intro hw l hl hl2 hlB hld
  have hd : l ∣ a - 1 + 2 * i := by
    have e : a + 2 * i - 1 = a - 1 + 2 * i := by omega
    rwa [e] at hld
  rcases covered ha hcw hpa hl hl2 hlB hi hd with h | h
  · exact absurd hw h
  · exact h

theorem segsOk_sound {L : ℕ} : ∀ (S a : ℕ), segsOk L a S = true → 1 ≤ a → a + 2 * L * S < 2 ^ 64 →
    ∀ p, p.Prime → a ≤ p → p < a + 2 * L * S → (p - a) % 2 = 0 →
      Grosswald.HasSmallPrimitiveRoot p
  | 0, a, _, _, _, p, _, h1, h2, _ => by omega
  | S + 1, a, h, ha, h64, p, hp, h1, h2, hpar => by
    simp only [segsOk, Bool.and_eq_true] at h
    by_cases hlt : p < a + 2 * L
    · have e : p = a + 2 * ((p - a) / 2) := by omega
      rw [e] at hp ⊢
      exact segOk_sound h.1 ha (by nlinarith) (by omega) hp
    · exact segsOk_sound S (a + 2 * L) h.2 (by omega) (by nlinarith) p hp (by omega) (by nlinarith)
        (by omega)

/-- Range version for odd `a`: every prime in `[a, a + 2 L S)` has a small primitive root. -/
theorem range_sound {L S a : ℕ} (h : segsOk L a S = true) (ha : a % 2 = 1) (ha3 : 3 ≤ a)
    (h64 : a + 2 * L * S < 2 ^ 64) :
    ∀ p, p.Prime → a ≤ p → p < a + 2 * L * S → Grosswald.HasSmallPrimitiveRoot p := by
  intro p hp h1 h2
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  exact segsOk_sound S a h (by omega) h64 p hp h1 h2 (by omega)

end Grosswald.Direct

namespace Grosswald.Direct

open GrosswaldCompute

theorem segsOk_append {L : ℕ} : ∀ (S1 a S2 b : ℕ), segsOk L a S1 = true → segsOk L b S2 = true →
    b = a + 2 * L * S1 → segsOk L a (S1 + S2) = true
  | 0, a, S2, b, _, h2, hb => by simp only [Nat.mul_zero, Nat.add_zero] at hb; subst hb; simpa using h2
  | S1 + 1, a, S2, b, h1, h2, hb => by
    simp only [segsOk, Bool.and_eq_true] at h1
    rw [show S1 + 1 + S2 = (S1 + S2) + 1 by omega]
    simp only [segsOk, Bool.and_eq_true]
    exact ⟨h1.1, segsOk_append S1 (a + 2 * L) S2 b h1.2 h2 (by rw [hb]; ring)⟩

end Grosswald.Direct
