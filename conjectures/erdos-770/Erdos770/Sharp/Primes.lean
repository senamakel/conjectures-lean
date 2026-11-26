import Erdos770.Basic

/-!
# Small primes: trial division, the primes below 3000, and bad primes `r < 3000`

* `isPrimeSmall`: trial division by `2 ≤ m < 55`, exact for `r < 3025`.
* `P3000`: the 430 primes below `3000`, checked against `isPrimeSmall` by kernel `decide`.
* `lt_17_of_small`: if a prime `r < 3000` with `r - 1 ∤ n` divides `iⁿ - 1` for every
  `2 ≤ i ≤ M`, then `M < 17`. The check `smallOK` (kernel `decide`) says that for every prime
  `r < 3000` and every prime `ℓ ∣ r - 1` some `2 ≤ i ≤ 17` has `i^((r-1)/ℓ) ≢ 1 (mod r)`; the
  worst case is `r = 1559`, `ℓ = 2`, whose least quadratic non-residue is `17`.
-/

namespace Erdos770.Sharp

/-- Trial division by `2 ≤ m < 55` with `m² ≤ r`. -/
def isPrimeSmall (r : ℕ) : Bool :=
  2 ≤ r && (List.range 55).all (fun m => m < 2 || r < m * m || r % m != 0)

theorem prime_of_isPrimeSmall {r : ℕ} (hr : r < 3025) (h : isPrimeSmall r = true) :
    r.Prime := by
  simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hp
  have hmf := Nat.minFac_sq_le_self (by omega) hp
  have hm2 : 2 ≤ r.minFac := (Nat.minFac_prime (by omega)).two_le
  have hdvd := Nat.minFac_dvd r
  have hm55 : r.minFac < 55 := by nlinarith
  rcases hall _ hm55 with (h | h) | h
  · omega
  · nlinarith
  · exact h (Nat.mod_eq_zero_of_dvd hdvd)

theorem isPrimeSmall_of_prime {r : ℕ} (hp : r.Prime) : isPrimeSmall r = true := by
  simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hp.two_le, fun m _ => ?_⟩
  by_cases hm : m < 2
  · exact Or.inl (Or.inl hm)
  by_cases hmm : r < m * m
  · exact Or.inl (Or.inr hmm)
  refine Or.inr fun h0 => ?_
  have hd : m ∣ r := Nat.dvd_of_mod_eq_zero h0
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · omega
  · subst h1; nlinarith

/-- The primes below `3000`. -/
def P3000 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
  617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
  727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
  829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
  947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
  1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
  1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283,
  1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
  1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
  1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619,
  1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747,
  1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877,
  1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003,
  2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
  2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267,
  2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377,
  2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503,
  2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
  2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
  2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861,
  2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999]

theorem P3000_eq : P3000 = (List.range 3000).filter isPrimeSmall := by decide +kernel

theorem mem_P3000 {r : ℕ} : r ∈ P3000 ↔ r < 3000 ∧ r.Prime := by
  rw [P3000_eq, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, prime_of_isPrimeSmall (by omega) h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, isPrimeSmall_of_prime h2⟩

/-- For every prime `r < 3000` and prime `ℓ ∣ r - 1`, some `2 ≤ i ≤ 17` is not an `ℓ`-th power
residue mod `r`. -/
def smallOK : Bool :=
  P3000.all fun r => P3000.all fun l =>
    (r - 1) % l != 0 || (List.range 18).any fun i => 2 ≤ i && i ^ ((r - 1) / l) % r != 1

theorem smallOK_eq : smallOK = true := by decide +kernel

theorem lt_17_of_small {n M r : ℕ} (hn : 1 ≤ n) (hr : r.Prime) (hr3000 : r < 3000)
    (hnd : ¬ (r - 1) ∣ n) (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) : M < 17 := by
  have := Fact.mk hr
  have hr3 : 3 ≤ r := by
    rcases hr.eq_two_or_odd' with h | h
    · subst h; exact absurd (one_dvd n) (by simpa using hnd)
    · have := hr.two_le; rcases h with ⟨k, hk⟩; omega
  set d := Nat.gcd n (r - 1) with hd
  have hdr : d ∣ r - 1 := Nat.gcd_dvd_right _ _
  have hdne : d ≠ r - 1 := fun h => hnd (h ▸ Nat.gcd_dvd_left _ _)
  obtain ⟨c, hc⟩ := hdr
  have hc2 : c ≠ 1 := by rintro rfl; exact hdne (by omega)
  have hc0 : c ≠ 0 := by rintro rfl; omega
  set l := c.minFac with hl
  have hlp : l.Prime := Nat.minFac_prime hc2
  obtain ⟨e, he⟩ := Nat.minFac_dvd c
  have he' : c = l * e := he
  have hl1 : (r - 1) % l = 0 := by
    rw [hc, he']; exact Nat.mod_eq_zero_of_dvd ⟨d * e, by ring⟩
  have hdiv : (r - 1) / l = d * e := by
    rw [hc, he', show d * (l * e) = l * (d * e) by ring,
      Nat.mul_div_cancel_left _ hlp.pos]
  have hlr : l < 3000 := by
    have : l ≤ c := Nat.minFac_le (by omega)
    have : c ≤ r - 1 := by
      rw [hc]; exact Nat.le_mul_of_pos_left _ (Nat.gcd_pos_of_pos_left _ hn)
    omega
  have hok := smallOK_eq
  simp only [smallOK, List.all_eq_true] at hok
  have := hok r (mem_P3000.2 ⟨hr3000, hr⟩) l (mem_P3000.2 ⟨hlr, hlp⟩)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h | ⟨i, hi18, hi2, hi⟩
  · exact absurd hl1 h
  by_contra hM
  push Not at hM
  apply hi
  have hri := hdvd i hi2 (by omega)
  have hiu : (i : ZMod r) ^ n = 1 := (dvd_pow_sub_one_iff (by omega)).1 hri
  have hi0 : (i : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hiu
    exact zero_ne_one hiu
  have hfer : (i : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one hi0
  have hgd : (i : ZMod r) ^ d = 1 := pow_gcd_eq_one.2 ⟨hiu, hfer⟩
  have h1 : (i : ZMod r) ^ ((r - 1) / l) = 1 := by rw [hdiv, pow_mul, hgd, one_pow]
  have h2 : ((i ^ ((r - 1) / l) : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by push_cast; exact h1
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  rw [h2, Nat.mod_eq_of_lt hr.one_lt]

end Erdos770.Sharp
