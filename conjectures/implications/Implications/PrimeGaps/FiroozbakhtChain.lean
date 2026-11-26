import Mathlib

/-!
# A checked chain of primes from `127` to `65731`

`oppChain` is a list of 535 primes `127 = q₀ < q₁ < … < q_534 = 65731` with
`(q_{i+1} - q_i)² < q_i` at every step (`oppChainOK`, evaluated by `decide` in the kernel; no
`native_decide`). Primality of each entry is proved by `norm_num`. Walking the chain
(`exists_prime_sq_lt_of_chain`) gives, for every `m` with `127 ≤ m < 65731`, a prime `q > m` with
`(q - m)² < m`. The list was generated greedily (the largest admissible prime at each step).

This file uses no hypothesis: it is a finite computation about the primes.
-/

namespace Implications.PrimeGaps.Firoozbakht

/-- Part 0 of the chain. -/
def oppChain0 : List ℕ := [
  127, 137, 139, 149, 157, 167, 179, 191, 199, 211, 223, 233,
  241, 251, 263, 277, 293, 307, 317, 331, 349, 367, 383, 401,
  421, 439, 457, 467, 487, 509, 523, 541, 563, 577, 601, 619,
  643, 661, 683, 709, 733, 757, 773, 797, 823]

/-- Part 1 of the chain. -/
def oppChain1 : List ℕ := [
  839, 863, 887, 911, 941, 971, 997, 1021, 1051, 1069, 1097, 1129,
  1153, 1181, 1213, 1237, 1259, 1291, 1321, 1327, 1361, 1381, 1409, 1439,
  1471, 1499, 1531, 1567, 1601, 1637, 1669, 1709, 1747, 1787, 1823, 1861,
  1901, 1933, 1973, 2017, 2053, 2089, 2131, 2161, 2207]

/-- Part 2 of the chain. -/
def oppChain2 : List ℕ := [
  2251, 2297, 2341, 2389, 2437, 2477, 2521, 2557, 2593, 2633, 2683, 2731,
  2777, 2819, 2861, 2909, 2957, 3011, 3061, 3109, 3163, 3217, 3271, 3323,
  3373, 3413, 3469, 3527, 3583, 3637, 3697, 3739, 3797, 3853, 3911, 3967,
  4027, 4079, 4139, 4201, 4261, 4297, 4357, 4423, 4483]

/-- Part 3 of the chain. -/
def oppChain3 : List ℕ := [
  4549, 4603, 4663, 4729, 4793, 4861, 4919, 4987, 5051, 5119, 5189, 5261,
  5333, 5399, 5471, 5531, 5591, 5659, 5717, 5791, 5867, 5939, 6011, 6079,
  6151, 6229, 6301, 6379, 6451, 6529, 6607, 6679, 6737, 6803, 6883, 6961,
  7043, 7121, 7193, 7253, 7333, 7417, 7499, 7583, 7669]

/-- Part 4 of the chain. -/
def oppChain4 : List ℕ := [
  7753, 7841, 7927, 8011, 8093, 8179, 8269, 8353, 8443, 8527, 8609, 8699,
  8783, 8867, 8951, 9043, 9137, 9227, 9323, 9419, 9511, 9601, 9697, 9791,
  9887, 9973, 10069, 10169, 10267, 10357, 10457, 10559, 10657, 10753, 10853, 10957,
  11059, 11161, 11261, 11353, 11447, 11551, 11657, 11743, 11839]

/-- Part 5 of the chain. -/
def oppChain5 : List ℕ := [
  11941, 12049, 12157, 12263, 12373, 12479, 12589, 12697, 12809, 12919, 13009, 13121,
  13229, 13339, 13451, 13553, 13669, 13781, 13883, 13999, 14107, 14221, 14327, 14437,
  14557, 14669, 14783, 14897, 15017, 15139, 15259, 15377, 15497, 15619, 15739, 15859,
  15973, 16097, 16223, 16349, 16453, 16573, 16699, 16823, 16943]

/-- Part 6 of the chain. -/
def oppChain6 : List ℕ := [
  17053, 17183, 17299, 17419, 17539, 17669, 17791, 17923, 18049, 18181, 18313, 18443,
  18553, 18679, 18803, 18919, 19051, 19183, 19319, 19457, 19583, 19717, 19853, 19993,
  20129, 20269, 20411, 20551, 20693, 20809, 20947, 21089, 21227, 21347, 21493, 21617,
  21757, 21893, 22039, 22171, 22307, 22453, 22573, 22721, 22871]

/-- Part 7 of the chain. -/
def oppChain7 : List ℕ := [
  23021, 23167, 23311, 23459, 23609, 23761, 23911, 24061, 24203, 24337, 24481, 24631,
  24781, 24923, 25073, 25229, 25373, 25523, 25679, 25819, 25969, 26119, 26267, 26423,
  26573, 26731, 26893, 27043, 27197, 27361, 27509, 27673, 27827, 27983, 28123, 28289,
  28447, 28607, 28771, 28933, 29101, 29269, 29437, 29599, 29761]

/-- Part 8 of the chain. -/
def oppChain8 : List ℕ := [
  29927, 30097, 30269, 30431, 30593, 30763, 30937, 31091, 31267, 31397, 31573, 31741,
  31907, 32083, 32261, 32429, 32609, 32789, 32969, 33149, 33331, 33503, 33679, 33857,
  34039, 34217, 34381, 34549, 34729, 34913, 35099, 35281, 35461, 35617, 35803, 35983,
  36161, 36343, 36529, 36713, 36901, 37087, 37277, 37463, 37649]

/-- Part 9 of the chain. -/
def oppChain9 : List ℕ := [
  37831, 38011, 38201, 38393, 38569, 38749, 38933, 39119, 39313, 39511, 39709, 39901,
  40099, 40289, 40487, 40639, 40829, 41023, 41221, 41413, 41611, 41813, 42017, 42221,
  42409, 42611, 42797, 43003, 43207, 43411, 43613, 43801, 43997, 44203, 44389, 44587,
  44797, 45007, 45197, 45403, 45613, 45823, 46027, 46237, 46451]

/-- Part 10 of the chain. -/
def oppChain10 : List ℕ := [
  46663, 46877, 47093, 47309, 47521, 47737, 47951, 48163, 48371, 48589, 48809, 49019,
  49223, 49433, 49639, 49853, 50069, 50291, 50513, 50723, 50929, 51151, 51361, 51581,
  51803, 52027, 52253, 52457, 52673, 52901, 53129, 53359, 53569, 53791, 54013, 54217,
  54449, 54679, 54907, 55127, 55351, 55579, 55813, 56041, 56269]

/-- Part 11 of the chain. -/
def oppChain11 : List ℕ := [
  56503, 56737, 56963, 57193, 57427, 57653, 57881, 58111, 58337, 58573, 58789, 59029,
  59263, 59497, 59729, 59971, 60209, 60449, 60689, 60923, 61169, 61409, 61651, 61879,
  62119, 62351, 62597, 62827, 63073, 63317, 63559, 63809, 64037, 64283, 64513, 64763,
  65011, 65257, 65497, 65731]

/-- The checked chain of primes. -/
def oppChain : List ℕ :=
  oppChain0 ++ oppChain1 ++ oppChain2 ++ oppChain3 ++ oppChain4 ++ oppChain5 ++ oppChain6 ++ oppChain7 ++ oppChain8 ++ oppChain9 ++ oppChain10 ++ oppChain11

/-- The arithmetic check: consecutive entries increase and `(q - p)² < p`. -/
def oppChainOK : ℕ → List ℕ → Bool
  | _, [] => true
  | p, q :: l => decide (p < q) && decide ((q - p) ^ 2 < p) && oppChainOK q l

/-- The last entry of a chain. -/
def chainLast (p : ℕ) : List ℕ → ℕ
  | [] => p
  | q :: l => chainLast q l

theorem oppChain_head : oppChain = 127 :: oppChain.tail := by decide +kernel

theorem oppChain_ok : oppChainOK 127 oppChain.tail = true := by decide +kernel

theorem oppChain_last : chainLast 127 oppChain.tail = 65731 := by decide +kernel

theorem oppChain0_prime : ∀ q ∈ oppChain0, q.Prime := by
  simp only [oppChain0, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain1_prime : ∀ q ∈ oppChain1, q.Prime := by
  simp only [oppChain1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain2_prime : ∀ q ∈ oppChain2, q.Prime := by
  simp only [oppChain2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain3_prime : ∀ q ∈ oppChain3, q.Prime := by
  simp only [oppChain3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain4_prime : ∀ q ∈ oppChain4, q.Prime := by
  simp only [oppChain4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain5_prime : ∀ q ∈ oppChain5, q.Prime := by
  simp only [oppChain5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain6_prime : ∀ q ∈ oppChain6, q.Prime := by
  simp only [oppChain6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain7_prime : ∀ q ∈ oppChain7, q.Prime := by
  simp only [oppChain7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain8_prime : ∀ q ∈ oppChain8, q.Prime := by
  simp only [oppChain8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain9_prime : ∀ q ∈ oppChain9, q.Prime := by
  simp only [oppChain9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain10_prime : ∀ q ∈ oppChain10, q.Prime := by
  simp only [oppChain10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain11_prime : ∀ q ∈ oppChain11, q.Prime := by
  simp only [oppChain11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem oppChain_prime : ∀ q ∈ oppChain, q.Prime := by
  unfold oppChain
  simp only [List.forall_mem_append]
  exact ⟨oppChain0_prime, oppChain1_prime, oppChain2_prime, oppChain3_prime, oppChain4_prime, oppChain5_prime, oppChain6_prime, oppChain7_prime, oppChain8_prime, oppChain9_prime, oppChain10_prime, oppChain11_prime⟩

/-- Walking a checked chain. -/
theorem exists_prime_sq_lt_of_chain : ∀ (L : List ℕ) (p : ℕ), oppChainOK p L = true →
    (∀ q ∈ L, q.Prime) → ∀ m : ℕ, p ≤ m → m < chainLast p L →
    ∃ q : ℕ, q.Prime ∧ m < q ∧ (q - m) ^ 2 < m
  | [], p, _, _, m, hpm, hm => by simp [chainLast] at hm; omega
  | q :: l, p, hc, hl, m, hpm, hm => by
    simp only [oppChainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hpq, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl q (by simp)
    rcases lt_or_ge m q with h | h
    · refine ⟨q, hq, h, lt_of_le_of_lt (Nat.pow_le_pow_left (show q - m ≤ q - p by omega) 2) (by omega)⟩
    · exact exists_prime_sq_lt_of_chain l q hc' (fun e he => hl e (by simp [he])) m h
        (by simpa [chainLast] using hm)

/-- **Every `m` with `127 ≤ m < 65731` has a prime `q > m` with `(q - m)² < m`** (no hypothesis). -/
theorem exists_prime_sq_lt_small {m : ℕ} (h1 : 127 ≤ m) (h2 : m < 65731) :
    ∃ q : ℕ, q.Prime ∧ m < q ∧ (q - m) ^ 2 < m := by
  have hall := oppChain_prime
  rw [oppChain_head] at hall
  exact exists_prime_sq_lt_of_chain oppChain.tail 127 oppChain_ok
    (fun e he => hall e (List.mem_cons_of_mem _ he)) m h1 (by rw [oppChain_last]; exact h2)

end Implications.PrimeGaps.Firoozbakht
