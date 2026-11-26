import Erdos770.Core
import Erdos770.Sharp.Primes

/-!
# The direct check for `2 ≤ n < 216`

For each such `n`, with `B = 3` (`n < 8`) or `B = 17` (`n ≥ 8`), the kernel checks (`finOK_all`):
take `g = gcd(2ⁿ - 1, 3ⁿ - 1)`, divide out every prime `p < 3000` with `p - 1 ∣ n` (`stripQ`),
then take the gcd with `iⁿ - 1` for `4 ≤ i ≤ B` (`gcdFrom`); the result is `1`.
The stripped primes come from `P256`, the primes below `256`.

`gcdUpTo_eq_one_of_finOK`: this gives `gcd(2ⁿ - 1, …, Mⁿ - 1) = 1` for every `M ≥ max(P n, B)`.
A bad prime `r` divides `g`; it is not one of the stripped primes `p` (those are `≤ P n ≤ M < r`),
so it survives the stripping and divides the final value `1`.
-/

namespace Erdos770.Sharp

/-- The primes below `256`. -/
def P256 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

theorem P256_prime : P256.all isPrimeSmall = true := by decide +kernel

theorem prime_of_mem_P256 {p : ℕ} (hp : p ∈ P256) : p.Prime := by
  have h := P256_prime
  rw [List.all_eq_true] at h
  have hlt : p < 3025 := by
    have : ∀ q ∈ P256, q < 3025 := by decide
    exact this p hp
  exact prime_of_isPrimeSmall hlt (h p hp)

/-- The product of the primes `p < 256` with `p ≤ n + 1` and `p - 1 ∣ n`. -/
def Qn (n : ℕ) : ℕ := (P256.filter fun p => p ≤ n + 1 && n % (p - 1) == 0).prod

/-- Divide `g` by `gcd(g, q)` repeatedly (`f` times at most). -/
def stripQ (q : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | f + 1, g => if Nat.gcd g q = 1 then g else stripQ q f (g / Nat.gcd g q)

/-- `gcd(g, iⁿ - 1, (i+1)ⁿ - 1, …)` with `c` terms. -/
def gcdFrom (n g i c : ℕ) : ℕ := ((List.range c).map fun t => (i + t) ^ n - 1).foldl Nat.gcd g

/-- The lower bound used for `⌈5 log² n⌉` in the direct check. -/
def finB (n : ℕ) : ℕ := if n < 8 then 3 else 17

def finOK (n : ℕ) : Bool :=
  gcdFrom n (stripQ (Qn n) 64 (Nat.gcd (2 ^ n - 1) (3 ^ n - 1))) 4 (finB n - 3) == 1

theorem finOK_all : ∀ n < 216, 2 ≤ n → finOK n = true := by decide +kernel


lemma dvd_stripQ {r q : ℕ} (hr : r.Prime) (hq : ¬ r ∣ q) :
    ∀ f g, r ∣ g → r ∣ stripQ q f g
  | 0, g, h => h
  | f + 1, g, h => by
    unfold stripQ
    split_ifs with h1
    · exact h
    · apply dvd_stripQ hr hq f
      have hd : ¬ r ∣ Nat.gcd g q := fun h' => hq (h'.trans (Nat.gcd_dvd_right _ _))
      have : g = Nat.gcd g q * (g / Nat.gcd g q) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      rw [this] at h
      exact ((Nat.Prime.dvd_mul hr).1 h).resolve_left hd

lemma dvd_foldl_gcd {r : ℕ} : ∀ (l : List ℕ) (g : ℕ), r ∣ g → (∀ a ∈ l, r ∣ a) →
    r ∣ l.foldl Nat.gcd g
  | [], g, h, _ => h
  | a :: l, g, h, hl => by
    rw [List.foldl_cons]
    exact dvd_foldl_gcd l _ (Nat.dvd_gcd h (hl a (by simp)))
      fun b hb => hl b (by simp [hb])

lemma dvd_gcdFrom {r n : ℕ} (c g i : ℕ) (h : r ∣ g) (ht : ∀ t < c, r ∣ (i + t) ^ n - 1) :
    r ∣ gcdFrom n g i c := by
  apply dvd_foldl_gcd _ _ h
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨t, ht', rfl⟩ := ha
  exact ht t (List.mem_range.1 ht')

theorem gcdUpTo_eq_one_of_finOK {n M : ℕ} (hn : 1 ≤ n) (h : finOK n = true)
    (hBM : finB n ≤ M) (hPM : P n ≤ M) : gcdUpTo n M = 1 := by
  have hB3 : 3 ≤ finB n := by unfold finB; split_ifs <;> omega
  by_contra hg
  obtain ⟨r, hr, hMr, -, hdvd⟩ := exists_bad_prime hn (by omega) hg
  have hg0 : r ∣ Nat.gcd (2 ^ n - 1) (3 ^ n - 1) :=
    Nat.dvd_gcd (hdvd 2 le_rfl (by omega)) (hdvd 3 (by norm_num) (by omega))
  have hQ : ¬ r ∣ Qn n := by
    intro hQ
    rw [Qn, (Nat.Prime.prime hr).dvd_prod_iff] at hQ
    obtain ⟨p, hp, hrp⟩ := hQ
    rw [List.mem_filter] at hp
    obtain ⟨hpP, hpc⟩ := hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpc
    have hpp := prime_of_mem_P256 hpP
    have hrp' : r = p := (Nat.prime_dvd_prime_iff_eq hr hpp).1 hrp
    have := le_P hn hpp (Nat.dvd_of_mod_eq_zero hpc.2)
    omega
  have h1 := dvd_stripQ hr hQ 64 _ hg0
  have h2 := dvd_gcdFrom (n := n) (finB n - 3) _ 4 h1 fun t ht =>
    hdvd (4 + t) (by omega) (by omega)
  have hfin : gcdFrom n (stripQ (Qn n) 64 (Nat.gcd (2 ^ n - 1) (3 ^ n - 1))) 4 (finB n - 3) = 1 := by
    simpa [finOK] using h
  rw [hfin] at h2
  exact hr.one_lt.ne' (Nat.dvd_one.1 h2)

end Erdos770.Sharp
