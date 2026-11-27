import Lean

namespace AntihydraParity

def orbit (seed : Nat) : Nat → Nat
  | 0 => seed
  | n + 1 => (3 * orbit seed n) / 2

/-- Lifting the seed by a multiple of a power of two preserves the residue
needed to read the prefix of parity bits. -/
theorem orbit_shift (seed k n i : Nat) (hi : i ≤ n) :
    orbit (seed + 2 ^ n * k) i = orbit seed i + 2 ^ (n - i) * (3 ^ i * k) := by
  induction i with
  | zero => simp [orbit]
  | succ i ih =>
    have h : n - i = n - (i + 1) + 1 := by omega
    simp only [orbit, ih (by omega : i ≤ n), h, Nat.pow_succ]
    rw [show 3 * (orbit seed i + 2 ^ (n - (i + 1)) * 2 * (3 ^ i * k)) =
        3 * orbit seed i + 2 * (2 ^ (n - (i + 1)) * (3 ^ i * 3 * k)) by rw [Nat.mul_add]; congr 1; ac_rfl]
    exact Nat.add_mul_div_left _ _ (by decide)

theorem prefix_parity_shift (seed k n i : Nat) (hi : i < n) :
    orbit (seed + 2 ^ n * k) i % 2 = orbit seed i % 2 := by
  rw [orbit_shift seed k n i (by omega)]
  have h : n - i = (n - i - 1) + 1 := by omega
  rw [h, Nat.pow_succ, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mul_mod]

/-- Every finite all-odd block occurs for arbitrarily large seeds. -/
theorem odd_block (n k i : Nat) (hk : 0 < k) (hi : i < n) :
    orbit (2 ^ n * k - 1) i % 2 = 1 := by
  have hexact (j : Nat) (hj : j ≤ n) :
      orbit (2 ^ n * k - 1) j = 2 ^ (n - j) * (3 ^ j * k) - 1 := by
    induction j with
    | zero => simp [orbit]
    | succ j ih =>
      have h : n - j = n - (j + 1) + 1 := by omega
      simp only [orbit, ih (by omega : j ≤ n), h, Nat.pow_succ]
      have hpos : 0 < 2 ^ (n - (j + 1)) * (3 ^ j * k) :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.mul_pos (Nat.pow_pos (by decide)) hk)
      rw [show 2 ^ (n - (j + 1)) * 2 * (3 ^ j * k) =
        2 * (2 ^ (n - (j + 1)) * (3 ^ j * k)) by ac_rfl]
      rw [show 2 ^ (n - (j + 1)) * (3 ^ j * 3 * k) =
        3 * (2 ^ (n - (j + 1)) * (3 ^ j * k)) by ac_rfl]
      generalize 2 ^ (n - (j + 1)) * (3 ^ j * k) = t at hpos ⊢
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.mul_assoc]
      change (6 * t - 3) / 2 = 3 * t - 1
      clear ih h hj hi hk
      have he : 6 * t - 3 = 1 + 2 * (3 * t - 1) := by omega
      rw [he]
      rw [Nat.add_mul_div_left _ _ (by decide)]
      omega
  rw [hexact i (by omega), show n - i = n - i - 1 + 1 by omega, Nat.pow_succ]
  have hpos : 0 < 2 ^ (n - i - 1) * (3 ^ i * k) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.mul_pos (Nat.pow_pos (by decide)) hk)
  rw [show 2 ^ (n - i - 1) * 2 * (3 ^ i * k) =
    2 * (2 ^ (n - i - 1) * (3 ^ i * k)) by ac_rfl]
  omega

end AntihydraParity

#print axioms AntihydraParity.prefix_parity_shift
#print axioms AntihydraParity.odd_block
