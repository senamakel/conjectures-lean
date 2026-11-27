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

private theorem orbit_one (i : Nat) : orbit 1 i = 1 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [orbit, ih]

/-- Every finite all-odd block occurs for arbitrarily large seeds. -/
theorem odd_block (n k i : Nat) (hi : i < n) :
    orbit (1 + 2 ^ n * k) i % 2 = 1 := by
  rw [prefix_parity_shift 1 k n i hi, orbit_one]

end AntihydraParity

#print axioms AntihydraParity.prefix_parity_shift
#print axioms AntihydraParity.odd_block
