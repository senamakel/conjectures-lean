import FormalConjectures.Other.BeaverMathOlympiad

/-! Prefix parity and a counting reformulation of the pinned Antihydra target. -/

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

/-- The rounded-up Hydra orbit starting at 7. -/
def ceilOrbit (n : Nat) : Nat := Nat.rec 7 (fun _ d => (3 * d + 1) / 2) n

/-- Shifting by one conjugates the rounded-up Hydra orbit to Antihydra. -/
theorem orbit_eight_eq_ceil_succ (n : Nat) : orbit 8 n = ceilOrbit n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 3 * orbit 8 n / 2 = (3 * ceilOrbit n + 1) / 2 + 1
    rw [ih]
    omega

theorem orbit_eight_parity_complement (n : Nat) :
    orbit 8 n % 2 = 0 ↔ ceilOrbit n % 2 = 1 := by
  rw [orbit_eight_eq_ceil_succ]
  omega

def evenCount (n : Nat) : Nat :=
  ((Finset.range n).filter fun i => Even (orbit 8 i)).card

/-- Every prefix needs at least a third of its entries to be even. -/
theorem target_iff_even_count :
    (type_of% @BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.variants.set) ↔
      ∀ n, n ≤ 3 * evenCount n := by
  have hcard (n : Nat) :
      ((Finset.range n).filter fun i => Odd (orbit 8 i)).card + evenCount n = n := by
    simpa [evenCount, Nat.not_odd_iff_even] using
      (Finset.card_filter_add_card_filter_not
        (p := fun i => Odd (orbit 8 i)) (s := Finset.range n))
  have hcount (n : Nat) :
      ((Finset.range n).filter fun i => Odd (orbit 8 i)).card ≤ 2 * evenCount n ↔
        n ≤ 3 * evenCount n := by
    have := hcard n
    omega
  constructor
  · intro h n
    apply (hcount n).mp
    simpa [evenCount, Nat.Ico_zero_eq_range] using
      h (orbit 8) rfl (fun _ => rfl) n
  · intro h a h0 hs n
    have ha : a = orbit 8 := by
      funext i
      induction i with
      | zero => exact h0
      | succ i ih => rw [hs, ih, orbit]
    subst a
    simpa [evenCount, Nat.Ico_zero_eq_range] using (hcount n).mpr (h n)

end AntihydraParity

#print axioms AntihydraParity.prefix_parity_shift
#print axioms AntihydraParity.odd_block

#print axioms AntihydraParity.target_iff_even_count

#print axioms AntihydraParity.orbit_eight_parity_complement
