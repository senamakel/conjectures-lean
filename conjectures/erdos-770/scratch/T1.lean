import Mathlib
def g (n : ℕ) : ℕ := Nat.gcd (2 ^ n - 1) (3 ^ n - 1)
set_option maxRecDepth 100000 in
example : ∀ n < 2048, 0 < n → g n ∣ (2 ^ n - 1) := by decide +kernel
