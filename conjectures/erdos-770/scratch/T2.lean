import Mathlib
def okD (r d : ℕ) : Bool := !(d ∣ r - 1 ∧ 0 < d) || (List.range 18).any (fun i => 2 ≤ i ∧ i ^ d % r ≠ 1)
def okR (r : ℕ) : Bool := !(Nat.Prime r) || (List.range (r - 1)).all (fun d => okD r d)
set_option maxRecDepth 100000 in
theorem small : (List.range 3000).all okR = true := by decide +kernel
