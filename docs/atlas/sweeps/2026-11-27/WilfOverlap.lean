def sigma : List Nat := [1, 6, 2, 3, 7, 4, 8, 5]
def tau : List Nat := [1, 6, 2, 4, 7, 3, 8, 5]

def overlapShifts (pattern : List Nat) : List Nat :=
  (List.range 7 |>.map (· + 1)).filter fun shift =>
    (List.range (8 - shift)).all fun i =>
      (List.range (8 - shift)).all fun j =>
        decide ((pattern[i + shift]! < pattern[j + shift]!) =
          (pattern[i]! < pattern[j]!))

def swapPositions (pattern : List Nat) : List Nat :=
  (List.range 8).map fun i => pattern[if i == 3 then 5 else if i == 5 then 3 else i]!

theorem sigma_overlaps : overlapShifts sigma = [5, 7] := by decide
theorem tau_overlaps : overlapShifts tau = [5, 7] := by decide
theorem swap_sigma : swapPositions sigma = tau := by decide
theorem swap_tau : swapPositions tau = sigma := by decide

#print axioms sigma_overlaps
#print axioms tau_overlaps
#print axioms swap_sigma
#print axioms swap_tau
