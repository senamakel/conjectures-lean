import Erdos770.Sharp.Finite
open Erdos770.Sharp
def gf (n g : ℕ) : ℕ := ((List.range 14).map (fun t => (t + 4) ^ n - 1)).foldl Nat.gcd g
set_option trace.profiler true in
theorem d1 : ∀ n < 256, 2 ≤ n → 0 < gf n (Nat.gcd (2 ^ n - 1) (3 ^ n - 1)) := by decide +kernel
def Q2 (n : ℕ) : ℕ := ((List.range (n + 1)).filter (fun d => 0 < d && n % d == 0 && isPrimeSmall (d + 1))).foldl (fun a d => a * (d + 1)) 1
set_option trace.profiler true in
theorem d2 : ∀ n < 256, 0 < Q2 n := by decide +kernel
def Q3 (n : ℕ) : ℕ := (P3000.filter fun p => decide (p ≤ n + 1)).foldl (fun a p => if n % (p - 1) = 0 then a * p else a) 1
set_option trace.profiler true in
theorem d3 : ∀ n < 256, 0 < Q3 n := by decide +kernel
