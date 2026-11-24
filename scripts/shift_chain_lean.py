# Writes Cramer/Shift/Small.lean from chain107.txt (output of scripts/shift_chain.py).
import ast
chain=ast.literal_eval(open('chain107.txt').read())
n=len(chain); sz=40; nch=(n+sz-1)//sz
L=["import Cramer.Small\n",
"/-!\n# The range `2 ≤ x < 10^8`: a prime in `(x, x + (107/100)√x log x]` by a checked prime chain\n",
f"`primeChain107` is a list of {n} primes `2 = q₀ < q₁ < … < q_{n-1} = {chain[-1][0]}`, each paired with",
"`k = ⌊16 log₂ q⌋`. `chainOK107` checks `2^k ≤ q_i^16` and",
"`(q_{i+1} − q_i)² · (16·10⁶)² ≤ 11449 q_i (6931 k)²`, which gives",
"`q_{i+1} − q_i ≤ (107/100) √q_i (0.6931 k / 16) ≤ (107/100) √q_i log q_i` (`gap_le_107`). The check is",
"evaluated by `decide` in the kernel (no `native_decide`); primality of each entry is proved by",
"`norm_num`, in chunks of 40. The list was generated greedily (largest admissible prime at each",
"step, `scripts/shift_chain.py`).\n-/\n",
"namespace Cramer.Shift\n","open Real\n"]
for i in range(nch):
  ch=chain[i*sz:(i+1)*sz]
  L.append(f"/-- Chunk {i} of the chain. -/")
  L.append(f"def chain107Chunk{i} : List (ℕ × ℕ) := [" + ", ".join(f"({q}, {k})" for q,k in ch) + "]\n")
  L.append(f"theorem chain107_prime_{i} : ∀ e ∈ chain107Chunk{i}, e.1.Prime := by")
  L.append(f"  simp only [chain107Chunk{i}, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]")
  L.append("  exact ⟨" + ", ".join(["by norm_num"]*len(ch)) + "⟩\n")
L.append("/-- The checked chain of primes, each with `⌊16 log₂ q⌋`. -/")
L.append("def primeChain107 : List (ℕ × ℕ) := " + " ++ ".join(f"chain107Chunk{i}" for i in range(nch)) + "\n")
L.append('''/-- The arithmetic check: `2^k ≤ p^16` at every node, and the gap condition between neighbours. -/
def chainOK107 : ℕ × ℕ → List (ℕ × ℕ) → Bool
  | (p, k), [] => decide (2 ^ k ≤ p ^ 16)
  | (p, k), (q, k') :: l =>
      decide (2 ^ k ≤ p ^ 16) && decide (p < q)
        && decide ((q - p) ^ 2 * (16 * 10 ^ 6) ^ 2 ≤ 11449 * p * (6931 * k) ^ 2) && chainOK107 (q, k') l

set_option maxRecDepth 100000 in
theorem primeChain107_ok : chainOK107 (2, 16) primeChain107.tail = true := by decide +kernel

theorem primeChain107_head : primeChain107 = (2, 16) :: primeChain107.tail := by decide +kernel
''')
L.append(f"set_option maxRecDepth 100000 in\ntheorem primeChain107_last : lastP 2 primeChain107.tail = {chain[-1][0]} := by decide +kernel\n")
L.append("theorem primeChain107_prime : ∀ e ∈ primeChain107, e.1.Prime := by\n  rw [primeChain107]\n  simp only [List.forall_mem_append, and_assoc]\n  exact ⟨" + ", ".join(f"chain107_prime_{i}" for i in range(nch)) + "⟩\n")
L.append('''/-- `2^k ≤ p^16` gives `0.6931 k / 16 ≤ log p`. -/
lemma log_ge_of_pow_le_107 {p k : ℕ} (hp : 2 ^ k ≤ p ^ 16) (_hp1 : 1 ≤ p) :
    0.6931 * (k : ℝ) / 16 ≤ Real.log p := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((p : ℝ) ^ 16) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  rw [Real.log_pow, Real.log_pow] at h1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  push_cast at h1
  nlinarith

/-- The gap condition implies `q ≤ p + (107/100) √p log p`. -/
lemma gap_le_107 {p q k : ℕ} (hp : 2 ^ k ≤ p ^ 16) (hpq : p < q)
    (hg : (q - p) ^ 2 * (16 * 10 ^ 6) ^ 2 ≤ 11449 * p * (6931 * k) ^ 2) :
    (q : ℝ) ≤ p + 107 / 100 * √(p : ℝ) * Real.log p := by
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hp
    · exact h
  have hlog := log_ge_of_pow_le_107 hp hp1
  set X := 107 / 100 * √(p : ℝ) * (0.6931 * k / 16) with hX
  have hX0 : 0 ≤ X := by positivity
  have hg' : ((q : ℝ) - p) ^ 2 ≤ X ^ 2 := by
    have h1 : (((q - p) ^ 2 * (16 * 10 ^ 6) ^ 2 : ℕ) : ℝ) ≤ ((11449 * p * (6931 * k) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast [Nat.cast_sub hpq.le] at h1
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hq : (q : ℝ) - p ≤ X := by
    by_contra hc
    push Not at hc
    nlinarith
  have : X ≤ 107 / 100 * √(p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- `x ↦ x + (107/100)√x log x` is monotone on `[1, ∞)`. -/
lemma step_mono_107 {p y : ℝ} (hp : 1 ≤ p) (hpy : p ≤ y) :
    p + 107 / 100 * √p * Real.log p ≤ y + 107 / 100 * √y * Real.log y := by
  have h1 : √p ≤ √y := Real.sqrt_le_sqrt hpy
  have h2 : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h4 : 0 ≤ √p := Real.sqrt_nonneg _
  have h5 : √p * Real.log p ≤ √y * Real.log y :=
    mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-- Walking a checked chain. -/
theorem exists_prime_of_chain_107 : ∀ (L : List (ℕ × ℕ)) (p k : ℕ), chainOK107 (p, k) L = true →
    p.Prime → (∀ e ∈ L, e.1.Prime) → ∀ y : ℝ, (p : ℝ) ≤ y → y < lastP p L →
    ∃ q : ℕ, q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + 107 / 100 * √y * Real.log y
  | [], p, k, _, _, _, y, hpy, hy => by simp [lastP] at hy; linarith
  | (q, k') :: l, p, k, hc, hp, hl, y, hpy, hy => by
    simp only [chainOK107, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpk, hpq⟩, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl (q, k') (by simp)
    rcases lt_or_ge y q with h | h
    · refine ⟨q, hq, h, ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      exact (gap_le_107 hpk hpq hg).trans (step_mono_107 hp1 hpy)
    · exact exists_prime_of_chain_107 l q k' hc' hq (fun e he => hl e (by simp [he])) y h
        (by simpa [lastP] using hy)

/-- **Every `(x, x + (107/100)√x log x]` with `2 ≤ x < 10^8` contains a prime** (no hypothesis). -/
theorem exists_prime_small_107 {x : ℝ} (hx2 : 2 ≤ x) (hx : x < 10 ^ 8) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 107 / 100 * √x * Real.log x := by
  have hall := primeChain107_prime
  rw [primeChain107_head] at hall
  refine exists_prime_of_chain_107 primeChain107.tail 2 16 primeChain107_ok Nat.prime_two
    (fun e he => hall e (List.mem_cons_of_mem _ he)) x (by norm_num; linarith) ?_
  rw [primeChain107_last]; push_cast; linarith

end Cramer.Shift
''')
open('Cramer/Shift/Small.lean','w').write("\n".join(L))
