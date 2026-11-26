# Prime chain for Cramer/CMS/Small.lean (constant 22/25): writes Cramer/CMS/Small.lean.
# Usage: python3 scripts/cms_chain.py
import math, sys
N = 100_300_000
s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
for i in range(2, int(N ** .5) + 1):
    if s[i]: s[i * i::i] = bytearray(len(range(i * i, N + 1, i)))
def k_of(p):
    k = (p ** 16).bit_length() - 1
    assert 2 ** k <= p ** 16 < 2 ** (k + 1)
    return k
def ok(p, q):
    k = k_of(p)
    return (q - p) ** 2 * (16 * 10 ** 4) ** 2 * 625 <= 484 * p * (6931 * k) ** 2
chain = [5]; p = 5
while p < 100_000_000:
    g = int(0.88 * math.sqrt(p) * math.log(p)) + 2
    q = min(p + g, N)
    while not (s[q] and ok(p, q)): q -= 1
    assert q > p, p
    chain.append(q); p = q
chain = [(q, k_of(q)) for q in chain]
n = len(chain); sz = 40; nch = (n + sz - 1) // sz
print(n, chain[-1], file=sys.stderr)
L = ["import Cramer.Small\n",
"/-!\n# The range `4 ≤ x < 10^8` for the constant `22/25`: a checked prime chain\n",
f"`primeChainCMS` is a list of {n} primes `5 = q₀ < q₁ < … < q_{n-1} = {chain[-1][0]}`, each paired with",
"`k = ⌊16 log₂ q⌋`. `chainOKCMS` checks `2^k ≤ q_i^16` and",
"`625 (q_{i+1} − q_i)² (16·10⁴)² ≤ 484 q_i (6931 k)²`, which gives",
"`q_{i+1} − q_i ≤ (22/25) √q_i (0.6931 k / 16) ≤ (22/25) √q_i log q_i` (`gap_le_cms`). The check is",
"evaluated by `decide` in the kernel (no `native_decide`); primality of each entry is proved by",
"`norm_num`, in chunks of 40. The list was generated greedily (largest admissible prime at each",
"step, `scripts/cms_chain.py`).\n-/\n",
"namespace Cramer.CMS\n", "open Real\n"]
for i in range(nch):
    ch = chain[i * sz:(i + 1) * sz]
    L.append(f"/-- Chunk {i} of the chain. -/")
    L.append(f"def chainCMSChunk{i} : List (ℕ × ℕ) := [" + ", ".join(f"({q}, {k})" for q, k in ch) + "]\n")
    L.append(f"theorem chainCMS_prime_{i} : ∀ e ∈ chainCMSChunk{i}, e.1.Prime := by")
    L.append(f"  simp only [chainCMSChunk{i}, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]")
    L.append("  exact ⟨" + ", ".join(["by norm_num"] * len(ch)) + "⟩\n")
L.append("/-- The checked chain of primes, each with `⌊16 log₂ q⌋`. -/")
L.append("def primeChainCMS : List (ℕ × ℕ) := " + " ++ ".join(f"chainCMSChunk{i}" for i in range(nch)) + "\n")
L.append(f'''/-- The arithmetic check: `2^k ≤ p^16` at every node, and the gap condition between neighbours. -/
def chainOKCMS : ℕ × ℕ → List (ℕ × ℕ) → Bool
  | (p, k), [] => decide (2 ^ k ≤ p ^ 16)
  | (p, k), (q, k') :: l =>
      decide (2 ^ k ≤ p ^ 16) && decide (p < q)
        && decide ((q - p) ^ 2 * (16 * 10 ^ 4) ^ 2 * 625 ≤ 484 * p * (6931 * k) ^ 2) && chainOKCMS (q, k') l

set_option maxRecDepth 100000 in
theorem primeChainCMS_ok : chainOKCMS ({chain[0][0]}, {chain[0][1]}) primeChainCMS.tail = true := by decide +kernel

theorem primeChainCMS_head : primeChainCMS = ({chain[0][0]}, {chain[0][1]}) :: primeChainCMS.tail := by decide +kernel

set_option maxRecDepth 100000 in
theorem primeChainCMS_last : lastP {chain[0][0]} primeChainCMS.tail = {chain[-1][0]} := by decide +kernel
''')
L.append("theorem primeChainCMS_prime : ∀ e ∈ primeChainCMS, e.1.Prime := by\n  rw [primeChainCMS]\n  simp only [List.forall_mem_append, and_assoc]\n  exact ⟨" + ", ".join(f"chainCMS_prime_{i}" for i in range(nch)) + "⟩\n")
L.append(f'''/-- `2^k ≤ p^16` gives `0.6931 k / 16 ≤ log p`. -/
lemma log_ge_of_pow_le_cms {{p k : ℕ}} (hp : 2 ^ k ≤ p ^ 16) :
    0.6931 * (k : ℝ) / 16 ≤ Real.log p := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((p : ℝ) ^ 16) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  rw [Real.log_pow, Real.log_pow] at h1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  push_cast at h1
  nlinarith

/-- The gap condition implies `q ≤ p + (22/25) √p log p`. -/
lemma gap_le_cms {{p q k : ℕ}} (hp : 2 ^ k ≤ p ^ 16) (hpq : p < q)
    (hg : (q - p) ^ 2 * (16 * 10 ^ 4) ^ 2 * 625 ≤ 484 * p * (6931 * k) ^ 2) :
    (q : ℝ) ≤ p + 22 / 25 * √(p : ℝ) * Real.log p := by
  have hlog := log_ge_of_pow_le_cms hp
  set X := 22 / 25 * √(p : ℝ) * (0.6931 * k / 16) with hX
  have hX0 : 0 ≤ X := by positivity
  have hg' : ((q : ℝ) - p) ^ 2 ≤ X ^ 2 := by
    have h1 : (((q - p) ^ 2 * (16 * 10 ^ 4) ^ 2 * 625 : ℕ) : ℝ) ≤ ((484 * p * (6931 * k) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast [Nat.cast_sub hpq.le] at h1
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hq : (q : ℝ) - p ≤ X := by
    by_contra hc
    push Not at hc
    nlinarith
  have : X ≤ 22 / 25 * √(p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- `x ↦ x + (22/25)√x log x` is monotone on `[1, ∞)`. -/
lemma step_mono_cms {{p y : ℝ}} (hp : 1 ≤ p) (hpy : p ≤ y) :
    p + 22 / 25 * √p * Real.log p ≤ y + 22 / 25 * √y * Real.log y := by
  have h1 : √p ≤ √y := Real.sqrt_le_sqrt hpy
  have h2 : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h4 : 0 ≤ √p := Real.sqrt_nonneg _
  have h5 : √p * Real.log p ≤ √y * Real.log y :=
    mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-- Walking a checked chain. -/
theorem exists_prime_of_chain_cms : ∀ (L : List (ℕ × ℕ)) (p k : ℕ), chainOKCMS (p, k) L = true →
    1 ≤ p → (∀ e ∈ L, e.1.Prime) → ∀ y : ℝ, (p : ℝ) ≤ y → y < lastP p L →
    ∃ q : ℕ, q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + 22 / 25 * √y * Real.log y
  | [], p, k, _, _, _, y, hpy, hy => by simp [lastP] at hy; linarith
  | (q, k') :: l, p, k, hc, hp, hl, y, hpy, hy => by
    simp only [chainOKCMS, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpk, hpq⟩, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl (q, k') (by simp)
    rcases lt_or_ge y q with h | h
    · refine ⟨q, hq, h, ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
      exact (gap_le_cms hpk hpq hg).trans (step_mono_cms hp1 hpy)
    · exact exists_prime_of_chain_cms l q k' hc' (by omega) (fun e he => hl e (by simp [he])) y h
        (by simpa [lastP] using hy)

/-- **Every `(x, x + (22/25)√x log x]` with `5 ≤ x < 10^8` contains a prime** (no hypothesis). -/
theorem exists_prime_small_cms {{x : ℝ}} (hx5 : 5 ≤ x) (hx : x < 10 ^ 8) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 22 / 25 * √x * Real.log x := by
  have hall := primeChainCMS_prime
  rw [primeChainCMS_head] at hall
  refine exists_prime_of_chain_cms primeChainCMS.tail {chain[0][0]} {chain[0][1]} primeChainCMS_ok (by norm_num)
    (fun e he => hall e (List.mem_cons_of_mem _ he)) x (by norm_num; linarith) ?_
  rw [primeChainCMS_last]; push_cast; linarith

end Cramer.CMS
''')
open("Cramer/CMS/Small.lean", "w").write("\n".join(L))
