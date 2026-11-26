# Lane `novel-via-rh`: open statements that our explicit GRH theorems settle by an unpublished argument

Date 2026-11-26. Research only: nothing built, no Lean file edited. Every number below was
computed with Python `-I` (scripts in the session scratchpad, not kept). Claims not confirmed
from a primary source are marked *(unverified)*. Edges are in `novel-via-rh.edges.jsonl`.

## Result in one paragraph

One cluster reaches class A: **primitive roots modulo `p²`**. Kerr, McGown and Trudgian
(arXiv:1908.11497, J. Number Theory 2020) conjecture that Grosswald's bound also holds for
`h(p)`, the least primitive root mod `p²` (`h(p) < √p − 2` for every `p > 409`), and that
`h(p) ≤ p^{log 2/log 3}` for every prime. They write that they cannot prove either. The best
unconditional result is `h(p) < p^{2/3}` (McGown–Sorenson, Math. Comp. 2024). I found no
GRH-conditional treatment anywhere. The deduction is the McGown–Treviño–Trudgian sieve that
grosswald-grh already runs, plus **one extra character family** (the `p − 1` characters of
order `p` mod `p²`, all primitive of conductor `p²`). The general-modulus Bach bound needed for
that family is already in Lean (`weinberger-grh`, `bach_primitive_of_GRH`). A cheaper sibling is
in the same class: every odd prime `p` has a **prime** `q < p` that is a primitive root modulo
`p²`, and therefore modulo every power of `p`. That is Erdős 985 lifted to prime powers, and it
needs only erdos-985's unsieved argument plus the same extra term. Nothing else I checked
reached class A. One class-B item, Cohen–Trudgian's square-free primitive root conjecture, is
recorded with its finite check done.

## Class A candidates, easiest first

### A1. A prime `q < p` that is a primitive root modulo `p²` (hence modulo every `p^k`), for every odd prime `p` · effort S–M

- **Statement.** `∀ p prime, p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod (p^2)) = p*(p-1)`.
  For odd `p`, a primitive root mod `p²` is a primitive root mod every `p^k` (standard; an
  elementary Lean lemma, not in Mathlib as far as I know *(unverified)*). So the corollary is
  `∀ k ≥ 1, orderOf (q : ZMod (p^k)) = φ(p^k)`. This strictly strengthens `erdos_985`.
- **Literature.** Unconditionally open: it implies Erdős 985, and "prime primitive root `< p`"
  is not known unconditionally even for large `p` (Ha 2013: `ĝ(p) ≪ p^{3.1}`; MathOverflow
  112594). The best result mod `p²` is for integers, not primes: `h(p) < p^{0.99}` (KMT 2019,
  Thm 1), later `p^{2/3}`. Under GRH: MTT 2016 treats mod `p` only. No GRH statement mod `p²`
  was found (search below).
- **Deduction.** Let `W = {x ∈ (ℤ/p²)ˣ : x^{p−1} = 1}`, the subgroup of index `p`. Then `q` is a
  primitive root mod `p²` iff it is a primitive root mod `p` and `q ∉ W`. On units,
  `1_W = (1/p) Σ_{χ^p = 1} χ`, and each of the `p − 1` non-trivial `χ` is primitive mod `p²`.
  With erdos-985's weight `S(f) = Σ_{n<x} Λ(n) f(n)(1 − n/x)`:
  - erdos-985 already gives `S(prim root mod p) ≥ θ·(x/2 − √x/20 − 3) − θ(2^ω − 1)·bachC·√x·log p`,
    where `θ = φ(p−1)/(p−1)`.
  - `S(1_W) ≤ x/(2p) + (√x/20 + 3)/p + max_{χ^p=1, χ≠1} ‖bachSum χ x‖`, and the last term is at
    most `(√x + 2 + 3/x)(2/3)(log p² + 5/3) + log x + 1.6` by `bach_primitive_of_GRH` with
    `N = p²`.
  - A prime `q < p` that is a primitive root mod `p²` exists once the first term exceeds the
    second. Prime powers `q^k` that are primitive roots force `q` primitive, as in erdos-985.
  The extra term is about `(4/3)·√x·log p`, against `θ(2^ω − 1)·bachC·√x·log p` from the sieve,
  so the threshold moves only a little. With `x = p` my calibrated model puts erdos-985's closing
  point at `10^{7.2}` to `10^{9.9}` (it is `10^8` in Lean). Adding `2/θ ≤ 2(p−1)/φ(p−1)` (about
  12 at `p ≈ 10^8`) to `2^ω − 1` raises it to an estimated `≤ 3·10^8` *(model estimate; recompute
  in Lean's Numerics before fixing the constant)*.
- **Finite range.** Every prime `p` below the new threshold, about `1.6·10^7` primes. For each,
  give a prime `q < p`, a Lucas certificate of primitivity mod `p` (erdos-985's checker), and
  one `powMod q (p−1) (p²) ≠ 1`. That is about `1.6·10^7` extra modular exponentiations,
  negligible beside erdos-985's existing check to `10^8`. Python check to `2·10^6`: no prime
  fails. The least such `q` is always `< √p − 2` once `p > 2791` (largest exceptions:
  `(1811, 41)`, `(2791, 53)`, which are exactly MTT's `ĝ` exceptions).
- **Missing Lean.** (1) `1_W` as a character sum over `(ZMod (p^2))ˣ`, with the primitivity of
  order-`p` characters mod `p²` (conductor argument: `χ` is non-trivial on `1 + pℤ`). (2) Port
  erdos-985's `Main` inequality with the extra term. (3) Extend the checker. Effort S–M.
- **Catch.** It is the obvious lift of a solved problem. Its value is the "every power of `p`"
  form. No problem list states it; KMT's paper only studies the integer version.

### A2. Grosswald's conjecture modulo `p²`: `h(p) < √p − 2` for every prime `p > 409` (Kerr–McGown–Trudgian) · effort M–L

- **Statement source.** KMT, arXiv:1908.11497 §1 (read in full): "Grosswald conjectured that
  `g(p) < √p − 2` for all `p > 409` and this is almost certainly true for `h(p)` as well. While
  we are unable to prove this…"; and later: "Almost certainly the statement
  `h(p) ≤ p^{log 2/log 3}` is true for all primes, as is the analogue of Grosswald's conjecture:
  that `h(p) < √p − 2` for all `p > 409`." The exponent `log 2/log 3` is sharp at `p = 3`
  (`h(3) = 2`).
- **Literature.** Unconditional: `h(p) < p^{0.74}` (Chen), then `h(p) < p^{2/3}`
  (McGown–Sorenson, arXiv:2206.14193 v2 Thm 4, read). The limit of that method is `0.661`, per
  the paper: "0.661 seems the limit of this method for h(p)". `g(p) = h(p)` for every
  `p ≤ 10^{16}` except 40487 and 6692367337, a computation that cannot be used in Lean.
  Grosswald for `g`: GRH (MTT 2016, in Lean as grosswald-grh); unconditionally open on
  `(10^{16}, 1.77·10^{54})` (Bagger, arXiv:2608.20431). For `h`: **no conditional or
  unconditional proof found.**
- **Deduction.** grosswald-grh's pipeline (README, "How the proof goes"), with the A1 term
  added:
  1. Sieve (MTT Thm 3), with `S` prime factors of `p − 1` removed. Weighted count of primitive
     roots mod `p` below `x = ⌊√p⌋ − 2`:
     `≥ δθ(e)·[x/2 − √x/20 − 3 − (2^{ω−s}(2 + (s−1)/δ) − 1)·c(p,x)√x log p]`.
  2. Weighted count of `W`-elements below `x`:
     `≤ x/(2p) + O(1) + (√x + 3)(2/3)(2 log p + 5/3) + log x + 1.6` (`bach_primitive_of_GRH` at `N = p²`).
  3. A counterexample to `h(p) < √p − 2` makes (1) ≤ (2), which is grosswald's `crit` plus a
     term about `(4/3)√x log p / (δθ(e))`.
  4. Tail `p ≥ 10^{47}` (`S = ∅`): the extra term changes `2^ω − 1` into `2^ω − 1 + O(1/θ)`, so
     `Tail.lean`'s `2^ω < 4520 p^{1/8}` becomes `2^ω + 2/θ < 4520 p^{1/8}`. Same threshold.
  5. Algorithm 1 on `(10^{13}, 10^{47})`: re-run with the modified `crit`. Leaves enumerate
     `p = k∏X + 1` and must now find `g < √p − 2` that passes Lucas against `X` **and**
     `g^{p−1} ≢ 1 (mod p²)`: one more `powMod` per leaf success.
  6. Direct range `409 < p < 10^{13} + 10^8`: `segOk` must also check `g^{p−1} mod p² ≠ 1` for
     the proposed `g`, with the untrusted sieve proposing another `g` when it fails (only
     `p = 40487` and `6692367337` below `10^{13}`, by McGown–Sorenson).
- **Corollaries, all class A.** (i) KMT's `h(p) ≤ p^{log 2/log 3}` for every prime: from A2 for
  `p > 409`, since `√p < p^{0.6309}`, and a check for `p ≤ 409` (Python: holds; equality at
  `p = 3`; next largest exponents `0.5646` at `p = 7`, `0.5606` at `p = 191`). (ii) The prime
  version `ĥ(p) < √p − 2` for `p > 2791`, if the sieve is run on primes as MTT do: Python finds
  no exception in `2791 < p ≤ 2·10^6`.
- **Finite computation.** The size of grosswald-grh's: about `3.3·10^6` CPU-s direct plus
  `2.3·10^5` CPU-s tree, according to its README. That is about 1000 CPU-hours, and all of it
  has to be re-run because the checker changes. There may be more leaves where the larger
  `crit` fails for small `ω`, where `2/θ` is comparable with `2^ω`; I have not sized that
  *(unsized; run `scripts/treecut.c` with the new crit)*.
- **Missing Lean.** A1's two lemmas, a modified `crit` with its soundness proof, and the two
  checkers extended by one `powMod` with their soundness proofs. No new analysis. Effort M–L,
  mostly compute and checker plumbing.
- **Catch.** The novelty is modest: the GRH argument is routine for anyone who knows MTT. It is
  still a conjecture stated in print by the people who work on it, with no conditional proof in
  print. Bagger 2026 and McGown–Sorenson 2024 both discuss Grosswald for `g` only.

## Class B (conditional result effectively published; the unconditional form just follows)

- **B1. Cohen–Trudgian Conjecture 1.** `g_□(p) < √p − 2` for every `p > 409`, where `g_□` is the
  least square-free primitive root (J. Number Theory 170 (2017), arXiv:1602.02440, read).
  Unconditional record `g_□(p) < p^{0.96}`. Under GRH, MTT's `ĝ(p) < √p − 2` for `p > 2791`
  covers `p > 2791`, since a prime is square-free. Cohen–Trudgian cite that result next to the
  conjecture. Python check `409 < p ≤ 2791`: no exception. Lean: needs MTT's **prime** version
  `ĝ`. grosswald-grh proves `g`, and its direct checker accepts any `g`, so `ĝ` may need its own
  run. formal-conjectures PR #8222 (open, 2026-11-23) adds the `ĝ < √p − 2` statement to
  `ErdosProblems/985.lean`. Effort S once `ĝ` is in Lean; low novelty.
- **B2. Least prime quadratic residue with an explicit bound.** LLS Thm 1.4 (in Lean as
  `LLS.LeastPrimeInCoset`) keeps the escape clause "`p ≤ 10^9` or …". An explicit
  `r(q) ≤ (c log q)²` for every `q` follows from `bach_primitive_of_GRH` for a real character
  (prime squares are residues and cost `O(√x)`). No named open conjecture asks for it. Not
  pursued.

## Rejected (edges recorded)

- **Jarso–Trudgian conjectures** (Math. Comp. 88 (2019) §5): three consecutive QNRNPs when
  `φ(p−1) ≤ (p−1)/4`; two consecutive when `φ(p−1) ≤ (4/15)(p−1)`. They need sums of
  `χ(n)χ'(n+1)` (Weil bound), and GRH for Dirichlet L does not control them.
- **KMT's "`ĥ(p) < p^{1/2}` for all `p > 1171`"**: the sentence is garbled in the arXiv text
  ("Using e 3$. It seems reasonable that even…"). If `ĥ` is the least prime primitive root mod
  `p²`, it is false: `ĥ(2791) = 53 > √2791 ≈ 52.83` (Python). So `ĥ` means something else there
  *(unverified; read the JNT version)*.
- **`h(p) < p^{0.6309}` by itself.** No cheaper than A2: with `x = p^{0.6309}` the `S = ∅` tail
  closes only near `10^{22}`–`10^{26}` in my model, so it needs the same sieve tree. Take it as
  a corollary of A2.
- **Prime primitive root `ĝ(p) < √p − 2`**: published (MTT 2016 Thm 1). Not new.
- Earlier lanes' rejections stand and were not repeated: primes between `x^α` and `(x+1)^α`
  for `α < 3`, Legendre-type windows, class-number lists beyond 100, Sun's quadratic-form
  conjectures A185150 and A191004 (Legendre strength: windows of size `n`, below Cramér's
  `√x log x`).

## Novelty search, line by line (2026-11-26)

| Where | Query | Found |
|---|---|---|
| arXiv / web (Exa, 3 queries) | least (prime) primitive root mod `p²`; Grosswald analogue mod `p²` under GRH; 2024–2026 primitive roots mod prime powers under GRH | KMT 2019 (conjecture, "unable to prove"); McGown–Sorenson 2024 (computation, `p^{2/3}`); Bagger 2026 (`g` only); Carella 2025 (heuristic `p^{1/2+ε}`, mod `p²`); Fan–Pollack 2025 (dual problem). No GRH result mod `p²` |
| McGown–Sorenson v2 full text | grep `GRH`, `h(p)`, `√` | GRH appears only for `g` (citing MTT) |
| Zenodo (via Exa) | QRH/RH corollaries for primitive roots | dr vengy notes 23352867, 23394710, 23423889: Vinogradov's conjecture for `g`, `g*` mod `p` only. Nothing mod `p²` |
| formal-conjectures clone `9097e2f` | `Grosswald`, `ZMod (p ^ 2)`, primitive root files outside Erdős | only `ErdosProblems/985.lean` (mod `p`) and `PowerfulNumbersDensity.lean` (unrelated) |
| formal-conjectures PRs | `gh pr list --search "primitive root"` (all states) | #8222 (`ĝ < √p−2` mod `p`), #7425 (simultaneous primitive roots, a different problem), #3245/#2723 (closed). Nothing mod `p²` |
| 1337isnot1337/solved-conjectures clone `43152d5` | `CONTENTS.md` grep Grosswald/primitive; `git grep "primitive root"` on every remote branch | only cyclotomic Hadamard files. Nothing relevant. The `research` branch is not in this clone, so `research/rh-transfer` was not re-read (the toolkit-reuse lane read it today) |
| openai/math | `gh search code primitiveRoot --repo openai/math` | Fourier and number-field files only |
| GitHub code search | `Grosswald` (Lean); `orderOf` + `p ^ 2` (Lean); "primitive root modulo p^2" | our own grosswald-grh, formal-conjectures 985; nothing mod `p²` |

## What I could not check

- The published JNT version of KMT (the end of §3 is garbled in arXiv v1), and Chen's
  `h(p) < p^{0.74}` paper (not opened).
- Whether Mathlib has "primitive root mod `p²` ⇒ mod `p^k`" (not searched in Mathlib source).
- Exact thresholds for A1 and A2 in Lean's own constants (`bachC`, `crit`). My numbers come
  from a calibrated model, not from the Lean inequalities.
- Broad OEIS "Conjecture:" sweeps, Guy's UPINT A/B/F, MathOverflow open-problem tags, and
  Kourovka/OPIA lists were not swept systematically this session. The time went into A1 and A2.
  The formal-conjectures OEIS files with `jacobiSym`, `legendreSym` or `orderOf` were read (all
  Legendre-strength or congruence identities, none GRH-reachable).
- MathOverflow and erdosproblems.com comment threads for a mod-`p²` remark (no specific page
  exists for the `p²` question).
