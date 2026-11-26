# Further projects

Eleven of the 28 folders under [`conjectures/`](../conjectures/) are not among the 17 headline
results. They are here for one of three reasons:

- **Dependency.** A headline result requires it as a Lean package, so it has to build.
- **Side project.** It was started beside the headline results, and its result stands on its own.
- **Wound down or finished early.** It predates the rule that a target must be open in the
  literature (see [`NEXT_TARGETS.md`](NEXT_TARGETS.md)), so it is kept but not extended.

Each folder's README gives the exact Lean statements, the `#print axioms` output and the build
target. The per-project checklist is in [`AGENTS.md`](../AGENTS.md).

| Folder | Result | Status | Why it is here |
| :--- | :--- | :--- | :--- |
| [`ankeny-grh`](../conjectures/ankeny-grh/) | Bach's explicit Ankeny theorem under GRH: the least non-residue and the least element outside a subgroup are `≤ c log² q` | 🟡 proved with `c = 21/5`; lls-grh proves Bach's own `c = 2` | Dependency (required by bach-sorenson-grh, erdos-770, lls-grh, miller-grh) |
| [`miller-grh`](../conjectures/miller-grh/) | Deterministic Miller–Rabin under GRH: testing every base `≤ c log² n` decides primality | 🟡 proved with `c = 21/5`; `c = 2` follows from lls-grh | Dependency (required by lls-grh) |
| [`littlewood-rh`](../conjectures/littlewood-rh/) | Littlewood's bound `\|ζ(1/2+it)\| ≤ exp(C log t / log log t)` under RH, with `C = 4` | ✅ proved; the sharp constant `(log 2)/2 + ε` (Chandee–Soundararajan) is not | Dependency (required by mertens-rh) |
| [`artin-grh`](../conjectures/artin-grh/) | Hooley's theorem: Artin's primitive root conjecture under GRH for the Kummer fields | 🟠 proved given `HooleyHypothesis`; riemann-hypothesis has no zero-free region for non-abelian Dedekind zeta functions, so it can't be discharged | Dependency (required by abelian-erh) |
| [`shoup-grh`](../conjectures/shoup-grh/) | Shoup's least primitive root bound `g(p) ≪ ω(p−1)⁴ (log ω + 1)⁴ log² p` under GRH | 🟡 `ω(p−1)^{21/5} log² p` proved, below Wang's exponent 6; Shoup's exponent not | Side project |
| [`psi-grh`](../conjectures/psi-grh/) | `ψ(x,χ)` and primes in arithmetic progressions under GRH, uniform in `q` | ✅ proved | Side project |
| [`erdos-969`](../conjectures/erdos-969/) | Erdős Problem 969: the error term for squarefree and `k`-free numbers, Montgomery–Vaughan's `E_k(x) = O(x^{1/(k+1)+ε})` under RH | 🟡 the Montgomery–Vaughan bound is proved; Erdős 969 itself stays open | Side project |
| [`goldbach-average-rh`](../conjectures/goldbach-average-rh/) | Fujii's average Goldbach bound `Σ_{n≤x} G(n) = x²/2 + O(x^{3/2})` under RH | ✅ proved | Side project |
| [`mills-rh`](../conjectures/mills-rh/) | Mills' constant under RH, and Caldwell–Cheng's prime between consecutive cubes | 🟡 87 decimals proved; Caldwell–Cheng's 600 not | Side project |
| [`goldbach-grh`](../conjectures/goldbach-grh/) | Ternary Goldbach under GRH | ⬜ wound down on 2026-11-24: Helfgott (2013) proves it without GRH, so it is not a target | Wound down |
| [`hironaka-fc`](../conjectures/hironaka-fc/) | Hironaka's resolution of singularities in characteristic 0 | ✅ proved (tier U₀: one lemma from riemann-hypothesis, no RH); a formalisation of a known theorem, finished before the open-problems-only rule | Finished before the target rule |
