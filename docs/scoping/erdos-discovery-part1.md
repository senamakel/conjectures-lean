# Erdős discovery, slice 1 (problems 3–414): where could we prove something real?

Date 2026-11-24. Research only. No repo was edited and no Lean was run. Three small Python checks
ran under `nice -n 19`, each under a CPU-minute, in the session scratchpad. Live pages were read
through Exa on 2026-11-24: `erdosproblems.com/<n>`, `erdosproblems.com/forum/thread/<n>` and the
erdosproblems.ai mirrors. Anything I could not confirm is marked *(unverified)*.

## 1. Coverage

- **Slice:** `atlas/erdos_open_part1.json`, 214 problems (213 `open`, 1 `partially_resolved`, #19),
  numbers 3–414. Only #390 has `lean = true` in the atlas.
- **Read in full:** every statement and commentary, in a 200 KB dump (`p1.txt`) read top to bottom,
  not filtered by keyword. By tag: number theory 106, graph/Ramsey 35, additive combinatorics 33,
  geometry/distances 20, irrationality 13, other 7.
- **Live threads checked** for the 13 that looked attackable after reading: #124, #129, #203, #261,
  #273, #289, #306, #307, #317, #348, #389, #404, plus a web search on #404.
- **Not re-proposed:** nothing the earlier RH discovery pass kept or discarded. #233 is already
  assigned (erdos-233). #5, #208, #218 and #238 were discarded there; I add one note on #238 below.

**Result in one line:** no RH/GRH-shaped candidate in this slice. **One** candidate of kind (A),
#404(ii), and it is risky. Everything else is research-hard, already claimed, or already worked
over by computation.

## 2. Candidates kept

### 1. Erdős #404, question (ii): an infinite sequence of factorials whose partial sums converge to 0 p-adically. Kind (A). Confidence low to moderate.

- **Statement** (erdosproblems.com/404, as corrected after Kovač, Aug 2025). Let f(a,p) be the
  largest k such that p^k | a₁!+⋯+aₙ! for some a = a₁ < ⋯ < aₙ.
  - (i) For which (a,p) is f(a,p) finite?
  - (ii) Is there a prime p and an infinite a₁ < a₂ < ⋯ with v_p(Σ_{i≤k} aᵢ!) → ∞?

  formal-conjectures has **no** statement. There is a jig.so statement (#159, `Erdos404FactorialSumValuations.statement`)
  and a LeanGenius file that states it with Lin's bound as an axiom.
- **Live status (2026-11-24): open.** The site's banner says "cannot be resolved with a finite
  computation". What is known:
  - The erdosproblems.ai wiki (updated 14 Oct 2026) says "No claim settles this problem."
  - Lin: f(2,2) ≤ 254. Kitamura (July 2026, Lean-checked) shows this is sharp, f(2,2) = 254, and
    computes f(a,2) for every a ≤ 256. f(a,2) is finite in all of them.
  - Kitamura also gives f(1,p) ≥ 20000 for p = 3, 5, 7.
  - Tao (forum, 29 Sep 2025) says f(1,5) "possibly even infinite". He gives the lifting lemma:
    P(a,p,N) ⇒ P(a,p,N+H) whenever the subset sums of the normalised factorials N!,…,(N+H−1)!
    cover Z/p^{v_p((N+H)!/N!)}. He calls the N = 0 case key.
  - Plasma AI (wiki): unboundedness of f(a,p) at one pair is equivalent to (ii), by compactness.
    f(a,p) = v_p(a!) when p | a+1.
  - jig.so #159 (Aug 2026, GPT-5.6) lists "recursive p-adic cancellation, valuation-level gaps,
    compactness trees" as routes it tried and did not close.
  - The site lists "Sky-Yang" as currently working on it.
- **What we would prove.** For one fixed odd prime, for example p = 5: f(1,5) = ∞. That answers
  (ii) yes.
- **Plan.**
  1. *Reduction* (done in the literature, easy in Lean). f(a,p) = ∞ ⇔ (ii) at (a,p), by König's
     lemma / compactness over {0,1}^ℕ. Mathlib has `padicValNat` and Legendre
     (`padicValNat_factorial`).
  2. *Block lemma.* Call N ≡ 0 (mod p^E) with v_p(N+p^E) = E "clean". On a clean block of length
     p^E, v_p((N+p^E)!/N!) = v_p((p^E)!). I checked this and it is easy. My scratch check for the
     N = 0 case: the subset sums of {i! : i < p^E} cover all of Z/p^{v_p((p^E)!)} for
     (p,E) = (5,1), (5,2), (7,1). They **fail** for p = 3: 79/81 residues at E = 2, 97.5% at
     E = 3. For p = 2 they fail badly, as Lin's bound predicts.
  3. *The missing step, not solved.* A naive digit-by-digit induction (p sub-blocks of length
     p^{E−1}) breaks on the top sub-block. Its endpoint has valuation E, so it must fix one more
     digit than a clean block gives. Carried down the recursion, the base block of p elements must
     fix ~E extra digits, which 2^p subsets cannot do for large E. Surplus in the lower sub-blocks
     cannot simply be passed upward, because later blocks overwrite those digits. A proof needs an
     invariant stronger than coverage: equidistribution of the higher digits over the subsets that
     hit each residue, or joint coverage of adjacent blocks. I do not have that invariant.
  4. *Computation that would guide step 3.* For p = 5, 7: residue-multiplicity profiles of clean
     blocks at E = 2, and at E = 3 by meet-in-the-middle (5^31 residues; impossible as a dense DP,
     feasible over a few digits at a time). Find out whether "every residue is hit by subsets whose
     next digit takes every value" holds. That would be the inductive hypothesis.
  5. *If step 3 closes:* Lean proof of the block lemma by induction on E. The base case is a
     `decide` on p = 5 (2^5 subsets mod 5, plus the digit-profile check). Then the compactness
     step. No RH, no workspace inputs. Tier D.
- **How new.** It would settle a named open sub-question that Tao has commented on publicly. A
  careful mathematician would call it a genuine (if minor) result, provided the invariant is real.
  Right now I cannot rule out that (ii) is false for every p (that f(a,p) is finite everywhere, as
  it is for p = 2), and the p = 3 coverage failure is a warning sign.
- **Effort and risk.** L to XL. **Main risk:** step 3 is the whole problem, and since Sept 2025
  several AI-assisted groups have tried exactly this route without closing it. Spend at most 1–2
  days on step 4 before deciding.

Nothing else in the slice met the bar.

## 3. Near misses (looked attackable, but are not)

- **#317(ii)** (strict inequality |Σ δ_k/k| > 1/[1..n] for large n). My reduction: equality forces
  Σ δ_k L_n/k = ±1. For a prime p ∈ (n/2, n] only k = p survives mod p, so δ_p ≠ 0 and
  L_n/p ≡ ±1 (mod p). So (ii) holds at n whenever some prime p ∈ (n/2,n] has L_n/p ≢ ±1 (mod p).
  A scratch check shows such a p exists for **every 5 ≤ n ≤ 5000**, which settles (ii) on that
  range. No route to all n: the claim is about L_n mod p for primes near n, and neither GRH nor
  sieves control it. Worth one paragraph in a forum post, not a target. *(I did not see this
  reduction in the thread.)*
- **#261** (n/2^n = Σ a_k/2^{a_k} for every n?). Verified for n ≤ 10000 (Tengely–Ulas–Zygadło
  2020). It reduces to a binary carry problem: after a greedy run of top indices, fix the low
  bits exactly. That looks like an automaton argument but I found no proof. Kovač (Aug 2025)
  confirms it is open.
- **#273** (covering system with moduli p−1, p ≥ 5). A finite witness would settle it, but
  veljjanoski (Sept 2026) ruled out lcm < 8·10⁶ exhaustively, after Zeraoulia (lcm ≥ 393120, Zenodo
  21613011). Greedy search at lcm up to 1.7·10⁶ still leaves 10–14% uncovered. Crowded and far away.
- **#203** (m coprime to 6 with every 2^k3^l·m+1 composite). A 2D covering search exists: 442 primes
  with |⟨2,3⟩| ≤ 2000, coverage plateau ~76% (veljjanoski, Sept 2026). No covering is in sight.
- **#389 / #396** (Erdős–Straus divisibility of consecutive products). Existence verified to n = 35
  with witnesses k ~ 10^16 (Sept 2026). Proving existence for all n needs simultaneous
  prime-gap-type structure. RH gives only upper bounds on gaps, which is the wrong direction.
- **#348** (complete sequences, case m=2, n=3). Large structured searches (Sprite144, July 2026)
  suggest no witness exists. The strong-sense version was settled by van Doorn. No idea for the
  weak version.
- **#289** (1 as a sum over k disjoint, non-adjacent intervals, all large k). Kovač's easy proof
  covers only the overlapping version. The intended version is open and I had no construction.
- **#307** (two prime sets, product of reciprocal sums = 1). Reduces to Σ_{p∈P} ∏P/p = ∏Q and its
  mirror. Needs |P∪Q| ≥ 60 and factoring huge numbers. Stijn Cambie calls the computational route
  "not the way to go".
- **#238** (runs of c₁ log x consecutive primes with all gaps > c₂, for every c₁). Pigeonholing with
  the Selberg upper bound for gaps ≤ c₂ gives runs of length ≍ log x/c₂, which is Erdős's result.
  Arbitrary c₁ needs lower-bound information on where gaps fall. Even c₂ = 2 (runs with no twin
  primes) is beyond Shiu/Maynard-type results. Agrees with the earlier discard.
- **#129**: false as written (Girao's random colouring). The site keeps it open only because the
  intended statement is unknown. Nothing to prove.

## 4. Bulk discard summary

| Reason | Count (approx.) | Examples |
|---|---|---|
| Already solved or claimed, or the named part is done | 6 | #306 (Tang, Lean proof, Zenodo 20767390, June 2026, plus a second ω=2 claim), #124 (first question: Aristotle/Alexeev, Nov 2025; second partly settled by Fan 2026), #129 (false as written), #65 (first part known), #19 (large n done), #114 (large n done, Tao 2025) |
| Asymptotic or order-of-growth questions with no finite resolution, no RH input, research-hard | ~95 | #3, #20, #30, #39, #52, #77, #142, #148, #165, #170, #241, #293, #304, #311, #336, #357, #394, #400 |
| Graph, Ramsey, hypergraph extremal problems (no number-theoretic input; frontier research) | 35 | #23, #61, #64, #82, #85, #128, #149, #159, #167, #181, #184 |
| Discrete geometry and distances | 20 | #89, #96, #97, #99, #104, #107, #212, #213, #217 |
| Irrationality or transcendence (no method in reach) | 13 | #68, #249, #251, #257, #263–#269 |
| Need conjectures beyond RH (Hardy–Littlewood tuples, ABC, Cramér, Elliott–Halberstam, Schanuel) | ~20 | #5, #15, #141, #145, #208, #218, #252, #291, #364–#366, #371, #373, #382, #383, #385, #393, #398, #408 |
| Existence by search: heavily computed already, or the witness is beyond any search | ~10 | #242 (to 10^18), #375 (Grimm, to 1.9·10^10), #398, #364/#366 (to 10^22–10^28), #11 (to 2^50), #203, #273, #389, #406, #412 |
| Ill-posed or definitional (needs the intended statement first) | ~5 | #129, #278, #361, #409, #203's q-variant |
| Assigned elsewhere in the workspace | 1 | #233 |

**Why the slice has no RH/GRH candidate.** The number theory problems here that mention primes
need short-interval or *lower*-bound information on gaps (#5, #218, #234, #238, #375, #382, #385),
which RH does not give. The rest need additive structure (#9, #10, #11, #236, #244) or
digit-and-valuation structure (#376, #377, #404, #406), which no Dirichlet L-function input
controls.
