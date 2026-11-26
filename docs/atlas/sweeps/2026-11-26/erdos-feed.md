# Lane `erdos-feed`: Erdős status changes, consequence chains, and non-RH conditional deductions

Date 2026-11-26. Research only: no repo was edited and nothing was built. Sources: the teorth/erdosproblems
`data/problems.yaml` (diffed between d8b3fc4, 2026-08-31, and main, 2026-11-24; 470 commits read);
formal-conjectures (FC) at 9097e2f with 200 commits of history, parsed into declarations
(`fc-scan-work/decls.jsonl`); the Atlas raw harvest (`atlas-repo/data/raw/erdos.jsonl`); the
plasma-ai/erdos wiki (26k-file tree read through `gh api`); the openai/math release at adc7f12;
and live erdosproblems.com pages and threads, read through Exa on 2026-11-26. Work files are in
`discovery/erdos-feed-work/`. Anything I could not confirm from a primary source is marked
*(unverified)*.

**In one line:** I kept two cheap Class-2 packages (abc ⇒ 977-factorial, and abc ⇒ the four
936 variants), plus one Class-1 package of free corollaries of OpenAI's Lean Szemerédi bound
(`erdos_142.variants.lower`, and the all-k form of #140). All three are S effort. None of them is
deep, and the Class-1 package is easy enough that someone will probably post it within days. The
best-looking Class-1 corollary, the [Er80] tail question on #169, was claimed with a Lean proof
on 2026-11-24 (FC PR #8269), so I dropped it.

## 1. Status feed since 2026-09

### 1a. Changes recorded in the community database (teorth `problems.yaml`, Aug 31 → Nov 24)

There are 66 changes in all (`erdos-feed-work/teorth/changes.json`). The number-theory and
additive ones are:

| # | Old → new | Lean code |
|---|---|---|
| 3 | open → **open (Lean)** (2026-10-16) | OpenAI `OAI.Erdos3.manuscriptReciprocalProgressionTheorem`, openai/math@adc7f12 `lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean`. Linked as FC `erdos_3`'s formal_proof (FC #6898). Lean v4.34.1, Mathlib d13f23b, 4,786 files. The database notes that no human reader has digested it yet |
| 1 | open → disproved (Lean) | yes (Lean status only, no URL in the database) |
| 14 | open → solved (2026-10-15) | none recorded |
| 126 | open → proved (Lean) | yes (no URL in the database) |
| 131 | open → disproved | none |
| 137, 850 | open → "verifiable" | 850: Collin Ren's AI-assisted Lean for the two-consecutive family (the three-consecutive Erdős–Woods question stays open) |
| 143 | open → solved | FC `erdos_143.parts.i` fixed to true (FC #7807, Koukoulopoulos–Lamzouri–Lichtman) |
| 293 | open → solved (van Doorn–Tang, arXiv:2512.22083) | none |
| 304 | open → proved | none |
| 677 | open → "falsifiable" | none |
| 190, 318, 343, 441, 482, 1050 | solved/proved → (Lean) | jbaelaw, Collin Ren (awards repo), gotrevor/lean-gallery |
| 346, 421, 477, 730, 1005 | open → solved, back-dated to 2025 (corrections of the field) | none |

The others are graph theory, set theory, geometry or analysis: 74, 81, 96, 97, 108, 184 (OpenAI
Lean), 193, 196, 501, 522 (Lean), 547, 548, 550 (Lean), 557, 571, 595, 601, 623, 625 (Lean,
2026-11-16), 630, 651, 703, 740, 754, 803, 857 (proved, 2026-10-20), 918, 973 (Lean), 994, 1018,
1019, 1025, 1129, 1147, 1160, 1168, 1171, 1218–1221.

### 1b. Status the database has not caught up with

In 42 cases the database still says "open" but FC marks **every** main statement `research solved`
with a `formal_proof` link (`erdos-feed-work/stale.txt`). The number-theory ones are 254, 260,
267, 289, 306, 341, 371, 394, 424, 431, 486, 489, 769, 796, 817, 821, 824, 952, 968, 970, 978
(parts ii and iii), 1054, 1097 and 1188. Links include williamjblair/lean-proofs `starfleet/`
(254, 267, 394, 489, 521, 769, 796, 1188), cadamcat/* (172, 181, 821, 824) and linrock/math-proofs
(689, 1054). The others are 130, 138, 172, 181, 520, 521, 604, 655, 689, 836, 1033, 1150 and 1212.
Most of the attributes were added in FC's 2026-10-29 Palomar-linter commit, so the git date is not
the date of the proof.

The wiki also lists results that neither the database nor FC records:
- **#252** (irrationality of Σσ_k(n)/n! for every k): an anonymous Lean development,
  tokengr1nder/Erdos252 `Erdos252.erdos_252` (Palomar PALOMAR-2026-10-12-000001). The plasma-ai wiki
  accepts it ("rebuilt and its statement audited"), while erdosproblems.com still says OPEN (page
  edited 2026-01-22). This makes FC's Schinzel- and Dickson-conditional variants of 252 moot.
- **#169**: f(3) ≥ 3.0085385 and f(4) ≥ 4.4397534742 (Kiichi et al., with Lean, 2026-09-26),
  and the OpenAI corollary f(k) ≤ Σ_m r_k(2^m)/2^m < ∞.
- **RH and GRH are now marked solved in FC** (6bc2f74, 2026-11-24, citing [Al26]). FC now lists
  `erdos_233.variants.upper_bound_unconditional` as `research solved` with no formal_proof. Our
  erdos-233 proves it. Linking it is a Palomar submission, not a research task.

## 2. Consequence chains inside the corpus

I extracted 162 sentences that contain a `[n]` cross-reference and an implication keyword from the
harvest commentary (`xref.json`), and 41 more from FC docstrings (`fc_xref.txt`). I then marked
each endpoint with its current status and looked at every edge that joins an open problem to a
settled one, plus the open problems that cite a problem settled since September.

**(a) Open problems implied by a settled one.** Only the #3 chain gives anything:
- #3 (OpenAI Lean bound `r_k(N) ≤ C N exp(−c (log log N)^{1+η})` for every k ≥ 3) gives **#142's
  open FC variant `lower`**, **the all-k form of #140**, **#169's f(k) < ∞**, and #169's [Er80] tail
  question. The first two are kept below. f(k) < ∞ is recorded by Plasma, and the tail question was
  taken by FC PR #8269 (mnn31, 2026-11-24, with a linked Lean proof; also Pal 2007, Lemma 5) and
  PR #6685.
- #857 is now "proved" (m(n,k) ≪ (2 − 1/(16k³))^n for every k; the page credits the account of
  Bucić–He–Lee). By the page's own remark, this makes #856's exponents c_k < 1 for every k, through
  Tang–Zhang [TaZh25b]. That is a real edge, but neither half is in Lean, so it is effort L.
- #2 (Hough) gives #1188 F(x) → ∞. The page already records this.

**(b) Weaker forms or special cases of settled problems that are still marked open.**
- `erdos_142.variants.lower` (= Erdős's "$5000" r_k = o(N/log N)) is still `research open` in FC
  even though `erdos_3` now carries a formal_proof. This is the one stale "weaker form" I found. It
  is candidate 1.
- FC `erdos_3.variants.three` still has only a `conditional formal_proof ... assuming kelley_meka`,
  although it is the k = 3 case of the now-linked `erdos_3`. It is a solved statement, so it adds
  nothing as a result, but it is a one-line fix.
- #826 (stronger than 248), #1094 (stronger than 384), #1150 (stronger than 228), #1159 (a weaker
  version of the *disproved* 664), #44 and #536 (implied by the *disproved* 707 and 537), #52 and
  #545 (special cases solved). None of these edges runs in a useful direction.

## 3. Ranked candidates (easiest first)

### 1. `erdos_142.variants.lower`, plus the all-k form of #140, from OpenAI's Lean bound · Class 1 · effort S

- **Statements.** FC `FormalConjectures/ErdosProblems/142.lean`, `research open`, no formal_proof:
  ```lean
  theorem erdos_142.variants.lower (k : ℕ) (hk : 1 < k) :
      (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)
  ```
  Here `r = Set.IsAPOfLengthFree.maxCard` (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean:218`,
  an `sSup` of `Finset.card S` over `S ⊆ Icc 1 N` that are AP-free).
  #140's all-k form ([ErGr80], [Er81]): for every k ≥ 3 and every C > 0, r_k(N) ≪ N/(log N)^C. FC
  has **no** 140 file. Open PR #6660 states only k = 3 (Kelley–Meka).
- **Premise.** `OAI.Erdos3.manuscriptQuantitativeDensityTheorem : QuantitativeDensityTheorem` (openai/math
  adc7f12, `Results/Conclusions.lean`), where `QuantitativeDensityBound k := ∃ C c η > 0, ∀ N ≥ 3,
  extremalNumber k N ≤ C * N * exp (-c * (log (log N)) ^ (1 + η))`. `extremalNumber` is the
  sup of card over AP-free `S ⊆ Icc 1 N`, with `HasAP A k := ∃ a d, 0 < d ∧ ∀ i < k, a + i*d ∈ A`.
- **Proof sketch.** (1) Bridge lemma: `maxCard k N ≤ extremalNumber k N`. A non-trivial FC
  `IsAPOfLength k` inside S gives `HasAP S k`, so OAI-AP-free implies FC-AP-free. Unfold both and
  check d ≠ 0 against `IsAPOfLengthWith`. (2) k = 2 separately: every 2-element set is a
  non-trivial 2-AP, so r_2(N) ≤ 1. (3) Asymptotics: exp(−c L^{1+η})·(log N)^C =
  exp(C L − c L^{1+η}) → 0 with L = log log N. That gives the o(N/log N) of 142 (C = 1) and the
  O(N/(log N)^C) of 140 in a few lines of `Real.tendsto_exp_neg...`/`isLittleO` bookkeeping.
- **Already known.** Plasma's 142 page says "the bound would also give r_k(N) = o(N/log N)", and its
  140 claim page says the same two OAI declarations give the k ≥ 4 cases. **Nobody has a Lean
  statement or proof of either corollary** that I found. I searched FC PRs for 142, 140, r_k, Kelley,
  OpenAI and quasipolynomial; FC's nine "bridge the OpenAI …" PRs (#7727–7735, none for 3, 140 or
  142); and GitHub code for erdos_142 and Erdos140.
- **Catch.** (i) It is a corollary, roughly a paragraph long. A careful reader would call it a
  formalisation of a remark, not a result. (ii) It rests on the OpenAI proof, which nobody has
  reviewed (about 190 pages; the database note says "not yet digested"). (iii) Toolchain mismatch:
  OAI uses Lean v4.34.1 with Mathlib d13f23b and we use v4.36.0 with fc4f59e5, and the library has
  4,786 files. The practical form is tier H: copy `QuantitativeDensityBound` verbatim as a `Prop`
  hypothesis and prove `erdos_142_lower_of_qdb`, plus a separate-toolchain `Unconditional/` that
  imports OAI. (iv) Workspace policy: this is neither an RH-consequence nor an open problem once #3
  is accepted, so it needs the owner's sign-off as a target. (v) Speed: Plasma has already written
  the sentence, and anyone in mnn31's #8269 thread could post this within days.

### 2. abc ⇒ `erdos_936` (2ⁿ ± 1 and n! ± 1 powerful only finitely often) · Class 2 · effort S

- **Statements.** FC `936.lean`: four `research open` variants, for example
  ```lean
  def EventuallyNotPowerful (a : ℕ → ℕ) : Prop := atTop.Eventually (fun n => ¬ (a n).Powerful)
  theorem erdos_936.variants.factorial_add_one : EventuallyNotPowerful (·! + 1)
  ```
  The others are `two_pow_add_one`, `two_pow_sub_one` and `factorial_sub_one`. The site and the
  database say OPEN. The thread's last substantive post is 2026-07-13 (unconditional constraints
  only).
- **Premise.** FC `FormalConjectures/Wikipedia/ABC.lean`, `ABC.abc (ε) (hε)` (finitely many coprime
  a + b = c with rad(abc)^{1+ε} < c). Use it verbatim as `type_of% ABC.abc`, as 393.lean does. It
  is open.
- **Deduction source.** Cushing–Pascoe, arXiv:1611.01192 (n! ± 1). CrowdMath, arXiv:2005.07321
  (2ⁿ ± 1). Both are quoted on the page.
- **Proof sketch.** Lemma P: powerful m ⇒ rad(m)² ≤ m. Triples (1, 2ⁿ, 2ⁿ+1), (1, 2ⁿ−1, 2ⁿ),
  (1, n!, n!+1) and (1, n!−1, n!) are coprime and distinct for distinct n. If the odd member x is
  powerful, then rad(abc) ≤ 2√x (powers of 2), or rad ≤ primorial(n)·√x ≤ 4ⁿ√x (Mathlib
  `primorial_le_4_pow`). With ε = 1/2: (2√x)^{3/2} < x, and (4ⁿ√x)^{3/2} < x once n! > 4^{6n}. So
  infinitely many powerful values would give infinitely many abc exceptions. All of this is
  elementary: one finiteness-to-eventually step, plus Lemma P from `Nat.factorization`.
- **Lean elsewhere.** rjwalters/lean-genius `Erdos936Problem.lean` *axiomatises* both results
  (`axiom cushing_pascoe_theorem`), so it proves nothing. kavanaghpatrick/aristotle-math-problems has
  submission files for all four variants (contents not read, *(unverified)*; they look like
  unconditional attempts). No FC PR on 936 except a closed #2974.
- **Catch.** Tier C. The deduction is a textbook abc exercise, so it is worth doing only as a
  bundle with candidate 3 (shared Lemma P, the rad bound and the factorial bound). "abc ⇒ X" carries
  little weight while abc itself is open. The honest label would be "abc-consequence"; the workspace
  has no such label, so the owner has to decide.

### 3. abc ⇒ `erdos_977.variants.factorial` (P(n!+1)/n → ∞) · Class 2 · effort S

- **Statement.** FC `977.lean`, `research open`, no formal_proof:
  ```lean
  theorem erdos_977.variants.factorial :
      Tendsto (fun n : ℕ ↦ (Nat.maxPrimeFac (n.factorial + 1) : ℝ) / n) atTop atTop
  ```
  The site says "appears to be open still" (page last edited 01 Feb 2026). In the thread, StijnC
  (2025-10-12) notes only that abc implies it.
- **Premise.** `ABC.abc`, open. Source: Murty–Wong 2002 (P(n!+1) > (1+o(1)) n log n under abc).
- **Proof sketch.** Apply abc with ε = 1 to (1, n!, n!+1). For large n,
  n! < rad(n!(n!+1))² ≤ (primorial(n)·primorial(P))² ≤ 4^{2(n+P)}, with P = maxPrimeFac(n!+1),
  since rad(n!+1) divides primorial(P). So log n! ≤ 2(n+P) log 4. With log n! ≥ n log n − n
  (Mathlib Stirling-type lower bound; exact lemma name *(unverified)*), P ≥ n log n/(2 log 4) − 2n,
  so P/n → ∞. Even "c < rad(abc)² with finitely many exceptions" suffices.
- **Lean elsewhere.** None found. I searched FC PRs ("977", "Murty", "abc conjecture"), GitHub code
  (`erdos_977.variants.factorial`, which hits only FC, ryantuck mirrors and mathdb-lean/plby, all of
  them for the main 2ⁿ−1 statement), and the plasma 977 page (Stewart claims only).
- **Catch.** As for candidate 2. A day of work together with 936.

### 4. abc ⇒ #373 (finitely many n! = a₁!⋯a_k!) · Class 2 · effort M *(argument unverified)*

FC `373.lean`, `erdos_373` (open), plus solved-but-sorry `variants.of_limit` (H: P(n(n+1))/log n → ∞)
and `variants.of_lower_bound`. Luca (Math. Proc. Camb. Phil. Soc. 2007) proves finiteness under abc
(Plasma claim page `E0373/claims/2007_11_01_luca`). I have not read Luca's argument. abc on
(n, 1, n+1) gives only P(n(n+1)) ≥ (1−ε) log n, which falls short of both FC hypotheses (they need
→ ∞·log n or > 4 log n), so Luca must use more structure. FC's sibling 393 (`variants.luca`) already
has a Palomar Lean proof (PALOMAR-2026-11-02-000011), which shows someone works this seam. Check
before starting.

### 5. Prime k-tuples (qualitative) ⇒ ¬`erdos_855` (second Hardy–Littlewood conjecture) · Class 2 · effort M–L

FC `855.lean`: `erdos_855 : ∀ᶠ (xy : ℕ × ℕ) in atTop ×ˢ atTop, π (xy.1 + xy.2) ≤ π xy.1 + π xy.2`
(open). The source is Hensley–Richards 1973 (Acta Arith. 25), quoted on the page (thread read
2026-11-26). Catch: FC's formulation makes x and y both large, so one dense admissible tuple
(diameter 3159) is not enough. You need ρ*(y) > π(y) for arbitrarily large y, which means the
Hensley–Richards construction plus an explicit inequality of the form π(2x) < 2π(x) − c·x/log²x
(Rosser–Schoenfeld type). That is not in Mathlib. riemann-hypothesis's unconditional PNT inputs
might give it *(unverified)*. FC PR #8223 (open) adds only RH-conditional variants. lean-genius
axiomatises the incompatibility. Use the hypothesis shape of FC 884 (`hHL : ∀ H : Finset ℤ,
admissible → {n | ∀ h ∈ H, Prime (n+h)}.Infinite`).

## 4. Rejected (kept in the edges file so nobody repeats them)

- **#169 tail question [Er80] and f(k) < ∞ from #3**: FC PR #8269 (mnn31, Lean proof linked,
  2026-11-24), PR #6685, Plasma's OpenAI claim page.
- **abc ⇒ #393**: Palomar Lean proof (FC `erdos_393.variants.luca`).
- **HL ⇒ ¬#884**: the unconditional Lean disproof (Jayyhk/erdos-lean) makes the conditional
  variant trivial.
- **Schinzel / Dickson ⇒ #252**: moot after tokengr1nder's unconditional Lean proof.
- **Goldbach-strong ⇒ #418-odd, 8p²−1 primes ⇒ #913, Pilatte/Shiu ⇒ #427, #40 ⇒ #28**: already
  proved inside FC.
- **#857 ⇒ #856 (c_k < 1)**: real, but needs Tang–Zhang's reduction and the weak-sunflower bound,
  neither in Lean. L.
- **abc ⇒ #208 and #145 (Granville 1998)**: polynomial-abc input, not elementary. L.
- **AFM25 conditional ⇒ #627**: Ramsey-limit hypothesis; FC `variants.conditional` is solved with
  sorry. L.
- **Erdős's π-hypothesis ⇒ #950 (f ≪ log log log n)**: no proof in the source. XL.
- **Fermat primes ⇒ #1113**: the contrapositive heuristic has no written proof. XL.
- **#15 (Tao, strong HL)**, **#428 (limsup only)**, **#891 (modified statement)**,
  **#371 / #928 / #408 (Elliott–Halberstam)**: deep or about a different statement.

## 5. What was searched and what was not

- Searched: the teorth database diff; FC git history (200 commits) and the full Erdős declaration
  table; harvest commentary for cross-references and for abc, Schinzel, Dickson, HL, Elliott–Halberstam
  and Cramér conditionals; the plasma-ai wiki for 3, 140, 142, 169, 252, 373, 855, 856, 936 and 977;
  FC PR search (142, 140, 169, 977, 936, 855, r_k, Kelley, OpenAI, Murty, abc); GitHub code search
  (erdos_169, Erdos169, erdos_936, erdos_977, Erdos855); live pages for 3, 140, 142, 169, 855 (thread),
  857, 936 (thread) and 977 (thread). 1337isnot1337/solved-conjectures: `CONTENTS.md` and the
  first 40 of 225 remote branches have no hit for 936, 977, 142, 140, 169, 373 or 855.
- Not checked: erdosproblems.ai and erdosproblemaday pages (I relied on the plasma-ai wiki instead);
  the contents of the aristotle-math-problems 936 files; Luca 2007's argument; whether the OAI
  library builds; the "last edited" dates on the 142, 140 and 936 pages (Exa's snapshots did not
  show them; Plasma reports 142 as last edited 4 April 2026). GitHub code search hit its rate
  limit once.
