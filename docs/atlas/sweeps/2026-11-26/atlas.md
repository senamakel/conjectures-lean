# Lane `atlas`: implication edges in the Conjecture Atlas

Date 2026-11-26. Research only. Nothing was built, and no repository was edited. The scripts and
intermediate dumps are in `scratchpad/discovery/atlas-work/` (`extract.py`, `dump.py`,
`erdos_xref.py`, `hits.jsonl`, `open_dump2.txt`, `xref_open_resolved.txt`). Every Python run used
`-I`. Edges, including the rejected ones, are in `atlas.edges.jsonl`.

The scope changed mid-task (coordinator message): rows from every field qualify and are ranked
equally. My extraction already covered every field.

## 1. Atlas schema, briefly

`data/conjectures.jsonl` holds 2,196 rows: 1,221 Erdős, 463 formal-conjectures, 408 Wikipedia and
104 hand-curated. `data/ranked.jsonl` holds the same rows with `difficulty{score,tier}` and
`agent{score,band,opportunity}`. `opportunity` is the ranking key used below. The fields
(`research/schema/conjecture.schema.json`) are:

- `status`: `open | partially_resolved | contested | independent | resolved`. There are 1,347
  open rows, 787 resolved and 55 partially resolved.
- Difficulty: `signals{consensus_hardness, barrier_strength, prerequisite_depth,
  attack_intensity, age, partial_progress}`, each 0–5.
- Agent affinity: `agent_signals{refutability, computational_surface, statement_formality,
  search_space_structure, literature_density, machinery_depth}`, each 0–5.
- Free text: `why_hard`, `progress`, `agent_notes`, `attempts[]`.
- `lean{declaration, template, category, formal_proof, ...}` comes from formal-conjectures.
- `provenance{dataset, source_ref, harvested}`. The Erdős harvest is dated 2026-09-09.

**There is no typed dependency field.** The only relation is `related[]`, an untyped list of ids,
present on the 104 hand rows only. None of those links is "implied by", "equivalent to" and so
on. Every implication therefore had to be mined from prose: the row text plus the raw Erdős
`commentary` in `data/raw/erdos.jsonl`.

Branches:
- `origin/rh-grh-attack-candidates` is merged into main. Its only content is
  `research/notes/2026-11-24-rh-grh-consequences.md`, which is our own NEXT_TARGETS list.
- `origin/conjecture-20-76` (Kourovka 20.76 solver setup) and
  `origin/vkhatana/searching-understanding-space` (harness code) contain no data rows.

## 2. Extraction (whole corpus, no sampling)

- A regex pass over every row's text fields and the raw Erdős commentary looked for: follows
  from, would follow, implied by, implies, assuming, conditional on, equivalent to, special case
  of, consequence of, plus named premises (Schinzel, Dickson, Bunyakovsky, abc, Elliott–Halberstam,
  Cramér, Hardy–Littlewood, Bateman–Horn, Chowla, BSD, Vojta, Bombieri–Lang, RH/GRH).
- 534 rows matched; 305 of them are open, partially resolved or contested. I read all 305
  (`open_dump2.txt`).
- A second pass (`erdos_xref.py`) found 520 Erdős→Erdős cross-references with an implication
  keyword nearby. 90 of them join an open row to a row now marked resolved, and I read all 90.
- Only 3 atlas rows mention GRH at all. Every RH-shaped edge in the atlas (#233, #969, #985,
  #684, #770) is already done, assigned or discarded in `docs/scoping/`.

## 3. Candidates kept, easiest first

### A. Erdős 936 under abc: 2^n±1 and n!±1 are powerful only finitely often. Class 2, effort S

- **Statement.** fc `ErdosProblems/936.lean`, four declarations, all research open:
  `erdos_936.variants.two_pow_add_one : EventuallyNotPowerful (2 ^ · + 1)`, plus `two_pow_sub_one`,
  `factorial_add_one` and `factorial_sub_one`. They use
  `def EventuallyNotPowerful (a : ℕ → ℕ) : Prop := atTop.Eventually (fun n => ¬ (a n).Powerful)`.
- **Premise.** fc `Wikipedia/ABC.lean`, `ABC.abc (ε) (hε : 0 < ε) : {(a,b,c) | 0<a ∧ 0<b ∧ 0<c ∧
  Pairwise Coprime ∧ a+b=c ∧ (radical (a*b*c))^(1+ε) < c}.Finite`. The premise is open.
- **Deduction.** For powerful x, rad(x)² ∣ x, so rad(x) ≤ √x.
  - 2^n+1: take (1, 2^n, 2^n+1). The radical is at most 2√c, and (2√c)^{3/2} < c once c > 64.
  - 2^n−1: take (1, 2^n−1, 2^n), with the same bound.
  - n!±1: rad(n!) is the primorial of n, which is at most 4^n (Mathlib `primorial_le_4_pow`). Take
    ε = 1/3; then 256^n < n! for large n finishes it.
  - In each case, distinct n give distinct triples, so the finite set gives finitely many n.
- **Sources.** Cushing–Pascoe, arXiv:1611.01192, Lemma 4.3 (n!−k is left as Exercise 4.4).
  CrowdMath, arXiv:2005.07321, Thm 2.3. The erdosproblems.ai wiki notes that the 2^n−1 sign is
  covered by neither paper's stated theorem and supplies the one-line deduction.
- **Status.** Live erdosproblems.com/936 is OPEN (checked 2026-11-26). Unconditionally, every
  case is open. erdosproblemaday's report of 2026-07-28 found only finite classifications and a
  Wieferich obstruction.
- **Existing Lean.** rjwalters/lean-genius `Erdos936Problem.lean` only **axiomatizes** the result
  (`axiom abc_conjecture_holds : Prop` and `axiom cushing_pascoe_theorem`). It is not a proof.
  kavanaghpatrick/aristotle-math-problems has the open statements with `sorry`. I found no real
  proof.
- **Missing lemmas.** rad ≤ √ for powerful numbers; rad(n!) = primorial; an explicit 256^n < n!;
  bridging fc's `ABC.radical` to `Nat.Powerful`.
- **Finite computation.** None needed; only eventual statements are asked.
- **Catch.** abc is open and Mochizuki's claim is contested, so this is strictly tier C. It is a
  modest headline: a formal proof of a published two-line deduction.

### B. `erdos_891.variants.weisenberg` from Dickson. Class 2, effort S

- **Statement.** fc `ErdosProblems/891.lean`, category *research solved*, body `sorry`:
  `(k) (hk : k ≥ 2) (hdickson : type_of% Dickson.dickson_conjecture) : ∃ᶠ n in atTop, ∀ m ∈ Ico n
  (n + (∏ i ∈ range k, i.nth Nat.Prime) - 1), ω m ≤ k`.
- **Deduction.** Weisenberg's comment on erdosproblems.com/891. Let L = lcm(1..P−1), where P is
  the product of the first k primes. Dickson's conjecture applies to the linear forms
  (L/i)n' + 1 for 1 ≤ i < P; there is no fixed prime divisor because every form equals 1 at
  n' = 0. With n = L·n' + 1, each m = n + i − 1 equals i·((L/i)n' + 1). Then
  ω(m) ≤ ω(i) + 1 ≤ k, because i < p₁⋯p_k forces ω(i) ≤ k − 1.
- **Status.** #891 itself is open (live page unchanged). This fills an fc `sorry`; it does not
  settle #891.
- **Existing Lean.** None. proofbee lists the statement as open; formal-conjectures benchmarks
  carry it.
- **Missing lemmas.** `BunyakovskyCondition` and `SchinzelCondition` for linear forms with
  value 1 at 0; ω(i) ≥ k ⇒ i ≥ p₁⋯p_k.
- **Catch.** It overlaps the fc-scan lane. The value is low but the cost is low too.

### C. Erdős 647, windowed variant, from Dickson. Class 2, effort S

- **Statement.** fc `ErdosProblems/647.lean`, `erdos_647.variants.infinite`, research open:
  `∀ k, { n | ⨆ m : Set.Ioo (n - k) n, ↑m + σ 0 m ≤ n + 2 }.Infinite`. There is no conditional
  version in fc yet, so the new theorem would be `erdos_647.variants.infinite_of_dickson
  (h : type_of% Dickson.dickson_conjecture)`.
- **Source.** Erdős [Er79d], repeated on erdosproblems.com/647: the statement "follows from
  Schinzel's Hypothesis H". No proof is written there. **The construction below is mine.**
  - Take n = L·t with L = lcm(1..k−1).
  - Ask that (L/j)t − 1 be prime for 1 ≤ j < k. Then n − j = j·p_j, so
    τ(n − j) = 2τ(j) ≤ j + 2. This holds because every proper divisor of j is at most j/2, so
    τ(j) ≤ j/2 + 1.
  - Admissibility: at t = q − 1 every form is ≡ −1 (mod q), so no prime is a fixed divisor.
  - Python sanity check: k = 3, 5, 8 all give valid n (e.g. 10780560 for k = 8).
- **Status.** Live: VERIFIABLE (main question). The erdosproblems.ai wiki (Oct 2026) records only
  finite kernel-checked exclusions: Mian–Siddique arXiv:2608.17880 to 10^9 and fjordmindlabs to
  10^13. The windowed variant is open, and nobody has written up the Dickson deduction.
- **Existing Lean.** None. epoch-research/LeanOpenProblems and aristotle-math-problems have the
  `sorry` statement only.
- **Missing lemmas.** τ(j) ≤ j/2 + 1; τ(j·p) = 2τ(j) for a prime p ∤ j; handling `⨆` over
  `Set.Ioo` in ℕ (bounded, finite); trivial cases k ≤ 1.
- **Catch.** It says nothing about the £25 main question (n > 24), and Dickson is open. If we
  publish it, the deduction is ours, not Erdős's written proof.

### D. `erdos_761.variants.parts_ii_imp_i` via Erdős 760. Class 1 premise, effort S (M if porting)

- **Statement.** fc `ErdosProblems/761.lean`, research solved, `sorry`: part (ii) (large
  cochromatic number ⇒ a subgraph with large dichromatic number) implies part (i) (large
  chromatic ⇒ large dichromatic). The fc statement is in universe `u`.
- **Premise.** `erdos_760 : ∃ c > 0, ∀ V [Finite V] G m, G.chromaticNumber = m → ∃ H : G.Subgraph,
  ∃ k, k ≤ H.coe.cochromaticNumber ∧ c·m/log m ≤ k` (Alon–Krivelevich–Sudakov 1997). It is proved
  in Lean at plby/lean-proofs `src/v4.29.1/ErdosProblems/Erdos760.lean`, the formal_proof fc
  cites.
- **Deduction.** Choose m with c·m/log m ≥ m₀(ii). Take H from 760, then H′ ≤ H from (ii).
  Dichromatic number is monotone under subgraphs.
- **Status.** Both parts are open (live page). 1337 has a research note on part (i)
  (`docs/erdos-neumann-lara-research.md`, research branch) and does not settle it.
- **Missing lemmas.** Monotonicity of fc's `dichromaticNumber` under `Subgraph.coe`; composing
  subgraphs of subgraphs; c·m/log m → ∞.
- **Catch.** It only links two open questions. plby's proof is on Lean v4.29.1, so it must be
  re-proved or ported to our pin; or prove from the weaker `erdos_760.variants.erdos_gimbel`,
  which also tends to ∞ (also `sorry` in fc).

### E. Richards: first Hardy–Littlewood ⇒ not second Hardy–Littlewood. Class 2, effort M

- **Statement.** fc `Wikipedia/HardyLittlewood.lean`, `not_first_and_secondHardyLittlewoodConjecture`,
  research solved, `sorry`. HL2 is stated as ∀ x, y ≥ 2, so **one** counterexample suffices.
- **Deduction.** Hensley–Richards 1973 and Richards, Bull. AMS 80 (1974). An admissible 447-tuple
  of diameter 3158 is reported (attributed to Engelsma; attribution unverified). I computed
  π(3159) = 446. Then HL1 for that tuple gives infinitely many x with
  π(x + 3159) − π(x) ≥ 447 > π(3159).
- **Missing.**
  - The tuple itself (external data) and its admissibility certificate (decide over primes
    ≤ 447).
  - Proof that fc's C_P (a `tprod`) is positive: the factors are 1 + O(1/q²), and HasProd 0 must
    be excluded.
  - Asymptotic equivalence to a divergent integral ⇒ the count is unbounded.
- **Existing Lean.** lean-genius `Erdos855Problem.lean` axiomatizes it
  (`axiom hensley_richards_incompatibility`). I found no proof.
- **Catch.** fc's `erdos_855` is the eventual-in-both form (∀ᶠ in atTop ×ˢ atTop). Refuting that
  needs dense admissible tuples for **every** large y (the HR sieve construction), which is
  effort L and recorded as its own edge.

### F. `erdos_373.variants.of_limit` and `of_lower_bound`. Class 2, effort M (unsized)

- **Premise.** P(n(n+1))/log n → ∞, or P(n(n−1)) > 4 log n eventually. Both are open.
- **Consequence.** Only finitely many nontrivial n! = a₁!⋯a_k!.
- **Source.** Erdős [Er76d] p.28. The live page is open.
- **Status in fc.** Research solved, `sorry`. No Lean found.
- **Catch.** I did not read Erdős's argument, so the effort is a guess (unverified).

### G. `erdos_935.parts.iii` under abc. Class 2, effort M–L

- **Statement.** Q₂(n(n+1)⋯(n+ℓ))/n^{ℓ+1} → 0 for ℓ ≥ 2. Research open in fc. The live page
  credits [Fe26] (Aletheia, Google DeepMind) with "abc implies a positive answer".
- **Catch.** My pairwise-abc attempt gives only n^{ℓ+1+ε}, so the [Fe26] argument must be sharper.
  Read it before committing.

## 4. Rejected (all recorded in edges.jsonl)

- **#547 and #557 from #548.** The atlas row is stale. fc already has `formal_proof`
  (zhangjun725/erdos557).
- **#252 under Schinzel/Dickson.** erdosproblems.ai reports an anonymous kernel-checked Lean proof
  of the unconditional statement for every k (Sept 2026; unverified by me).
- **#40 ⇒ #28.** Proved in fc (`implies_erdos_28`).
- **#44 / #329 via #707.** #707 is disproved.
- **#393 (Luca, abc).** Already on the Palomar registry.
- **#364, #366, #398 under abc.** abc gives finiteness, but the questions ask for none, existence,
  or the exact set {4, 5, 7}.
- **#145 and #208 (Granville, abc).** Effort L.
- **#855, eventual form.** Effort L.
- **#15 and #420 from Zhang's bounded gaps.** The premise is not in Lean.
- **#470 (Melfi).** The premise is beyond RH.
- **#1054 (strong Goldbach).** fc's statements are already solved variants.
- **Specialisation-only edges** (#566 ⇒ #567, #562 ⇒ #564, #385 ⇔ #430, #683 ⇔ #961, #367 ~ #935):
  both sides are open, and the deductions are trivial or not stated.
- **The atlas holds no new RH/GRH edge.** Its RH-shaped rows (#233, #969, #985, #684, #770,
  Legendre, Cramér) are all done, assigned or discarded in `docs/scoping/`.

## 5. Checks performed

- **Do-not-repeat.**
  - conjectures-lean `README.md` (28 rows), `docs/NEXT_TARGETS.md` and every `docs/scoping/*.md`:
    no overlap with A–G.
  - 1337 solved-conjectures, `CONTENTS.md` on main plus a full-ref `git grep`: none of 936, 647,
    891, 855, 761 or Hensley appears as settled. Its `erdos-neumann-lara-research.md` (#761 part i)
    is open research.
- **formal-conjectures at 9097e2f.** Declarations and `formal_proof` attributes were read for 547,
  548, 557, 647, 760, 761, 891, 936, 855, 252, 364, 366, 373, 393, 398, 145, 208, 935 and 40, and
  for Wikipedia ABC, Dickson, Schinzel and HardyLittlewood.
- **GitHub** (`gh search code`): erdos_936, erdos_647, erdos_891.variants.weisenberg, erdos_855,
  erdos_252.variants.schinzel, EventuallyNotPowerful, parts_ii_imp_i,
  not_first_and_secondHardyLittlewoodConjecture. Also the plby/lean-proofs tree (46,486 paths):
  nothing for 761, 891, 647, 936, 855 or Hardy–Littlewood.
- **Live status** (erdosproblems.com, the erdosproblems.ai wiki, erdosproblemaday) checked
  2026-11-26 for 936, 647, 891, 855, 252, 761, 373, 935 and 398.
- **Not checked.** The Palomar registry index (only reached through fc citations); Mathlib for
  `dichromaticNumber` monotonicity; the source of the 447-tuple; [Fe26]'s argument; Erdős
  [Er76d]'s #373 argument.
