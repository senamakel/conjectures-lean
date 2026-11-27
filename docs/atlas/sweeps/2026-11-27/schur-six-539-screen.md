# Schur (S(6)\ge 539) certificate screen

**Checked:** 27 November 2026. **Outcome:** no witness in the bounded radius-two
neighborhood described below. This does not prove (S(6)<539).

## Prior art and status

Chen, Zhu and Long published an explicit six-class partition of
\(\{1,\ldots,537\}\), with 131 inequivalent examples found by their search
[arXiv:2610.31362](https://arxiv.org/abs/2610.31362). Adam McKenna then published
an explicit partition through 538, checked by a direct program and a Lean 4
kernel proof ([Zenodo DOI 10.5281/zenodo.23937655](https://doi.org/10.5281/zenodo.23937655),
[certificate and Lean files](https://github.com/mysticflounder/schur-538)). The
Lean theorem checks the literal 538-position coloring, with equal summands
allowed; it reports `propext` and `Quot.sound` and uses neither `sorry` nor
`native_decide`. The preprint is not human peer reviewed.

The November follow-up in
[`jeffchen006/Schur-Number-6/evolve538/README.md`](https://github.com/jeffchen006/Schur-Number-6/tree/main/evolve538)
reports a 47-generation, eight-island, roughly 24.5-hour evolutionary search
with 1,676 programs and 2,359 longer runs. It reached no 539 word. The reported
539 experiments include blank-start program runs, growth with a prefix of at
least 50 fixed, and partial residue-class searches at (N=539) and (N=540)
(between 0% and 83% of the cells). That README does not report a systematic
single-coordinate recoloring of the stored 538 words.

The evolved-word file contains 1,021 valid length-538 records, 995 distinct up
to color renaming. I added McKenna's two published 538 words if their
color-renaming classes were absent from that corpus. The two baselines are
distinct up to color renaming. The bounded script fetches all three inputs from
commit-pinned raw GitHub URLs and checks their SHA-256 values before inspecting
them.

No November claim of (S(6)\ge539) surfaced in Exa searches for the exact bound
and wording through 27 November. The exact OMA catalogue search for “Schur”
returned zero candidates, and GitHub PR searches for `Erdos483`, “Schur number”,
and `538` returned no Schur-number-six PR (the numeric search's matches were
unrelated). At the OMA formal-conjectures pin
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, LemmaGraph returns:

```lean
def Erdos483.HasTriple {k N : ℕ} (χ : Fin N → Fin k) : Prop :=
  ∃ a b c : Fin N, (a.val + 1) + (b.val + 1) = c.val + 1 ∧
    χ a = χ b ∧ χ b = χ c

def Erdos483.Forces (k N : ℕ) : Prop :=
  ∀ χ : Fin N → Fin k, Erdos483.HasTriple χ
```

The documentation says index (i) denotes (i+1) and equal summands are
allowed. Thus a verified coloring of `[1,539]` is exactly a witness to
`¬ Erdos483.Forces 6 539` at that registry statement; formal-conjectures does
not define a Schur-number function. LemmaGraph's result is pinned at
`v4.33.1+0df444a3`.

LivingBrain tools were not loaded in this session, so no memory search was
available.

## Bounded search and stop rule

The persisted script
[`schur-six-539-neighborhood.py`](schur-six-539-neighborhood.py) extends that
screen to at most two changed old positions and includes both published
McKenna words. Neither baseline was in the evolved-word corpus, giving 997
distinct input words up to color renaming. For a chosen appended color (c),
each pair
\((x,539-x)\) already colored (c,c) must be hit by a recolored endpoint.
These 269 complementary pairs are disjoint. Hence:

* zero such pairs gives an immediate extension and stops with that witness;
* one pair requires at least one of its two endpoints to change. The script
  checks both one-endpoint recolors and every two-position support meeting that
  pair, with all (5^2) replacement-color choices;
* two pairs require one changed endpoint in each, with (2\cdot5\cdot2\cdot5=100)
  assignments per appended color;
* more than two pairs cannot be fixed with two recolors and are skipped.

The old sum-free check is reduced to triples touching a changed position. The
script counts one-site conflicts, then adjusts for the at most two old Schur
triples containing both changed positions. The appended value is checked via
the complementary pairs summing to 539. Any found candidate is independently
checked against every sum-free triple on `[1,539]` before it is printed.

Before the radius-two run, the hard cap is 100,000,000 distinct candidate
colorings. The script counts the full bounded neighborhood first and refuses
to start if it exceeds the cap. It stops at the first fully verified witness,
or after exhausting the complete counted neighborhood; there is no automatic
cap increase or unbounded solver run.

## Run and result

Run from the worktree root:

```sh
python3 docs/atlas/sweeps/2026-11-27/schur-six-539-neighborhood.py --inventory
python3 docs/atlas/sweeps/2026-11-27/schur-six-539-neighborhood.py --max-candidates 100000000
```

The inventory found that all 5,982 input-word/appended-color combinations have
more than two complementary pairs colored (c,c). The extension pairs are
disjoint, and changing at most two old positions can affect at most two of
them. Therefore the additional radius-two candidate set is empty. The script
exhaustively checked the radius-zero/one neighborhood: 16,097,562 candidate
colorings (5,982 with no old recolor and 16,091,580 with one). It found no
witness. The total bounded search count was below the 100,000,000 cap; it
completed in 15.3 seconds. The radius-two stage skipped all 5,982 word/color
combinations by the pair-count obstruction and tested zero additional
assignments.

An independent small-instance check by the parent agent compared the
change-aware old-triple test against direct triple enumeration for every
two-recolor mutation of every 3-color sum-free word of length 7: 21,672
mutations, all agreed. No two-recolor candidate survived the complementary-pair
filter here, so this check validates the helper logic rather than a surviving
candidate.

This screen only tests the listed stored certificates and the specified
Hamming neighborhood; it says nothing about other six-colorings of `[1,538]`
or a construction from scratch.
