# Porting notes: the Montgomery–Vaughan large sieve

Source: [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) at commit `330a61c`,
Copyright 2026 Charlie Reams, Apache License 2.0 (`../LICENSE-ternary-goldbach`,
`../NOTICE-ternary-goldbach`).

| File here | Source file |
|---|---|
| `Shan.lean` | `TernaryGoldbach/Prelim/Shan.lean` |
| `HilbertIdentity.lean` | `TernaryGoldbach/Prelim/HilbertIdentity.lean` |
| `HilbertReal.lean` | `TernaryGoldbach/Prelim/HilbertReal.lean` |
| `HilbertCsc.lean` | `TernaryGoldbach/Prelim/HilbertCsc.lean` |
| `LargeSieveMVProof.lean` | `TernaryGoldbach/Prelim/LargeSieveMVProof.lean` |
| `Montgomery.lean` | `TernaryGoldbach/MinorArcs/Montgomery.lean` |
| `SumMuSqPhi.lean` | `TernaryGoldbach/Prelim/SumMuSqPhi.lean` |

Changes, applied to every file:

* module paths `Cramer.Vendor.LS.*`, imports rewritten to match;
* the namespace `TernaryGoldbach` is renamed `Cramer.Vendor.TG`, so the files do not clash with
  the copy of ternary-goldbach that schoenfeld-rh vendors. The exponential `e` still comes from
  `TernaryGoldbach.CircleMethod`, which schoenfeld-rh vendors (lake dependency);
* a header naming the source commit, file and licence.

No statement was changed. One proof repair for Lean `v4.36.0` / Mathlib `fc4f59e5`:

* `Shan.lean`, at the `convexOn_zpow … .subset` call: the subset argument is given explicitly as
  `(show Set.Ici (1 : ℝ) ⊆ Set.Ioi 0 from …)`.

The other six files are unchanged apart from the renaming.

`Cramer/CMS/BrunTitchmarsh.lean` (not vendored) copies `frac_sep` and `le_dist_round_of_forall`
from the same commit's `TernaryGoldbach/MinorArcs/TypeII.lean` as `frac_sep'` and
`le_dist_round_of_forall'`, specialised to `q = 1`, `A = 0`, `u = 0`.
