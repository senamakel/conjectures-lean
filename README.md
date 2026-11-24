# The Mertens function bound under RH in Lean

Let `M(x) = ∑_{n ≤ x} μ(n)` be the Mertens function. Littlewood (C. R. Acad. Sci. Paris 154
(1912) 263–266; see Titchmarsh, *The Theory of the Riemann Zeta-Function*, ch. 14) proved that
the Riemann hypothesis implies `M(x) = O(x^{1/2+ε})` for every `ε > 0` (the converse also holds
and is not formalised here). The best unconditional bound is of the form
`M(x) ≪ x exp(-c (log x)^{3/5} (log log x)^{-1/5})` (Walfisz, via the Vinogradov–Korobov
zero-free region).

This project also proves Titchmarsh's sharper bound `|M(x)| ≤ √x · exp(25 log x / log log x)`
for all large `x` under RH (Titchmarsh, J. London Math. Soc. 2 (1927) 247–254, improving
Landau, Rend. Circ. Mat. Palermo 48 (1924) 277–280), and the bound
`1/|ζ(σ+it)| ≤ exp(C log t / log log t)` on `σ ≥ 1/2 + 8/log log t` that it rests on.

**Literature status: RH-equivalent** (Titchmarsh's bound: **RH-consequence**). The main library
is a complete Lean proof that RH implies these bounds, following Littlewood (1912), Riesz (1916),
Hardy–Littlewood (1916), Landau (1924) and Titchmarsh (1927), together with the convergence of
`∑ μ(n) n^{-s}` on `Re s > 1/2` (Littlewood 1912), the bound `∑_{n ≤ x} λ(n) = O(x^{1/2+ε})` for
the Liouville function, and the Farey-sequence bounds of Franel (1924) and Landau (1924); each
of the `x^{1/2+ε}`-type bounds is RH in another form. `Unconditional/` proves every one of them
unconditionally in Lean, with the certified Lean proof of RH (Alpöge 2026) from
leanprover-community/riemann-hypothesis. Redheffer's identity `det R_n = M(n)` is **known**
(Redheffer 1977, no hypothesis); this is a complete Lean proof of it.

The project formalises Littlewood's implication together with its standard companions:

* `1/ζ(s) ≪_{ε,δ} |t|^ε` on `Re s ≥ 1/2 + δ`, `|t| ≥ 1`, under RH (Titchmarsh §14.2);
* Riesz (Acta Math. 40 (1916)): the Riesz function `∑_{k≥1} (-1)^{k+1} x^k / ((k-1)! ζ(2k))` is
  `O(x^{1/4+ε})` under RH;
* Hardy–Littlewood (Acta Math. 41 (1916) 119–196): `∑_n μ(n)/n · e^{-x/n²}` converges and is
  `O(x^{-1/4+ε})` under RH;
* Redheffer (1977): `det R_n = M(n)` for Redheffer's matrix (no hypothesis), hence
  `det R_n = O(n^{1/2+ε})` under RH;
* Littlewood (1912): under RH, `∑ μ(n) n^{-s}` converges to `1/ζ(s)` for every `Re s > 1/2`
  (Titchmarsh, ch. 14). The series converges only conditionally for `1/2 < Re s ≤ 1`, so the
  statement is about the limit of its partial sums;
* the Liouville function: under RH, `L(x) = ∑_{n ≤ x} λ(n) = O(x^{1/2+ε})`. The equivalence with
  RH comes from `ζ(2s)/ζ(s) = s ∫₁^∞ L(t) t^{-s-1} dt` (stated, e.g., in Humphries, J. Number
  Theory 133 (2013) 545–582, arXiv:1108.1524; this attribution was not checked against an older
  primary source);
* Franel (Göttinger Nachrichten 1924, 198–201) and Landau (same volume, 202–206): with
  `f_1 < ⋯ < f_A` the Farey fractions of order `N` in `(0, 1]`, under RH
  `∑_k (f_k − k/A)² = O(N^{−1+ε})` (Franel) and `∑_k |f_k − k/A| = O(N^{1/2+ε})` (Landau).

Only the RH ⇒ bound directions are in scope.

```lean
theorem Mertens.invZeta_bound_of_RH (hRH : RiemannHypothesis) : Mertens.InvZetaBound
theorem Mertens.mertens_of_RH (hRH : RiemannHypothesis) : Mertens.MertensBound
theorem Mertens.riesz_of_RH (hRH : RiemannHypothesis) : Mertens.RieszBound
theorem Mertens.hardyLittlewood_of_RH (hRH : RiemannHypothesis) : Mertens.HardyLittlewoodBound
theorem Mertens.det_redheffer (n : ℕ) (hn : 1 ≤ n) : (Mertens.redheffer n).det = Mertens.mertens n
theorem Mertens.redheffer_of_RH (hRH : RiemannHypothesis) : Mertens.RedhefferBound
theorem Mertens.moebiusSeries_of_mertensBound (hMB : Mertens.MertensBound) :
    Mertens.MoebiusSeriesConverges
theorem Mertens.moebiusSeries_of_RH (hRH : RiemannHypothesis) : Mertens.MoebiusSeriesConverges
theorem Mertens.liouville_of_mertensBound (hMB : Mertens.MertensBound) : Mertens.LiouvilleBound
theorem Mertens.liouville_of_RH (hRH : RiemannHypothesis) : Mertens.LiouvilleBound
theorem Mertens.franel_of_mertensBound (hMB : Mertens.MertensBound) : Mertens.FranelBound
theorem Mertens.franel_of_RH (hRH : RiemannHypothesis) : Mertens.FranelBound
theorem Mertens.franelLandau_of_mertensBound (hMB : Mertens.MertensBound) :
    Mertens.FranelLandauBound
theorem Mertens.franelLandau_of_RH (hRH : RiemannHypothesis) : Mertens.FranelLandauBound
theorem Mertens.norm_invZ_le_sharp (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ l : ℝ, 2 ≤ l → ∀ s : ℂ, 1 / 2 + 4 / l ≤ s.re → s.re ≤ 2 →
      ‖invZ s‖ ≤ Real.exp (A * (l ^ 2 * Real.exp l + 1)) * (|s.im| + 3) ^ (4 / l)
theorem Mertens.invZetaSharpWith_of_RH (hRH : RiemannHypothesis) : Mertens.InvZetaSharpBoundWith 8
theorem Mertens.abs_mertens_nat_le_sharp (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ l : ℝ, 8 ≤ l → ∀ N : ℕ, 1 ≤ N →
      |(mertens N : ℝ)| ≤ 8 * l * Real.exp (A * (l ^ 2 * Real.exp l + 1)) *
        ((N : ℝ) + 1) ^ (1 / 2 + 12 / l)
theorem Mertens.mertensSharp_of_RH (hRH : RiemannHypothesis) : Mertens.MertensSharpBound
```

(`mertensSharp_of_RH` is proved with `C = 25`; `invZ s = (s - 1)/ζ₁(s)` equals `1/ζ(s)` for
`s ≠ 1`.)

The statements are fixed in [`Mertens/Statement.lean`](Mertens/Statement.lean), e.g.

```lean
noncomputable def mertens (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, μ n

def MertensBound : Prop :=
  ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε)
```

The second batch of targets is in [`Mertens/Statement2.lean`](Mertens/Statement2.lean):

```lean
noncomputable def moebiusPartial (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (μ n : ℂ) / (n : ℂ) ^ s

def MoebiusSeriesConverges : Prop :=
  (∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Tendsto (moebiusPartial s) atTop (𝓝 (riemannZeta s)⁻¹)) ∧
  Tendsto (moebiusPartial 1) atTop (𝓝 0)

noncomputable def liouvilleSum (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, liouville n

def LiouvilleBound : Prop :=
  ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (liouvilleSum x : ℝ)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε)
```

and for Farey fractions

```lean
def farey (N : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun pq => pq.1 ≤ pq.2).image
    fun pq => (pq.1 : ℚ) / pq.2

def fareyFrac (N : ℕ) (i : Fin (farey N).card) : ℚ := (farey N).orderEmbOfFin rfl i

noncomputable def franelL1 (N : ℕ) : ℝ :=
  ∑ i : Fin (farey N).card, |(fareyFrac N i : ℝ) - ((i : ℕ) + 1 : ℝ) / (farey N).card|

noncomputable def franelL2 (N : ℕ) : ℝ :=
  ∑ i : Fin (farey N).card, ((fareyFrac N i : ℝ) - ((i : ℕ) + 1 : ℝ) / (farey N).card) ^ 2

def FranelLandauBound : Prop :=
  ∀ ε : ℝ, 0 < ε → franelL1 =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)

def FranelBound : Prop :=
  ∀ ε : ℝ, 0 < ε → franelL2 =O[atTop] fun N : ℕ => (N : ℝ) ^ (-1 + ε)
```

The third batch is in [`Mertens/Statement3.lean`](Mertens/Statement3.lean):

```lean
def MertensSharpBound : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |(mertens x : ℝ)| ≤ Real.sqrt x * Real.exp (C * Real.log x / Real.log (Real.log x))

def InvZetaSharpBoundWith (c : ℝ) : Prop :=
  ∃ C t₀ : ℝ, ∀ s : ℂ, t₀ ≤ |s.im| →
    1 / 2 + c / Real.log (Real.log |s.im|) ≤ s.re →
      ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (C * Real.log |s.im| / Real.log (Real.log |s.im|))

def InvZetaSharpBound : Prop := InvZetaSharpBoundWith 1
```

`MertensSharpBound` is proved in full. `InvZetaSharpBound` (Titchmarsh's region
`σ ≥ 1/2 + 1/log log t`) is the fixed target; `InvZetaSharpBoundWith 8` is proved (see
Deviations).

Mathlib's `riemannZeta 1` is a junk value rather than the pole, so at `s = 1` the statement is
the true value `∑ μ(n)/n = 0`. `liouville` is Mathlib's `ArithmeticFunction.liouville`.
`fareyFrac N i` is `f_{i+1}`, the `(i+1)`-st smallest element of `F_N`.

## Tier and provenance

| Theorem | Tier |
|---|---|
| `invZeta_bound_of_RH`, `mertens_of_RH`, `riesz_of_RH`, `hardyLittlewood_of_RH`, `redheffer_of_RH` | **C** (RH is an explicit argument) |
| `moebiusSeries_of_RH`, `liouville_of_RH`, `franel_of_RH`, `franelLandau_of_RH` | **C** |
| `moebiusSeries_of_mertensBound`, `liouville_of_mertensBound`, `franel_of_mertensBound`, `franelLandau_of_mertensBound` | **C** (the hypothesis is the Mertens bound, itself equivalent to RH) |
| `norm_invZ_le_sharp`, `invZetaSharpWith_of_RH`, `abs_mertens_nat_le_sharp`, `mertensSharp_of_RH` | **C** |
| `det_redheffer` | **D** |
| `invZeta_bound`, `mertens_bound`, `riesz_bound`, `hardyLittlewood_bound`, `redheffer_bound`, `moebius_series`, `liouville_bound`, `franel_bound`, `franelLandau_bound`, `mertens_sharp_bound`, `invZeta_sharp_bound` in `Unconditional/` | **U** |

`RiemannHypothesis` is Mathlib's definition; the main library never imports
riemann-hypothesis. No target has a formal-conjectures counterpart (checked against
google-deepmind/formal-conjectures `86a2f58`: no Mertens, Redheffer, Riesz or Hardy–Littlewood
entry; checked again at `9097e2f` for the Möbius Dirichlet series, the Liouville sum and
Farey discrepancy: none; searched again 2026-11-24 for Mertens and `1/ζ` bounds near the half
line: none), so the targets are this project's own. There are no cited (tier H) hypotheses.

## Axioms

From `lake env lean scripts/print-axioms.lean` (the first six at commit `1191f36`, the next eight
on branch `finality`, the last four on branch `round5`, all 2026-11-24):

```
'Mertens.invZeta_bound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.mertens_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.riesz_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.hardyLittlewood_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.det_redheffer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.redheffer_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.moebiusSeries_of_mertensBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.moebiusSeries_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.liouville_of_mertensBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.liouville_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.franel_of_mertensBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.franel_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.franelLandau_of_mertensBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.franelLandau_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.norm_invZ_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.invZetaSharpWith_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.abs_mertens_nat_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.mertensSharp_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide`, no `sorry`, no `axiom` or `opaque` declarations.

## Proof outline

The full plan, with each step's Lean statement, is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

1. **`1/ζ ≪ |t|^ε`** (`Mertens/InvZeta.lean`). lindelof-rh supplies a holomorphic logarithm `M`
   of `ζ₁/(s+1)` on `σ > 1/2` with `‖M(σ+it)‖ ≤ C log(|t|+2)^α`, `α < 1`, on `σ ≥ 1/2 + δ`
   (Borel–Carathéodory, then three lines). Hence `‖1/ζ‖ ≤ exp ‖M‖ ≤ C_ε (|t|+2)^ε`.
2. **Line shift** (`Mertens/Shift.lean`). Cauchy's theorem on rectangles moves a vertical line
   integral across a strip when the integrand decays uniformly.
3. **Cesàro–Perron for `μ`** (`Mertens/Perron.lean`). erdos-985's `perron_weighted` at
   `Re s = 2`, moved to `σ₀ = 1/2 + ε`: `∑_{0<n<N} μ(n)(1 - n/N) = (1/2π) ∫ (1/ζ)(s) N^s/(s(s+1)) dt`.
4. **Exact differencing** (`Mertens/Littlewood.lean`). With `A(N) = ∑_{0<n<N} μ(n)(N-n)`,
   `M(N) = A(N+1) - A(N)`. The kernel difference `d = (N+1)^{s+1} - N^{s+1}` obeys
   `‖d‖ ≤ 2(N+1)^{σ+1}` and `‖d‖ ≤ ‖s+1‖(N+1)^σ`; their geometric mean with weight `θ = 2ε`
   makes the integrand `≪ (N+1)^{σ₀+θ}(1+|t|)^{-1-ε}`.
5. **Assembly** (`Mertens/Main.lean`): `|M(N)| ≤ K (N+1)^{1/2+3ε}`, so `M(x) = O(x^{1/2+ε})`.
6. **Redheffer** (`Mertens/Redheffer.lean`). The Möbius matrix `V_{ij} = μ(j/i)[i ∣ j]` is unit
   upper triangular and `V R_n` is lower triangular with diagonal `(M(n), 1, …, 1)`.
7. **Abel summation** (`Mertens/Abel.lean`, `Mertens/Weights.lean`). For a weight `w`,
   `∑ μ(n) w(n) = -∑ M(n)(w(n+1) - w(n))`. The mean value theorem gives two monomial bounds on
   `|w(n+1) - w(n)|` (`2x n^{-3}` and `32 n/x` for the Riesz weight `(x/t²)e^{-x/t²}`;
   `2 n^{-2}` and `5/x` for the Hardy–Littlewood weight `(1/t)e^{-x/t²}`), interpolated to
   `x^P n^{-1-ε}`.
8. **Hardy–Littlewood** (`Mertens/HardyLittlewood.lean`): `P = -1/4 + 2ε`.
9. **Riesz** (`Mertens/Riesz.lean`): `riesz x = ∑ μ(n)(x/n²)e^{-x/n²}` (swap of an absolutely
   convergent double series), then `P = 1/4 + 2ε`.
10. **Uniform Mertens bound** (`Mertens/Uniform.lean`): from `MertensBound`, for every `β > 1/2`,
    `|M(n)| ≤ K (n+1)^β` for all `n` (the trivial `|M(n)| ≤ n` below the threshold).
11. **Möbius series** (`Mertens/MoebiusSeries.lean`). Abel summation with `w_s(n) = n^{-s}`,
    `|w_s(n+1) - w_s(n)| ≤ |s| n^{-Re s - 1}` and `β = (1/2 + σ₁)/2`: the partial sums converge
    to `T(s) = -∑ M(n)(w_s(n+1) - w_s(n))`, uniformly on `{σ₁ < Re s, |s| < R}`, so `T` is
    holomorphic on `Re s > 1/2`. With `Z(s) = (s-1)ζ(s)` (removable singularity filled, `Z(1) = 1`),
    `T Z = s - 1` on `Re s > 1` (Mathlib's `L(μ,s) ζ(s) = 1`), hence on the half-plane by the
    identity theorem. So `T = 1/ζ` off `s = 1`, and `T(1) = 0`. No RH beyond the Mertens bound.
12. **Liouville** (`Mertens/Liouville.lean`). `λ * 1 = 1_{squares}` (both multiplicative, equal at
    prime powers), so `λ = 1_{squares} * μ` and `L(N) = ∑_{d² ≤ N} M(⌊N/d²⌋)`; with
    `β = 1/2 + ε`, `|L(N)| ≤ K 2^β N^β ∑_d d^{-2β}`.
13. **Farey counting** (`Mertens/FareyCount.lean`). Two Farey fractions of order `N` are at least
    `1/N²` apart, and for `0 ≤ x ≤ 1`, `#{f ∈ F_N : f ≤ x} = ∑_{q ≤ N} ⌊q x⌋ M(N/q)` (count the
    coprime `p ≤ qx` by Möbius over `d ∣ q`, then swap the convolution). Also `∑_{q ≤ N} M(N/q) = 1`.
14. **The key integral** (`Mertens/FareyAlg.lean`, `Mertens/FareyIntegral.lean`):
    `∫₀¹ {qx}{rx} dx = 1/4 + gcd(q,r)²/(12qr)`. Hermite's identity
    `{qx} = ∑_{i<q} {x + i/q} − (q−1)/2` reduces it to `∫₀¹ {x+a}{x+b} dx = 1/4 + B₂({b−a})/2`;
    the distribution relation `∑_{j<r} B₂({u + j/r}) = B₂({ru})/r` and
    `∑_{i<q} B₂({ri/q}) = gcd(r,q)²/(6q)` (multiplication by a unit permutes residues) finish it.
15. **Discrete versus continuous** (`Mertens/FareyDiscrete.lean`). With
    `G(x) = ∑_{q ≤ N} M(N/q){qx} = A x − #{f ≤ x}`, the `(i+1)`-st fraction satisfies
    `f − (i+1)/A = G(f)/A`. On `[f − 1/N², f)` no other Farey fraction occurs, so
    `G(f) = G(x) + A(f − x) − 1` there; integrating over these disjoint intervals gives
    `∑_f G(f)² ≤ 3N² ∫₀¹ G² + 3A(A²/N⁴ + 1)`.
16. **Franel and Landau** (`Mertens/Franel.lean`). `∫₀¹ G² = 1/4 + (1/12)∑ c_q c_r gcd(q,r)²/(qr)`,
    and `|c_q| ≤ K 2^β N^β q^{−β}` with `∑_{q,r} gcd(q,r)² (qr)^{−1−β} ≤ ζ(1+β)² ζ(2β)` (write
    `gcd² ≤ ∑_{d∣q, d∣r} d²`) gives `∫₀¹ G² ≪ N^{2β}`. With `N²/8 ≤ A ≤ N²` (the coprime pairs
    number `∑ μ(d)⌊N/d⌋² ≥ N²/4`), `∑_k δ_k² = A^{−2}∑_f G(f)² ≪ N^{2β−2}`; Cauchy–Schwarz gives
    `(∑_k |δ_k|)² ≤ A ∑_k δ_k² ≪ N^{2β}`.
17. **`log |ζ|` from below, `t ≥ 1`** (`Mertens/SharpLower.lean`). littlewood-rh's explicit
    formula `log x · (-ζ'/ζ(s)) = D(s,x) + Σ_ρ m_ρ (x^{ρ-s}-1)/(ρ-s)² - E_R(s,x)`, integrated over
    `σ ∈ [σ₀, 2]`, read from below. With `η = σ₀ - 1/2`, `L = log x` and
    `W = Re ξ'/ξ(σ₀+it) = Σ m η/|s₀-ρ|²`: each zero contributes at least `-2η/|s₀-ρ|²` once
    `ηL ≥ 1`, so `L(log|ζ(s₀)| - log|ζ(2+it)|) ≥ -2C - 2W`, `C = (x+1)L² + x + 1 + Σ 1/k²`.
18. **Selberg's device** (`re_logDeriv_xi_le`). The explicit formula *at* `s₀` gives
    `L‖ζ'/ζ(s₀)‖ ≤ C + 2W/η`, and `W ≤ ‖ζ'/ζ(s₀)‖ + ‖R(s₀)‖` with `‖R(s₀)‖ ≤ log(3+t) + 5`. For
    `ηL ≥ 4` this gives `W ≤ 2C/L + 2‖R(s₀)‖`: no loss in `1/η`. Hence
    `1/|ζ(s₀)| ≤ exp(A + (4C + 4 log(3+t) + 20)/L)` (`norm_inv_zeta_le_large`).
19. **`|t| ≤ 1`** (`Mertens/SharpSmall.lean`). Under RH each term of `Re ξ'/ξ(σ+it)` is at most
    `3/(2(σ-1/2))` times the term at `σ = 2`, so `log|ξ(σ+it)| - (3/2) Re ξ'/ξ(2+it) log(σ-1/2)`
    is antitone, and compactness of `[1/2,2] × [-1,1]` bounds `Γ_ℝ`: `‖invZ s‖ ≤ K₁ (3/(2η))^{K₂}`.
20. **Uniform bound** (`Mertens/SharpInvZeta.lean`). Steps 18–19 with `x = e^l`:
    `‖invZ(σ+it)‖ ≤ exp(A(l² e^l + 1)) (|t|+3)^{4/l}` on `1/2 + 4/l ≤ σ ≤ 2`, every `t`. With
    `l = ½ log log t` this is `InvZetaSharpBoundWith 8`.
21. **Titchmarsh's bound** (`Mertens/SharpMain.lean`). Steps 3–4 at `σ₀ = 1/2 + 4/l` with
    `θ = 8/l` and `∫ (1+|t|)^{-1-4/l} dt = l/2`: `|M(N)| ≤ 8 l e^{A(l²e^l+1)} (N+1)^{1/2+12/l}`.
    With `l = ½ log log x`, `e^l = √(log x)`, the exponent is
    `½ log x + 24 log x/log log x + O(√(log x)(log log x)²)`, at most `½ log x + 25 log x/log log x`
    for large `x`.

| File | Content |
|---|---|
| `Mertens/Statement.lean` | target definitions |
| `Mertens/InvZeta.lean` | Step 1, `invZeta_bound_of_RH` |
| `Mertens/Shift.lean` | Step 2, contour shift across a strip |
| `Mertens/Perron.lean` | Step 3, Perron integrand bounds and the shifted formula |
| `Mertens/Littlewood.lean` | Step 4, differencing and the pointwise bound |
| `Mertens/Main.lean` | Step 5, `mertens_of_RH` |
| `Mertens/Redheffer.lean` | Step 6, `det_redheffer` |
| `Mertens/RedhefferBound.lean` | `redheffer_of_RH` |
| `Mertens/Abel.lean` | Step 7, Abel summation and interpolation |
| `Mertens/Weights.lean` | Step 7, the two weights and their differences |
| `Mertens/HardyLittlewood.lean` | Step 8, `hardyLittlewood_of_RH` |
| `Mertens/Riesz.lean` | Step 9, `riesz_eq`, `riesz_of_RH` |
| `Mertens/Statement2.lean` | second batch of target definitions |
| `Mertens/Uniform.lean` | Step 10, `abs_mertens_le_of_mertensBound` |
| `Mertens/MoebiusSeries.lean` | Step 11, `moebiusSeries_of_RH` |
| `Mertens/Liouville.lean` | Step 12, `liouville_of_RH` |
| `Mertens/FareyCount.lean` | Step 13, separation and the counting identity |
| `Mertens/FareyAlg.lean` | Step 14, Hermite, distribution relation, `∑ B₂({ri/q})` |
| `Mertens/FareyIntegral.lean` | Step 14, `integral_fract_mul_fract_mul` |
| `Mertens/FareyDiscrete.lean` | Step 15, `sum_G_sq_le` |
| `Mertens/Franel.lean` | Step 16, `franel_of_RH`, `franelLandau_of_RH` |
| `Mertens/Statement3.lean` | third batch of target definitions |
| `Mertens/SharpLower.lean` | Steps 17–18, `norm_inv_zeta_le_large` |
| `Mertens/SharpSmall.lean` | Step 19, `norm_invZ_le_small` |
| `Mertens/SharpInvZeta.lean` | Step 20, `norm_invZ_le_sharp`, `invZetaSharpWith_of_RH` |
| `Mertens/SharpMain.lean` | Step 21, `mertensSharp_of_RH` |
| `Unconditional/MertensUnconditional.lean` | one-line discharges of RH |

## Deviations from the literature

* **No sharp-cutoff Perron formula.** Littlewood's proof truncates Perron's integral. Here the
  exact identity `M(N) = A(N+1) - A(N)` and the interpolated bound on the difference kernel
  replace it (step 4), so only the absolutely convergent Cesàro kernel is used. The exponent is
  the same, `1/2 + ε`.
* **Hardy–Littlewood series.** `∑ μ(n)/n · e^{-x/n²}` converges only conditionally, so
  `hardyLittlewood` is the limit of the partial sums `hlPartial`, and `HardyLittlewoodBound`
  asserts that the limit exists for every `x > 0` as well as the bound. (A `tsum` would be
  Mathlib's junk value `0`.)
* The Riesz and Hardy–Littlewood bounds are derived from the Mertens bound by partial
  summation rather than by a Mellin–Barnes contour shift; the exponents are the classical ones.
* The Möbius-series and Liouville theorems are derived from the Mertens bound alone, not from a
  contour integral for `1/ζ`; the classical statements are the same.
* Franel–Landau. Franel's exact identity for `∑ δ_k²` (via Dedekind sums) is not used: the
  discrete sum is compared with `∫₀¹ G²` on intervals of length `1/N²`, which costs constant
  factors only. Landau's L¹ bound is deduced from Franel's by Cauchy–Schwarz. The exponents are
  the classical ones.
* **Titchmarsh's bound, constant.** `MertensSharpBound` asks for some `C`; the proof gives
  `C = 25` (and `x₀` from a `Filter.Eventually` argument, not explicit). Simonič
  (arXiv:2109.11744) has an explicit `C ≈ 5.23` for `x ≥ 10^{10^{4.487}}`.
* **The `1/ζ` region: `c = 8` versus Titchmarsh's `c = 1`.** `InvZetaSharpBound`
  (`σ ≥ 1/2 + 1/log log t`) is not proved; `InvZetaSharpBoundWith 8` is. The argument needs
  `(σ - 1/2) log x ≥ 4` (Selberg's device absorbs `2W/(η log x) ≤ W/2`), and the crude Dirichlet
  polynomial bound `‖D‖ ≤ (x+1)(log x)²` forces `log x ≤ (1 - δ) log log t`; so any `c > 4` is
  within reach of this method and `c = 1` is not. Closing the gap needs `‖D‖ ≪ x^{1/2}(log x)²`
  (Chebyshev) and a kernel without the `-1/(ρ-s)²` term (Selberg's `Λ_x`), giving `c > 2`, or
  Titchmarsh's own route through `log ζ` and three circles. The Mertens bound does not depend on
  `c`: Step 21 uses the uniform bound of Step 20 at a fixed line, not the region.
* **Liouville.** The `L(x) = √x exp(C log x / log log x)` analogue is not stated or proved;
  `L(N) = ∑_{d² ≤ N} M(N/d²)` gives it once the bound for `M` is made uniform in `y ≤ x`
  (monotonicity of `log y / log log y`).
* **Route.** Step 17 is littlewood-rh's integrated explicit formula with the inequality reversed
  (`integral_zero_term_ge` follows the proof of littlewood-rh's `integral_zero_term_le`), not
  Titchmarsh's three-circles argument for `log ζ`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985). Dependencies: erdos-985 `9538edb` (Perron
kernel), lindelof-rh `9165bfe` (log ζ bounds) and littlewood-rh `385a84e` (explicit formula for
`ζ'/ζ`, Hadamard sum over zeros), all over HTTPS.

```
lake exe cache get
lake build
lake env lean scripts/print-axioms.lean
```

On the build box the project's own modules take about 5 minutes of wall time after the
dependencies are built; the slowest are `Mertens.Littlewood` (30–100 s), `Mertens.Statement`
(up to 65 s, mostly the Mathlib import) and `Mertens.InvZeta` (10–35 s). There is no
`native_decide`. The round-5 modules (`Mertens.Sharp*`) build in about 2 minutes of wall time
on the loaded box; `Mertens.SharpInvZeta` (42 s) and `Mertens.SharpLower` (33 s) are the slowest.

## Unconditional version

`Unconditional/MertensUnconditional.lean` imports both this project and
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`), which contains a Lean proof `riemannHypothesis : RiemannHypothesis`, and
closes the hypothesis in one line each. Each row is proved unconditionally in Lean, with the
certified proof of RH.

| Theorem | Statement | Axioms |
|---|---|---|
| `invZeta_bound` | `Mertens.InvZetaBound` | `[propext, Classical.choice, Quot.sound]` |
| `mertens_bound` | `Mertens.MertensBound` | `[propext, Classical.choice, Quot.sound]` |
| `riesz_bound` | `Mertens.RieszBound` | `[propext, Classical.choice, Quot.sound]` |
| `hardyLittlewood_bound` | `Mertens.HardyLittlewoodBound` | `[propext, Classical.choice, Quot.sound]` |
| `redheffer_bound` | `Mertens.RedhefferBound` | `[propext, Classical.choice, Quot.sound]` |
| `moebius_series` | `Mertens.MoebiusSeriesConverges` | `[propext, Classical.choice, Quot.sound]` |
| `liouville_bound` | `Mertens.LiouvilleBound` | `[propext, Classical.choice, Quot.sound]` |
| `franel_bound` | `Mertens.FranelBound` | `[propext, Classical.choice, Quot.sound]` |
| `franelLandau_bound` | `Mertens.FranelLandauBound` | `[propext, Classical.choice, Quot.sound]` |
| `mertens_sharp_bound` | `Mertens.MertensSharpBound` | `[propext, Classical.choice, Quot.sound]` |
| `invZeta_sharp_bound` | `Mertens.InvZetaSharpBoundWith 8` | `[propext, Classical.choice, Quot.sound]` |

```
scripts/check-unconditional.sh [RH_DIR]
```

Last run 2026-11-24 on this project's commit `95be863` (branch `round5`) against
riemann-hypothesis `507a75d91d` (linked from the community cache, not rebuilt): exit 0, 29 min
wall time on a heavily loaded box, output

```
'invZeta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'mertens_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'riesz_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'hardyLittlewood_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'redheffer_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'moebius_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'liouville_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'franel_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'franelLandau_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'mertens_sharp_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'invZeta_sharp_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of riemann-hypothesis cache, about 19 GB of RAM and roughly 900k
open files (on Linux, `sudo prlimit --pid $$ --nofile=2000000:2000000` first).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This
check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. erdos-985, lindelof-rh and littlewood-rh are lake dependencies.
`Mertens.integral_zero_term_ge` and `Mertens.integral_zeroSum_ge` follow the proofs of
littlewood-rh's `integral_zero_term_le` and `integral_zeroSum_le` (same owner) with the
inequalities reversed.
