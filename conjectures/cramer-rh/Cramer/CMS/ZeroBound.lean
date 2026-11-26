import Cramer.CMS.Glue
import CramerCompute.CMSAll

/-!
# The zero sum of the CMS weight, with the certified constants

The weight data `φ` (`phiL`, scale `2²⁰`), `c_j = φ_{|j−16|}` for `j ≤ 32`, and the glued cell
list `cells` (`7076` entries up to `θ = 120`, checked window by window in
`CramerCompute.CMSData`). `zeroBound` is `Cramer.CMS.zeroSum_le` with every sum over the cells
replaced by the certified integers of `CramerCompute.CMSData.wv_sum_*`, the increments of `N₀`
bounded through `log θ_{i+1} ≤ (r_i/4) log 2` (`rOK`) and
`0.6931471803 < log 2 < 0.6931471808`.
-/

namespace Cramer.CMS

open Finset Real
open CramerCompute (Ent chk chainB pairSum eOK rOK D0 SS)
open CramerCompute.CMSData (wv qs)
open Schoenfeld (Zeros mult)

/-- The weight values `φ_k`, `k = 0, …, 16` (scale `2²⁰`). -/
def phiL : List ℤ := [1048576, 1033512, 988445, 913766, 809517, 674706, 510899, 331687, 167635,
  52883, 0, -8976, -3344, 0, 0, -159, 0]

/-- `c_j = φ_{|j − 16|}`. -/
def cdat (j : ℕ) : ℤ := phiL.getD (Int.natAbs ((j : ℤ) - 16)) 0

lemma cdat_zero : cdat 0 = 0 := rfl

lemma cdat_high : ∀ j, 2 * 16 ≤ j → cdat j = 0 := by
  intro j hj
  unfold cdat
  rcases Nat.lt_or_ge j 33 with h | h
  · have : j = 32 := by omega
    subst this; rfl
  · exact List.getD_eq_default _ _ (by simp [phiL]; omega)

lemma cdat_sym : ∀ j, j ≤ 2 * 16 → cdat (2 * 16 - j) = cdat j := by
  intro j hj
  unfold cdat
  congr 1
  rw [Nat.cast_sub hj]; push_cast; omega

theorem cdat_coef : coefOK cdat (2 * 16) 16 16 qs = true := by decide +kernel

theorem C1a_val : C1a cdat (2 * 16) 16 = 51457188 := by decide +kernel
theorem C1b_val : C1b cdat (2 * 16) 16 = 279458152 := by decide +kernel
theorem C2a_val : C2a cdat (2 * 16) 16 = 4550324 := by decide +kernel
theorem C2b_val : C2b cdat (2 * 16) 16 = 36577552 := by decide +kernel
theorem Asum_val : Asum cdat (2 * 16) = 740648 := by decide +kernel

/-- `Σ_j c_j`, scale `2²⁰`. -/
theorem sum_cdat : ∑ j ∈ range (2 * 16 + 1), cdat j = 11989718 := by decide +kernel

/-- The glued cell list. -/
def cells : List Ent := glue (wv.map Prod.fst)

/-! ### Facts about the glued list -/

open CramerCompute.CMSData (AllOK HeadLast Links wv_ok wv_hl wv_links) in
lemma allOK_mem : ∀ l : List (List Ent × CramerCompute.WSums), AllOK l →
    ∀ p ∈ l, CramerCompute.winOK qs 1099511627776 51457188 279458152 4550324 36577552 p.1 p.2 = true
  | [], _, p, hp => by simp at hp
  | q :: l, h, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact h.1
    · exact allOK_mem l h.2 p hp'

open CramerCompute.CMSData (HeadLast) in
lemma headLast_len : ∀ l : List (List Ent), HeadLast l → ∀ w ∈ l, 2 ≤ w.length
  | [], _, w, hw => by simp at hw
  | v :: l, h, w, hw => by
    rcases List.mem_cons.1 hw with rfl | hw'
    · obtain ⟨a, b, ha, hb, hab⟩ := h.1
      rcases w with _ | ⟨x, _ | ⟨y, t⟩⟩
      · simp at ha
      · simp at ha hb; subst ha; subst hb; omega
      · simp
    · exact headLast_len l h.2 w hw'

open CramerCompute.CMSData (Links) in
lemma links_linked : ∀ l : List (List Ent), Links l → Linked l
  | [], _ => List.IsChain.nil
  | [w], _ => List.IsChain.singleton w
  | w :: v :: l, h => List.IsChain.cons_cons h.1 (links_linked (v :: l) h.2)

lemma wins_len : ∀ w ∈ wv.map Prod.fst, 2 ≤ w.length := headLast_len _ CramerCompute.CMSData.wv_hl

lemma wins_linked : Linked (wv.map Prod.fst) := links_linked _ CramerCompute.CMSData.wv_links

lemma win_ok : ∀ w ∈ wv.map Prod.fst, ∃ v, CramerCompute.winOK qs 1099511627776 51457188 279458152
    4550324 36577552 w v = true := by
  intro w hw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
  exact ⟨p.2, allOK_mem wv CramerCompute.CMSData.wv_ok p hp⟩

lemma cells_chk : chk qs 1099511627776 cells = true :=
  chk_glue qs _ _ wins_len wins_linked fun w hw => by
    obtain ⟨v, hv⟩ := win_ok w hw
    simp only [CramerCompute.winOK, Bool.and_eq_true] at hv
    exact hv.1.1.1.1.1.1.1.1.1.1

lemma cells_eOK : chainB (eOK 51457188 279458152 4550324 36577552) cells = true :=
  chainB_glue _ _ wins_len wins_linked fun w hw => by
    obtain ⟨v, hv⟩ := win_ok w hw
    simp only [CramerCompute.winOK, Bool.and_eq_true] at hv
    exact hv.1.1.1.1.1.1.1.1.1.2

lemma cells_rOK : chainB rOK cells = true :=
  chainB_glue _ _ wins_len wins_linked fun w hw => by
    obtain ⟨v, hv⟩ := win_ok w hw
    simp only [CramerCompute.winOK, Bool.and_eq_true] at hv
    exact hv.1.1.1.1.1.1.1.1.2

lemma cells_pairSum (f : Ent → Ent → ℕ) (proj : CramerCompute.WSums → ℕ)
    (hf : ∀ p ∈ wv, CramerCompute.winOK qs 1099511627776 51457188 279458152 4550324 36577552 p.1 p.2 =
      true → pairSum f p.1 = proj p.2) :
    pairSum f cells = (wv.map (fun p => proj p.2)).sum := by
  rw [cells, pairSum_glue f _ wins_len wins_linked, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  exact hf p hp (allOK_mem wv CramerCompute.CMSData.wv_ok p hp)

lemma cells_a1G : pairSum CramerCompute.fA1G cells = 4252035564110250469740648 := by
  rw [cells_pairSum _ (fun v => v.a1G), CramerCompute.CMSData.wv_sum_a1G]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.2
lemma cells_a1e : pairSum CramerCompute.fA1e cells = 760852761666848834989 := by
  rw [cells_pairSum _ (fun v => v.a1e), CramerCompute.CMSData.wv_sum_a1e]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.2
lemma cells_a2Gp : pairSum CramerCompute.fA2Gp cells = 463585232095674405339284 := by
  rw [cells_pairSum _ (fun v => v.a2Gp), CramerCompute.CMSData.wv_sum_a2Gp]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2
lemma cells_a2Gn : pairSum CramerCompute.fA2Gn cells = 44601726036410213767724532 := by
  rw [cells_pairSum _ (fun v => v.a2Gn), CramerCompute.CMSData.wv_sum_a2Gn]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2
lemma cells_a2ep : pairSum CramerCompute.fA2ep cells = 5587348473184294079485 := by
  rw [cells_pairSum _ (fun v => v.a2ep), CramerCompute.CMSData.wv_sum_a2ep]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2
lemma cells_a2en : pairSum CramerCompute.fA2en cells = 1037532018656752372080 := by
  rw [cells_pairSum _ (fun v => v.a2en), CramerCompute.CMSData.wv_sum_a2en]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2
lemma cells_tvG : pairSum CramerCompute.fTVG cells = 15568535259931704074 := by
  rw [cells_pairSum _ (fun v => v.tvG), CramerCompute.CMSData.wv_sum_tvG]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2
lemma cells_tve : pairSum CramerCompute.fTVe cells = 1207134689330252 := by
  rw [cells_pairSum _ (fun v => v.tve), CramerCompute.CMSData.wv_sum_tve]
  intro p _ h; simp only [CramerCompute.winOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ### The endpoints of the glued list -/

lemma wv_map_eq : wv.map Prod.fst = CramerCompute.CMSData.w0000 :: (wv.tail.map Prod.fst) := rfl

lemma wv_map_ne : wv.map Prod.fst ≠ [] := by rw [wv_map_eq]; exact List.cons_ne_nil _ _

lemma cells_len : 2 ≤ cells.length := two_le_length_glue (wv.map Prod.fst) wv_map_ne wins_len

lemma cells_head : cells.getD 0 default = ⟨0, 0, 18446744073709551616, 18446744073709551616, 0, 0, 0,
    13182834354755211737, 72271341813760, -20⟩ := by
  apply getD_zero_eq
  rw [cells, wv_map_eq, glue_head _ (by decide) _]
  exact CramerCompute.CMSData.w_first_head

lemma cells_second : (cells.getD 1 default).N = 32768 := rfl

set_option maxRecDepth 100000 in
lemma cells_last : cells.getD (cells.length - 1) default = ⟨125829120, 19, 15018987992987944400,
    15018987992987944415, 0, 0, 0, 20625534903171, 639958350772, 28⟩ := by
  apply getD_last_eq
  rw [cells, glue_getLast? _ wins_len wv_map_ne]
  rw [show (wv.map Prod.fst).getLast? = some CramerCompute.CMSData.w0707 from rfl]
  exact CramerCompute.CMSData.w_last_last

/-! ### The explicit bound -/

/-- `log 2`, rounded up and down. -/
def l2u : ℝ := 0.6931471808
/-- See `l2u`. -/
def l2l : ℝ := 0.6931471803

/-- The bound for the zero sum, as a function of `h = s/m`. -/
noncomputable def Zc (h : ℝ) : ℝ :=
  2 * ((1 / (2 * π * h)) *
      (Real.log (1 / (2 * π * h)) * (4252035564110250469740648 / (1099511627776 * 1048576) +
          h * (760852761666848834989 / (1048576 * 1048576))) +
        l2u / 4 * (463585232095674405339284 / (1099511627776 * 1048576) +
          h * (5587348473184294079485 / (1048576 * 1048576))) -
        l2l / 4 * (44601726036410213767724532 / (1099511627776 * 1048576) +
          h * (1037532018656752372080 / (1048576 * 1048576)))) +
    Ero (120 / h) * ((13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
      h * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576)) +
    ((1 + 16 * h) ^ (3 / 2 : ℝ) * 740648 / h ^ 2) * (tau (120 / h) / (120 / h)))

lemma rOK_log {e e' : Ent} (h : rOK e e' = true) :
    0 < e'.N ∧ Real.log ((e'.N : ℝ) / D0) ≤ (if 0 ≤ e.r then (e.r : ℝ) / 4 * l2u else (e.r : ℝ) / 4 * l2l) := by
  simp only [CramerCompute.rOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hN, hr⟩ := h
  refine ⟨hN, ?_⟩
  have hD0 : (0 : ℝ) < D0 := by simp [CramerCompute.D0]
  have hN' : (0 : ℝ) < e'.N := by exact_mod_cast hN
  have hx : 0 < (e'.N : ℝ) / D0 := by positivity
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  -- `4 log θ ≤ r log 2`
  have key : 4 * Real.log ((e'.N : ℝ) / D0) ≤ (e.r : ℝ) * Real.log 2 := by
    by_cases h0 : 0 ≤ e.r
    · simp only [h0, if_true, decide_eq_true_eq] at hr
      have hr' : ((e'.N : ℝ) / D0) ^ 4 ≤ 2 ^ e.r.toNat := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        have : ((e'.N ^ 4 : ℕ) : ℝ) ≤ ((D0 ^ 4 * 2 ^ e.r.toNat : ℕ) : ℝ) := by exact_mod_cast hr
        push_cast at this; linarith
      have := Real.log_le_log (by positivity) hr'
      rw [Real.log_pow, Real.log_pow] at this
      have hc : ((e.r.toNat : ℕ) : ℝ) = (e.r : ℝ) := by
        rw [show (e.r : ℝ) = ((e.r.toNat : ℤ) : ℝ) by rw [Int.toNat_of_nonneg h0]]; push_cast; rfl
      rw [hc] at this; push_cast at this; linarith
    · simp only [h0, if_false, decide_eq_true_eq] at hr
      have hr' : ((e'.N : ℝ) / D0) ^ 4 * 2 ^ (-e.r).toNat ≤ 1 := by
        rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
        have : ((e'.N ^ 4 * 2 ^ (-e.r).toNat : ℕ) : ℝ) ≤ ((D0 ^ 4 : ℕ) : ℝ) := by exact_mod_cast hr
        push_cast at this; linarith
      have hpos : 0 < ((e'.N : ℝ) / D0) ^ 4 * 2 ^ (-e.r).toNat := by positivity
      have := Real.log_le_log hpos hr'
      rw [Real.log_one, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
      have hc : (((-e.r).toNat : ℕ) : ℝ) = -(e.r : ℝ) := by
        rw [show -(e.r : ℝ) = ((((-e.r).toNat : ℤ)) : ℝ) by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring]
        push_cast; rfl
      rw [hc] at this; push_cast at this; linarith
  split_ifs with h0
  · have : (e.r : ℝ) * Real.log 2 ≤ (e.r : ℝ) * l2u := by
      have : (0 : ℝ) ≤ e.r := by exact_mod_cast h0
      unfold l2u; nlinarith
    linarith
  · have : (e.r : ℝ) * Real.log 2 ≤ (e.r : ℝ) * l2l := by
      have : (e.r : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
      unfold l2l; nlinarith
    linarith

/-- One term of the main zero sum. -/
lemma main_term_le {e e' : Ent} {h : ℝ} (hh : 0 < h) (hNN : e.N ≤ e'.N) (hr : rOK e e' = true) :
    ((e.Gn : ℝ) / 1099511627776 + h * ((e.en : ℝ) / D0)) *
      (N0 ((e'.N : ℝ) / D0 / h) - N0 ((e.N : ℝ) / D0 / h)) ≤
    (1 / (2 * π * h)) *
      (Real.log (1 / (2 * π * h)) * ((CramerCompute.fA1G e e' : ℝ) / (1099511627776 * 1048576) +
          h * ((CramerCompute.fA1e e e' : ℝ) / (1048576 * 1048576))) +
        l2u / 4 * ((CramerCompute.fA2Gp e e' : ℝ) / (1099511627776 * 1048576) +
          h * ((CramerCompute.fA2ep e e' : ℝ) / (1048576 * 1048576))) -
        l2l / 4 * ((CramerCompute.fA2Gn e e' : ℝ) / (1099511627776 * 1048576) +
          h * ((CramerCompute.fA2en e e' : ℝ) / (1048576 * 1048576)))) := by
  obtain ⟨hN', hlog⟩ := rOK_log hr
  have hD0 : (0 : ℝ) < D0 := by simp [CramerCompute.D0]
  have hD0v : (D0 : ℝ) = 1048576 := by simp [CramerCompute.D0]
  have hpi := Real.pi_pos
  set G := (e.Gn : ℝ) / 1099511627776
  set E := (e.en : ℝ) / D0
  have hB : 0 ≤ G + h * E := by positivity
  have hNr : (e.N : ℝ) ≤ e'.N := by exact_mod_cast hNN
  have hN'r : (0 : ℝ) < e'.N := by exact_mod_cast hN'
  set T := (e.N : ℝ) / D0 / h
  set T' := (e'.N : ℝ) / D0 / h
  have hT0 : 0 ≤ T := by positivity
  have hTT : T ≤ T' := by
    simp only [T, T']
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hNr hD0.le) hh.le
  have hT'0 : 0 < T' := by positivity
  have hN0 := N0_sub_le hT0 hTT hT'0
  have hsplit : Real.log (T' / (2 * π)) = Real.log ((e'.N : ℝ) / D0) + Real.log (1 / (2 * π * h)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; simp only [T']; field_simp
  set ℓb := (if 0 ≤ e.r then (e.r : ℝ) / 4 * l2u else (e.r : ℝ) / 4 * l2l)
  have hΔ : T' - T = ((e'.N : ℝ) - e.N) / D0 / h := by simp only [T, T']; field_simp
  have hΔ0 : 0 ≤ ((e'.N : ℝ) - e.N) / D0 / h := by
    have : 0 ≤ (e'.N : ℝ) - e.N := by linarith
    positivity
  have step : (G + h * E) * (N0 T' - N0 T) ≤
      (G + h * E) * (((e'.N : ℝ) - e.N) / D0 / h) * (Real.log (1 / (2 * π * h)) + ℓb) / (2 * π) := by
    calc (G + h * E) * (N0 T' - N0 T)
        ≤ (G + h * E) * ((T' - T) * Real.log (T' / (2 * π)) / (2 * π)) :=
          mul_le_mul_of_nonneg_left hN0 hB
      _ ≤ (G + h * E) * ((T' - T) * (Real.log (1 / (2 * π * h)) + ℓb) / (2 * π)) := by
          have h1 : Real.log (T' / (2 * π)) ≤ Real.log (1 / (2 * π * h)) + ℓb := by
            rw [hsplit]; linarith
          have h2 : 0 ≤ T' - T := by linarith
          gcongr
      _ = _ := by rw [hΔ]; ring
  refine step.trans (le_of_eq ?_)
  -- the casts of the summands
  have hsub : ((e'.N - e.N : ℕ) : ℝ) = (e'.N : ℝ) - e.N := by rw [Nat.cast_sub hNN]
  simp only [CramerCompute.fA1G, CramerCompute.fA1e, CramerCompute.fA2Gp, CramerCompute.fA2Gn,
    CramerCompute.fA2ep, CramerCompute.fA2en, G, E, ℓb, hD0v]
  split_ifs with hr0
  · have hc : ((e.r.toNat : ℕ) : ℝ) = (e.r : ℝ) := by
      rw [show (e.r : ℝ) = ((e.r.toNat : ℤ) : ℝ) by rw [Int.toNat_of_nonneg hr0]]; push_cast; rfl
    push_cast
    rw [hsub, hc]
    field_simp
    ring
  · have hc : (((-e.r).toNat : ℕ) : ℝ) = -(e.r : ℝ) := by
      rw [show -(e.r : ℝ) = ((((-e.r).toNat : ℤ)) : ℝ) by rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring]
      push_cast; rfl
    push_cast
    rw [hsub, hc]
    field_simp
    ring

lemma cells_chain_pos : List.IsChain (fun a b => CramerCompute.posOK a b = true) cells := by
  have hpos : ∀ L' : List Ent, chk qs 1099511627776 L' = true →
      List.IsChain (fun a b => CramerCompute.posOK a b = true) L' := by
    intro L'
    induction L' with
    | nil => intro _; exact List.IsChain.nil
    | cons a rest ih =>
      intro h
      cases rest with
      | nil => exact List.IsChain.singleton a
      | cons b rest' =>
        simp only [CramerCompute.chk, Bool.and_eq_true] at h
        exact List.IsChain.cons_cons h.1.1.2 (ih h.2)
  exact hpos cells cells_chk

lemma cells_pair (i : ℕ) (hi : i + 1 < cells.length) :
    (cells.getD i default).N ≤ (cells.getD (i + 1) default).N ∧
      rOK (cells.getD i default) (cells.getD (i + 1) default) = true := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  refine ⟨?_, (chainB_sound _ cells cells_rOK).getElem i hi⟩
  have := cells_chain_pos.getElem i hi
  simp only [CramerCompute.posOK, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

set_option maxRecDepth 100000 in
/-- **The zero sum of the CMS weight.** Under RH, for `h = s/m ≤ 1/64`, the sum over the
zeros of `‖Σ_j a_j g_ρ(t_j)‖` is at most `s² m^{−1/2} Zc(h)`. -/
theorem zeroBound (hRH : RiemannHypothesis) {m s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hsmall : s / m ≤ 1 / 64) :
    Summable (fun ρ : Zeros => mult ρ *
        ‖∑ j ∈ range (2 * 16 + 1), (aco cdat j : ℂ) * gρ (ρ : ℂ) (tk m s 16 j)‖) ∧
    ∑' ρ : Zeros, mult ρ * ‖∑ j ∈ range (2 * 16 + 1), (aco cdat j : ℂ) * gρ (ρ : ℂ) (tk m s 16 j)‖ ≤
      s ^ 2 * m ^ (-(1 / 2) : ℝ) * Zc (s / m) := by
  set h := s / m with hh
  have hh0 : 0 < h := div_pos hs hm
  have hD0v : (D0 : ℝ) = 1048576 := by simp [CramerCompute.D0]
  have heok : chainB (eOK (C1a cdat (2 * 16) 16) (C1b cdat (2 * 16) 16) (C2a cdat (2 * 16) 16)
      (C2b cdat (2 * 16) 16)) cells = true := by
    rw [C1a_val, C1b_val, C2a_val, C2b_val]; exact cells_eOK
  have hfirst : (cells[0]'(by have := cells_len; omega)).N = 0 := by
    rw [← List.getD_eq_getElem _ default, cells_head]
  have h2 : 2 * (s / m) ≤ ((cells[1]'(by have := cells_len; omega)).N : ℝ) / D0 := by
    rw [← List.getD_eq_getElem _ default, cells_second, hD0v]; norm_num; rw [← hh]; linarith
  have h44 : 4.4 * (s / m) ≤
      ((cells[cells.length - 1]'(by have := cells_len; omega)).N : ℝ) / D0 := by
    rw [← List.getD_eq_getElem _ default, cells_last, hD0v]; norm_num; rw [← hh]; linarith
  obtain ⟨hsum, hle⟩ := zeroSum_le hRH Schoenfeld.rosserZeroCount cdat cdat_zero cdat_high cdat_sym
    (le_refl 16) (by unfold CramerCompute.CMSData.qs; exact List.cons_ne_nil _ _) cdat_coef
    (by norm_num) cells cells_len cells_chk heok hfirst hm hs
    (by norm_num; rw [← hh]; linarith) h2 h44
  rw [← hh] at hle
  refine ⟨hsum, hle.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set n := cells.length - 1 with hn
  have hn1 : 1 ≤ n := by have := cells_len; omega
  -- the three pieces
  set Bf : ℕ → ℝ := fun i => ((cells.getD i default).Gn / 1099511627776 : ℝ) +
    h * ((cells.getD i default).en / D0)
  have hBnn : ∀ i, 0 ≤ Bf i := fun i => by simp only [Bf]; positivity
  -- (i) the main sum
  have hmain : ∑ i ∈ range n, Bf i * (N0 (((cells.getD (i + 1) default).N : ℝ) / D0 / h) -
      N0 (((cells.getD i default).N : ℝ) / D0 / h)) ≤
      (1 / (2 * π * h)) *
      (Real.log (1 / (2 * π * h)) * (4252035564110250469740648 / (1099511627776 * 1048576) +
          h * (760852761666848834989 / (1048576 * 1048576))) +
        l2u / 4 * (463585232095674405339284 / (1099511627776 * 1048576) +
          h * (5587348473184294079485 / (1048576 * 1048576))) -
        l2l / 4 * (44601726036410213767724532 / (1099511627776 * 1048576) +
          h * (1037532018656752372080 / (1048576 * 1048576)))) := by
    refine (sum_le_sum fun i hi => main_term_le hh0 (cells_pair i (by have := mem_range.1 hi; omega)).1
      (cells_pair i (by have := mem_range.1 hi; omega)).2).trans (le_of_eq ?_)
    have e1 := pairSum_eq CramerCompute.fA1G cells
    have e2 := pairSum_eq CramerCompute.fA1e cells
    have e3 := pairSum_eq CramerCompute.fA2Gp cells
    have e4 := pairSum_eq CramerCompute.fA2Gn cells
    have e5 := pairSum_eq CramerCompute.fA2ep cells
    have e6 := pairSum_eq CramerCompute.fA2en cells
    rw [cells_a1G] at e1; rw [cells_a1e] at e2; rw [cells_a2Gp] at e3; rw [cells_a2Gn] at e4
    rw [cells_a2ep] at e5; rw [cells_a2en] at e6
    rw [← mul_sum]
    refine congrArg (fun t => (1 / (2 * π * h)) * t) ?_
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_div]
    rw [← hn] at e1 e2 e3 e4 e5 e6
    rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6]
    push_cast; ring
  -- (ii) the variation
  have hTV : |Bf 0| + |Bf (n - 1)| + ∑ i ∈ range (n - 1), |Bf (i + 1) - Bf i| ≤
      (13182834354755211737 + 20625534903171 + 15568535259931704074) / 1099511627776 +
        h * ((72271341813760 + 639958350772 + 1207134689330252) / 1048576) := by
    have hlast : Bf n = 20625534903171 / 1099511627776 + h * (639958350772 / 1048576) := by
      simp only [Bf, hn]; rw [cells_last, hD0v]; norm_num
    have hfst : Bf 0 = 13182834354755211737 / 1099511627776 + h * (72271341813760 / 1048576) := by
      simp only [Bf]; rw [cells_head, hD0v]; norm_num
    have hstep : ∀ i, |Bf (i + 1) - Bf i| ≤
        (CramerCompute.fTVG (cells.getD i default) (cells.getD (i + 1) default) : ℝ) / 1099511627776 +
        h * ((CramerCompute.fTVe (cells.getD i default) (cells.getD (i + 1) default) : ℝ) / 1048576) := by
      intro i
      have e : Bf (i + 1) - Bf i = (((cells.getD (i + 1) default).Gn : ℝ) - (cells.getD i default).Gn) /
          1099511627776 + h * ((((cells.getD (i + 1) default).en : ℝ) - (cells.getD i default).en) / 1048576) := by
        simp only [Bf, hD0v]; push_cast; ring
      have c1 : ((CramerCompute.fTVG (cells.getD i default) (cells.getD (i + 1) default) : ℕ) : ℝ) =
          |((cells.getD (i + 1) default).Gn : ℝ) - (cells.getD i default).Gn| := by
        simp only [CramerCompute.fTVG]; rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
      have c2 : ((CramerCompute.fTVe (cells.getD i default) (cells.getD (i + 1) default) : ℕ) : ℝ) =
          |((cells.getD (i + 1) default).en : ℝ) - (cells.getD i default).en| := by
        simp only [CramerCompute.fTVe]; rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
      rw [e, c1, c2]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_div, abs_mul, abs_of_pos hh0, abs_div]
      norm_num
    have hsumTV : ∑ i ∈ range n, |Bf (i + 1) - Bf i| ≤
        15568535259931704074 / 1099511627776 + h * (1207134689330252 / 1048576) := by
      refine (sum_le_sum fun i _ => hstep i).trans (le_of_eq ?_)
      have e1 := pairSum_eq CramerCompute.fTVG cells
      have e2 := pairSum_eq CramerCompute.fTVe cells
      rw [cells_tvG] at e1; rw [cells_tve] at e2
      rw [← hn] at e1 e2
      rw [sum_add_distrib, ← sum_div, ← mul_sum, ← sum_div, ← e1, ← e2]
      push_cast; ring
    have hsplit : ∑ i ∈ range n, |Bf (i + 1) - Bf i| =
        ∑ i ∈ range (n - 1), |Bf (i + 1) - Bf i| + |Bf n - Bf (n - 1)| := by
      rw [show n = (n - 1) + 1 by omega, sum_range_succ, show n - 1 + 1 = n by omega]
    have hb1 : |Bf (n - 1)| ≤ |Bf n| + |Bf n - Bf (n - 1)| := by
      have := abs_sub_abs_le_abs_sub (Bf n) (Bf (n - 1))
      rw [abs_sub_comm (Bf n)] at this ⊢
      linarith [abs_sub_abs_le_abs_sub (Bf (n - 1)) (Bf n)]
    have hb0 : |Bf 0| = 13182834354755211737 / 1099511627776 + h * (72271341813760 / 1048576) := by
      rw [abs_of_nonneg (hBnn 0), hfst]
    have hbn : |Bf n| = 20625534903171 / 1099511627776 + h * (639958350772 / 1048576) := by
      rw [abs_of_nonneg (hBnn n), hlast]
    rw [hsplit] at hsumTV
    rw [hb0]
    linarith only [hb1, hsumTV, hbn]
  -- assemble
  have hTn : ((cells.getD n default).N : ℝ) / D0 / h = 120 / h := by
    rw [hn, cells_last, hD0v]; norm_num
  have hEro : 0 ≤ Ero (120 / h) := by
    have : 4.4 ≤ 120 / h := by rw [le_div_iff₀ hh0]; linarith
    linarith [Ero_ge this]
  rw [hTn, Asum_val]
  have h3 := mul_le_mul_of_nonneg_left hTV hEro
  simp only [Zc]
  push_cast at h3 ⊢
  linarith only [h3, hmain]

end Cramer.CMS
