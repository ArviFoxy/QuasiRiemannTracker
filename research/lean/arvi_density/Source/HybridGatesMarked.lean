/- The scalar gates of a marked density-split transition `G(B₀,L₀,c₀) → G(B,L,c)`.

`HybridGatesM qf B0 L0 c0 B L c A D` has the fields of `HybridGates qf …` (Sil's gates of the
variable-density crossing step, in this package's version with the floor `qf`) except the two
unmarked HIGH fields `high_at_q`, `high_density_derivative`, which are replaced by one field:

* `high_marked`: a uniform reserve `r > 0` of
  `highJ(B,L,w,u,ν) + gainC ν B₀ L₀ c₀ (w - u) (1 - 6u)` for every excess `v ∈ [0, c - s₀]` and
  every density `ν ∈ [q(v), 3/4]`, where `w = s₀ + v`, `u = u(v)` and `gainC` is PR 76's repeated-mark
  gain (eight copies). This is the HIGH payment of the marked leaf at the worst retained width
  `s = w - u` (the marked excess `ν s - gainC ν … s H` is nondecreasing in `s`); it replaces the
  unmarked reserve at `ν = q(v)` together with the density-derivative gate, because the facets of the
  gain are not monotone in `ν`.

`HybridGatesM.ofHybridGates`: every `HybridGates` gives a `HybridGatesM` (`gainC ≥ 0`).

The rest of this file is the machinery used by the generated certificates of `high_marked`
(`research/density/gen_hybrid.py --marked`):

* `le_gainC_of_facets`: `gainC` is the infimum, over the amplitude classes `p ∈ [0,1/2]` and the six
  branches `(i, j)`, of `facetVal`, so a lower bound valid for every `(p, k)` is a lower bound of `gainC`;
* `gHighM` and the cleared forms `gHighM_ij`: `(highJ + facetVal_ij) · cDenM = cNumM`, polynomial in
  `(v, ν, p)`; the `U, αU, βU, eU` of each branch are the denominators-cleared coefficients of
  `branchRoot_eq`;
* `nuT`, `nuT_mem`, `exists_nuT`, `nuT_eq`, `cNumY`, `cDenY`, `gHighM_scaled`: the density
  `ν = q(v) + t (3/4 - q(v)) = Y/E` as a box variable `t ∈ [0,1]` (`E = densE`, `Y = densK (1-t) +
  3/4 t E`), and the cleared forms multiplied by `E²`, polynomial in `(v, t, p)`;
* `box_lower3`: a box of `(v, t, p)` on which the cleared numerator is `≥ m > 0` and the cleared
  denominator lies in `(0, M]` gives `g ≥ m / M` (Bernstein coefficients via the nested `bernN` of
  `Source.HybridGates`). -/
import Submissions.arvi_density.Source.HybridGates
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC

set_option autoImplicit false
namespace QRH.ArviDensity
noncomputable section

open Hybrid

/-- The gates of a marked density transition: `HybridGates qf` with the unmarked HIGH fields
`high_at_q`, `high_density_derivative` replaced by `high_marked`. -/
structure HybridGatesM (qf B0 L0 c0 B L c A D : ℝ) : Prop where
  width_pos : 0 < c - cross B0 L0 B L
  sel_den_pos : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → 0 < 1 + D * v
  dens_den_pos : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → 0 < densE B0 L0 L A D v
  q_lower : UnifPos (gQLower B0 L0 L A D) 0 (c - cross B0 L0 B L)
  q_upper : UnifPos (gQUpper B0 L0 L A D) 0 (c - cross B0 L0 B L)
  q_floor : UnifPos (gQFloor qf B0 L0 L A D) 0 (c - cross B0 L0 B L)
  H_lower : UnifPos (gHLower A D) 0 (c - cross B0 L0 B L)
  retained_cap : UnifPos (gRetainedCap B0 L0 c0 B L A D) 0 (c - cross B0 L0 B L)
  retained_width : UnifPos (gRetainedWidth B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  /-- The LOW identity (C): `L0 u - q((L0-L)v+(6B0-L0)u) = (1/1000) L0 u`. -/
  low_identity : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L →
    lowDefect B0 L0 L A D v = 1 / 1000 * L0 * sel A D v
  low_div_eq : ∀ v, 0 < v → v ≤ c - cross B0 L0 B L →
    lowDefect B0 L0 L A D v / v = gLowPerWidth L0 A D v
  low_per_excess_width : UnifPos (gLowPerWidth L0 A D) 0 (c - cross B0 L0 B L)
  /-- The marked HIGH gate: a uniform reserve of `highJ + gainC` on the whole density range
  `ν ∈ [q(v), 3/4]`, at the retained width `w - u` and the packed radius `1 - 6u`. -/
  high_marked : ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → ∀ ν,
    dens B0 L0 L A D v ≤ ν → ν ≤ 3 / 4 →
      r ≤ highJ B L (width B0 L0 B L v) (sel A D v) ν +
        QRH.RepeatedMarks.Source.gainC ν B0 L0 c0 (width B0 L0 B L v - sel A D v) (packed A D v)
  principal_reference : UnifPos (gPrincipal B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  second_reference : UnifPos (gSecondRef B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  second_diagonal : UnifPos (gSecondDiag B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  reference_upper_positive : UnifPos (gRefUpper B0 L0 B L A D) 0 (c - cross B0 L0 B L)
  sel_hasDerivAt : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L →
    HasDerivAt (sel A D) (gSelDeriv A D v) v
  selection_monotonicity : UnifPos (gSelDeriv A D) 0 (c - cross B0 L0 B L)

namespace HybridGatesM
variable {qf B0 L0 c0 B L c A D : ℝ}

theorem dens_mem (h : HybridGatesM qf B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) :
    1 / 2 < dens B0 L0 L A D v ∧ dens B0 L0 L A D v < 3 / 4 := by
  have a := h.q_lower.pos v h0 h1
  have b := h.q_upper.pos v h0 h1
  unfold gQLower at a; unfold gQUpper at b
  constructor <;> linarith

theorem dens_floor (h : HybridGatesM qf B0 L0 c0 B L c A D) (v : ℝ) (h0 : 0 ≤ v)
    (h1 : v ≤ c - cross B0 L0 B L) : qf < dens B0 L0 L A D v := by
  have a := h.q_floor.pos v h0 h1
  unfold gQFloor at a
  linarith

end HybridGatesM

/-- Every `HybridGates` is a `HybridGatesM`: the gain is nonnegative, and the unmarked HIGH reserve
holds on all of `[q(v), 3/4]` (`HybridGates.high_reserve`). In particular PR 83's and PR 86's
certificates are marked certificates. -/
theorem HybridGatesM.ofHybridGates {qf B0 L0 c0 B L c A D : ℝ}
    (h : HybridGates qf B0 L0 c0 B L c A D) : HybridGatesM qf B0 L0 c0 B L c A D where
  width_pos := h.width_pos
  sel_den_pos := h.sel_den_pos
  dens_den_pos := h.dens_den_pos
  q_lower := h.q_lower
  q_upper := h.q_upper
  q_floor := h.q_floor
  H_lower := h.H_lower
  retained_cap := h.retained_cap
  retained_width := h.retained_width
  low_identity := h.low_identity
  low_div_eq := h.low_div_eq
  low_per_excess_width := h.low_per_excess_width
  high_marked := by
    obtain ⟨r, hr, hJ⟩ := h.high_reserve
    refine ⟨r, hr, fun v h0 h1 ν hν1 hν2 => ?_⟩
    have h2 := hJ v h0 h1 ν hν1 hν2
    have h3 := QRH.RepeatedMarks.Source.gainC_nonneg ν B0 L0 c0
      (width B0 L0 B L v - sel A D v) (packed A D v)
    linarith
  principal_reference := h.principal_reference
  second_reference := h.second_reference
  second_diagonal := h.second_diagonal
  reference_upper_positive := h.reference_upper_positive
  sel_hasDerivAt := h.sel_hasDerivAt
  selection_monotonicity := h.selection_monotonicity

/-! ### `gainC` is bounded below by its facets -/

open QRH.RepeatedMarks in
/-- A lower bound of `facetVal` valid for every amplitude class `p ∈ [0,1/2]` and every branch is a
lower bound of the repeated-mark gain `gainC` (an infimum over classes of the minimum over branches). -/
theorem le_gainC_of_facets {ν B lam h S Q r : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 3 / 4)
    (hB0 : 22 / 23 ≤ B) (hB1 : B ≤ 1) (hlam : 1 < lam) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hr : ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → ∀ k : Branch, r ≤ facetVal ν p 8 B lam h S Q k) :
    r ≤ Source.gainC ν B lam h S Q := by
  have P : ParentParams ν 8 B lam h := ⟨hν0, hν1, by norm_num, hB0, hB1, hlam, hh0, hh1⟩
  rw [Source.gainC_eq P hS hQ]
  show r ≤ sInf ((fun p => gainP ν p 8 B lam h S Q) '' classes)
  apply le_csInf
  · exact ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    show r ≤ gainP ν p 8 B lam h S Q
    rw [gainP_eq_inf ν p 8 B lam h S Q P.hν0.le]
    exact Finset.le_inf' _ _ (fun k _ => hr p hp.1 hp.2 k)

open QRH.RepeatedMarks in
/-- Case split over the six branches. -/
theorem forall_branch {P : Branch → Prop} (h00 : P (0, 0)) (h01 : P (0, 1)) (h02 : P (0, 2))
    (h10 : P (1, 0)) (h11 : P (1, 1)) (h12 : P (1, 2)) : ∀ k, P k := by
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> assumption

/-! ### Cleared forms of the marked HIGH functional -/

open QRH.RepeatedMarks

/-- The marked HIGH functional at branch `k`: `highJ + facetVal` at the retained width `w - u` and
packed radius `1 - 6u` (`w = width v`, `u = sel v`), amplitude class `p`, density `ν`, eight copies. -/
def gHighM (B0 L0 c0 B L A D v ν p : ℝ) (k : Branch) : ℝ :=
  highJ B L (width B0 L0 B L v) (sel A D v) ν +
    facetVal ν p 8 B0 L0 c0 (width B0 L0 B L v - sel A D v) (packed A D v) k

/-- Cleared numerator: `ν·(5QX·U + w(αU·SX + βU·QX)) + ν((1-2p)SX - ΠX)·d̂ + σX·d̂` with
`d̂ = (15-6ν)/2·U + (5-6ν)·eU`, `X = 1 + D v`, `SX = w X - A v`, `QX = X - 6 A v`,
`ΠX = (B - (L-1)w) X - A v`, `σX = A v`. -/
def cNumM (A D v ν p W B L U αU βU eU : ℝ) : ℝ :=
  ν * (5 * ((1 + D * v) - 6 * (A * v)) * U + (5 - 6 * ν) *
      (αU * (W * (1 + D * v) - A * v) + βU * ((1 + D * v) - 6 * (A * v)))) +
    ν * ((1 - 2 * p) * (W * (1 + D * v) - A * v) - ((B - (L - 1) * W) * (1 + D * v) - A * v)) *
      ((15 - 6 * ν) / 2 * U + (5 - 6 * ν) * eU) +
    (A * v) * ((15 - 6 * ν) / 2 * U + (5 - 6 * ν) * eU)

/-- Cleared denominator `X · d̂`. -/
def cDenM (D v ν U eU : ℝ) : ℝ := (1 + D * v) * ((15 - 6 * ν) / 2 * U + (5 - 6 * ν) * eU)

/-- The generic cleared form: for any `U, αU, βU, eU` with `αU = U·offS`, `βU = U·offQ`,
`eU = U·slopeExcess` of the branch `k`, `(highJ + facetVal_k) · cDenM = cNumM`. -/
theorem gHighM_generic (B0 L0 c0 B L A D v ν p : ℝ) (k : Branch) (U αU βU eU : ℝ)
    (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0)
    (hα : offS p 8 L0 k * U = αU) (hβ : offQ p B0 L0 c0 k * U = βU)
    (he : slopeExcess p L0 k * U = eU) :
    gHighM B0 L0 c0 B L A D v ν p k * cDenM D v ν U eU =
      cNumM A D v ν p (width B0 L0 B L v) B L U αU βU eU := by
  have hex := slopeExcess_nonneg P.hp0 P.hp1 P.hlam k
  have hν1 := P.hν1
  have hw : 0 ≤ 5 - 6 * ν := by linarith
  have hr := branchRoot_eq P (width B0 L0 B L v - sel A D v) (packed A D v) k
  unfold QRH.RepeatedMarks.w at hr
  obtain ⟨m, hmdef⟩ : ∃ m, m = (15 - 6 * ν) / 2 + (5 - 6 * ν) * slopeExcess p L0 k := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by
    have : 0 ≤ (5 - 6 * ν) * slopeExcess p L0 k := mul_nonneg hw hex
    intro h; rw [hmdef] at h; linarith
  rw [← hmdef] at hr
  have key : (15 - 6 * ν) / 2 * U + (5 - 6 * ν) * eU = m * U := by
    rw [← he, hmdef]; ring
  unfold gHighM cDenM cNumM
  rw [key]
  have hxi : baseXi ν = 10 / (15 - 6 * ν) := rfl
  have h15 : (15 - 6 * ν) ≠ 0 := by intro h; linarith
  subst hα hβ
  unfold facetVal
  rw [hr, hxi]
  unfold highJ rhoOf packed sel
  generalize 1 + D * v = X at *
  field_simp
  ring

section Branches
variable (p B0 L0 c0 : ℝ)

theorem offQ_02 (hL : L0 - 2 * p ≠ 0) (hL0 : L0 ≠ 0) :
    offQ p B0 L0 c0 ((0 : Fin 2), (2 : Fin 3)) = p * B0 / (L0 - 2 * p) := by
  have e : (1 : ℝ) - 2 * p / L0 = (L0 - 2 * p) / L0 := by field_simp
  simp only [offQ, e]
  simp
  field_simp

theorem slope_02 (hL : L0 - 2 * p ≠ 0) (hL0 : L0 ≠ 0) :
    slopeExcess p L0 ((0 : Fin 2), (2 : Fin 3)) = p / (L0 - 2 * p) := by
  have e : (1 : ℝ) - 2 * p / L0 = (L0 - 2 * p) / L0 := by field_simp
  simp only [slopeExcess, e]
  simp
  field_simp

theorem offQ_12 (hL : L0 - 2 * p ≠ 0) (hL0 : L0 ≠ 0) :
    offQ p B0 L0 c0 ((1 : Fin 2), (2 : Fin 3)) = p / (1 - p) + p * B0 / (L0 - 2 * p) := by
  have e : (1 : ℝ) - 2 * p / L0 = (L0 - 2 * p) / L0 := by field_simp
  simp only [offQ, e]
  simp
  field_simp

theorem slope_12 (hL : L0 - 2 * p ≠ 0) (hL0 : L0 ≠ 0) :
    slopeExcess p L0 ((1 : Fin 2), (2 : Fin 3)) = p / (1 - p) + p / (L0 - 2 * p) := by
  have e : (1 : ℝ) - 2 * p / L0 = (L0 - 2 * p) / L0 := by field_simp
  simp only [slopeExcess, e]
  simp
  field_simp

end Branches

/-- The six cleared forms, one per branch `(i,j)`, for `Params ν p 8 B0 L0 c0`. -/
theorem gHighM_00 (B0 L0 c0 B L A D v ν p : ℝ) (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0) :
    gHighM B0 L0 c0 B L A D v ν p (0, 0) * cDenM D v ν 1 0 =
      cNumM A D v ν p (width B0 L0 B L v) B L 1 (2 * p * 8 + p) 0 0 :=
  gHighM_generic B0 L0 c0 B L A D v ν p (0, 0) 1 _ _ _ P hx
    (by simp [offS]; try ring) (by simp [offQ]) (by simp [slopeExcess])

theorem gHighM_01 (B0 L0 c0 B L A D v ν p : ℝ) (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0) :
    gHighM B0 L0 c0 B L A D v ν p (0, 1) * cDenM D v ν 1 0 =
      cNumM A D v ν p (width B0 L0 B L v) B L 1 (2 * p * 8) (p * c0) 0 :=
  gHighM_generic B0 L0 c0 B L A D v ν p (0, 1) 1 _ _ _ P hx
    (by simp [offS]) (by simp [offQ]; try ring) (by simp [slopeExcess])

theorem gHighM_02 (B0 L0 c0 B L A D v ν p : ℝ) (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0) :
    gHighM B0 L0 c0 B L A D v ν p (0, 2) * cDenM D v ν (L0 - 2 * p) p =
      cNumM A D v ν p (width B0 L0 B L v) B L (L0 - 2 * p) (2 * p * 8 * (L0 - 2 * p))
        (p * B0) p := by
  have hL : L0 - 2 * p ≠ 0 := by have := P.hp1; have := P.hlam; intro h; linarith
  have hL0 : L0 ≠ 0 := by have := P.hlam; intro h; linarith
  refine gHighM_generic B0 L0 c0 B L A D v ν p (0, 2) (L0 - 2 * p) _ _ _ P hx
    (by simp [offS]) ?_ ?_
  · rw [offQ_02 p B0 L0 c0 hL hL0]; exact div_mul_cancel₀ _ hL
  · rw [slope_02 p L0 hL hL0]; exact div_mul_cancel₀ _ hL

theorem gHighM_10 (B0 L0 c0 B L A D v ν p : ℝ) (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0) :
    gHighM B0 L0 c0 B L A D v ν p (1, 0) * cDenM D v ν (1 - p) p =
      cNumM A D v ν p (width B0 L0 B L v) B L (1 - p) (p * (1 - p)) p p := by
  have h1 : 1 - p ≠ 0 := by have := P.hp1; intro h; linarith
  refine gHighM_generic B0 L0 c0 B L A D v ν p (1, 0) (1 - p) _ _ _ P hx
    (by simp [offS]) ?_ ?_
  · simp [offQ]; field_simp
  · simp [slopeExcess]; field_simp

theorem gHighM_11 (B0 L0 c0 B L A D v ν p : ℝ) (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0) :
    gHighM B0 L0 c0 B L A D v ν p (1, 1) * cDenM D v ν (1 - p) p =
      cNumM A D v ν p (width B0 L0 B L v) B L (1 - p) 0 (p + c0 * p * (1 - p)) p := by
  have h1 : 1 - p ≠ 0 := by have := P.hp1; intro h; linarith
  refine gHighM_generic B0 L0 c0 B L A D v ν p (1, 1) (1 - p) _ _ _ P hx
    (by simp [offS]) ?_ ?_
  · simp [offQ]; field_simp
  · simp [slopeExcess]; field_simp

theorem gHighM_12 (B0 L0 c0 B L A D v ν p : ℝ) (P : Params ν p 8 B0 L0 c0) (hx : 1 + D * v ≠ 0) :
    gHighM B0 L0 c0 B L A D v ν p (1, 2) *
        cDenM D v ν ((1 - p) * (L0 - 2 * p)) (p * (L0 - 2 * p) + p * (1 - p)) =
      cNumM A D v ν p (width B0 L0 B L v) B L ((1 - p) * (L0 - 2 * p)) 0
        (p * (L0 - 2 * p) + B0 * p * (1 - p)) (p * (L0 - 2 * p) + p * (1 - p)) := by
  have h1 : 1 - p ≠ 0 := by have := P.hp1; intro h; linarith
  have hL : L0 - 2 * p ≠ 0 := by have := P.hp1; have := P.hlam; intro h; linarith
  have hL0 : L0 ≠ 0 := by have := P.hlam; intro h; linarith
  refine gHighM_generic B0 L0 c0 B L A D v ν p (1, 2) ((1 - p) * (L0 - 2 * p)) _ _ _ P hx
    (by simp [offS]) ?_ ?_
  · rw [offQ_12 p B0 L0 c0 hL hL0]
    generalize L0 - 2 * p = a at hL ⊢
    field_simp
  · rw [slope_12 p L0 hL hL0]
    generalize L0 - 2 * p = a at hL ⊢
    field_simp

/-! ### The density as a box variable and the scaled cleared forms -/

/-- The density `ν ∈ [q(v), 3/4]` as `ν = q(v) + t (3/4 - q(v))`, `t ∈ [0,1]`: a box of `(v, t, p)`. -/
def nuT (B0 L0 L A D v t : ℝ) : ℝ := dens B0 L0 L A D v + t * (3 / 4 - dens B0 L0 L A D v)

theorem nuT_mem {B0 L0 L A D v t : ℝ} (h1 : 1 / 2 < dens B0 L0 L A D v)
    (h2 : dens B0 L0 L A D v < 3 / 4) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / 2 < nuT B0 L0 L A D v t ∧ nuT B0 L0 L A D v t ≤ 3 / 4 := by
  unfold nuT
  have a : 0 ≤ t * (3 / 4 - dens B0 L0 L A D v) := mul_nonneg ht0 (by linarith)
  have b : 0 ≤ (1 - t) * (3 / 4 - dens B0 L0 L A D v) := mul_nonneg (by linarith) (by linarith)
  constructor <;> nlinarith

theorem exists_nuT {B0 L0 L A D v ν : ℝ} (h2 : dens B0 L0 L A D v < 3 / 4)
    (h3 : dens B0 L0 L A D v ≤ ν) (h4 : ν ≤ 3 / 4) :
    ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ ν = nuT B0 L0 L A D v t := by
  have hd : 0 < 3 / 4 - dens B0 L0 L A D v := by linarith
  refine ⟨(ν - dens B0 L0 L A D v) / (3 / 4 - dens B0 L0 L A D v), div_nonneg (by linarith) hd.le,
    ?_, ?_⟩
  · rw [div_le_one hd]; linarith
  · unfold nuT; rw [div_mul_cancel₀ _ hd.ne']; ring

theorem nuT_eq {B0 L0 L A D v t : ℝ} (hE : densE B0 L0 L A D v ≠ 0) :
    nuT B0 L0 L A D v t =
      (densK L0 A * (1 - t) + 3 / 4 * t * densE B0 L0 L A D v) / densE B0 L0 L A D v := by
  unfold nuT
  rw [dens_eq]
  field_simp
  ring

/-- Scaled cleared numerator: `E² · cNumM` at `ν = Y/E`. -/
def cNumY (A D v p W B L U αU βU eU Y E : ℝ) : ℝ :=
  Y * (5 * ((1 + D * v) - 6 * (A * v)) * U * E + (5 * E - 6 * Y) *
      (αU * (W * (1 + D * v) - A * v) + βU * ((1 + D * v) - 6 * (A * v)))) +
    Y * ((1 - 2 * p) * (W * (1 + D * v) - A * v) - ((B - (L - 1) * W) * (1 + D * v) - A * v)) *
      ((15 * E - 6 * Y) / 2 * U + (5 * E - 6 * Y) * eU) +
    E * (A * v) * ((15 * E - 6 * Y) / 2 * U + (5 * E - 6 * Y) * eU)

/-- Scaled cleared denominator: `E² · cDenM = E · cDenY` at `ν = Y/E`. -/
def cDenY (D v U eU Y E : ℝ) : ℝ := (1 + D * v) * ((15 * E - 6 * Y) / 2 * U + (5 * E - 6 * Y) * eU)

theorem cDenY_pos {D v U eU Y E : ℝ} (hX : 0 < 1 + D * v) (hE : 0 < E) (hY : Y ≤ 3 / 4 * E)
    (hU : 0 < U) (he : 0 ≤ eU) : 0 < cDenY D v U eU Y E := by
  unfold cDenY
  have h1 : 0 < (15 * E - 6 * Y) / 2 * U := mul_pos (by linarith) hU
  have h2 : 0 ≤ (5 * E - 6 * Y) * eU := mul_nonneg (by linarith) he
  exact mul_pos hX (by linarith)

/-- The cleared forms at `ν = Y/E` from those at `ν`. -/
theorem gHighM_scaled {B0 L0 c0 B L A D v p Y E : ℝ} {k : Branch} {U αU βU eU : ℝ} (hE : E ≠ 0)
    (h : gHighM B0 L0 c0 B L A D v (Y / E) p k * cDenM D v (Y / E) U eU =
      cNumM A D v (Y / E) p (width B0 L0 B L v) B L U αU βU eU) :
    gHighM B0 L0 c0 B L A D v (Y / E) p k * (E * cDenY D v U eU Y E) =
      cNumY A D v p (width B0 L0 B L v) B L U αU βU eU Y E := by
  have h1 : gHighM B0 L0 c0 B L A D v (Y / E) p k * (E * cDenY D v U eU Y E) =
      E ^ 2 * (gHighM B0 L0 c0 B L A D v (Y / E) p k * cDenM D v (Y / E) U eU) := by
    unfold cDenM cDenY
    field_simp
    try ring
  rw [h1, h]
  unfold cNumM cNumY
  field_simp
  try ring

/-- Positivity of the scaled cleared denominators of the six branches. -/
theorem cDenY_pos_all {D v Y E p L0 : ℝ} (hX : 0 < 1 + D * v) (hE : 0 < E) (hY : Y ≤ 3 / 4 * E)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (hL : 1 < L0) :
    0 < E * cDenY D v 1 0 Y E ∧ 0 < E * cDenY D v (L0 - 2 * p) p Y E ∧
      0 < E * cDenY D v (1 - p) p Y E ∧
      0 < E * cDenY D v ((1 - p) * (L0 - 2 * p)) (p * (L0 - 2 * p) + p * (1 - p)) Y E := by
  have hL2 : 0 < L0 - 2 * p := by linarith
  have hp' : 0 < 1 - p := by linarith
  refine ⟨mul_pos hE (cDenY_pos hX hE hY one_pos le_rfl),
    mul_pos hE (cDenY_pos hX hE hY hL2 hp0), mul_pos hE (cDenY_pos hX hE hY hp' hp0),
    mul_pos hE (cDenY_pos hX hE hY (mul_pos hp' hL2) ?_)⟩
  have := mul_nonneg hp0 hL2.le
  have := mul_nonneg hp0 hp'.le
  linarith

/-! ### Boxes in `(v, t, p)` -/

/-- One box of `(v, t, p)` (any three real variables): if on `[lo₁,hi₁] × [lo₂,hi₂] × [lo₃,hi₃]` we have `g·d = n`, and after the
affine changes `x = lo + (hi-lo) t` the numerator is `≥ m ≥ 0` and the denominator lies in `(0, M]`,
then `g ≥ m/M` on the box. -/
theorem box_lower3 {g n d : ℝ → ℝ → ℝ → ℝ} {lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ m M : ℝ}
    (h₁ : lo₁ < hi₁) (h₂ : lo₂ < hi₂) (h₃ : lo₃ < hi₃) (hm : 0 ≤ m)
    (hgd : ∀ a b c, lo₁ ≤ a → a ≤ hi₁ → lo₂ ≤ b → b ≤ hi₂ → lo₃ ≤ c → c ≤ hi₃ →
      g a b c * d a b c = n a b c)
    (hn : ∀ t₁ t₂ t₃, 0 ≤ t₁ → t₁ ≤ 1 → 0 ≤ t₂ → t₂ ≤ 1 → 0 ≤ t₃ → t₃ ≤ 1 →
      m ≤ n (lo₁ + (hi₁ - lo₁) * t₁) (lo₂ + (hi₂ - lo₂) * t₂) (lo₃ + (hi₃ - lo₃) * t₃))
    (hd : ∀ t₁ t₂ t₃, 0 ≤ t₁ → t₁ ≤ 1 → 0 ≤ t₂ → t₂ ≤ 1 → 0 ≤ t₃ → t₃ ≤ 1 →
      0 < d (lo₁ + (hi₁ - lo₁) * t₁) (lo₂ + (hi₂ - lo₂) * t₂) (lo₃ + (hi₃ - lo₃) * t₃))
    (hdM : ∀ t₁ t₂ t₃, 0 ≤ t₁ → t₁ ≤ 1 → 0 ≤ t₂ → t₂ ≤ 1 → 0 ≤ t₃ → t₃ ≤ 1 →
      d (lo₁ + (hi₁ - lo₁) * t₁) (lo₂ + (hi₂ - lo₂) * t₂) (lo₃ + (hi₃ - lo₃) * t₃) ≤ M) :
    ∀ a b c, lo₁ ≤ a → a ≤ hi₁ → lo₂ ≤ b → b ≤ hi₂ → lo₃ ≤ c → c ≤ hi₃ → m / M ≤ g a b c := by
  intro a b c ha1 ha2 hb1 hb2 hc1 hc2
  have w₁ : 0 < hi₁ - lo₁ := sub_pos.2 h₁
  have w₂ : 0 < hi₂ - lo₂ := sub_pos.2 h₂
  have w₃ : 0 < hi₃ - lo₃ := sub_pos.2 h₃
  set t₁ := (a - lo₁) / (hi₁ - lo₁) with ht₁
  set t₂ := (b - lo₂) / (hi₂ - lo₂) with ht₂
  set t₃ := (c - lo₃) / (hi₃ - lo₃) with ht₃
  have e₁ : lo₁ + (hi₁ - lo₁) * t₁ = a := by rw [ht₁]; field_simp; ring
  have e₂ : lo₂ + (hi₂ - lo₂) * t₂ = b := by rw [ht₂]; field_simp; ring
  have e₃ : lo₃ + (hi₃ - lo₃) * t₃ = c := by rw [ht₃]; field_simp; ring
  have t₁0 : 0 ≤ t₁ := div_nonneg (by linarith) w₁.le
  have t₂0 : 0 ≤ t₂ := div_nonneg (by linarith) w₂.le
  have t₃0 : 0 ≤ t₃ := div_nonneg (by linarith) w₃.le
  have t₁1 : t₁ ≤ 1 := by rw [ht₁, div_le_one w₁]; linarith
  have t₂1 : t₂ ≤ 1 := by rw [ht₂, div_le_one w₂]; linarith
  have t₃1 : t₃ ≤ 1 := by rw [ht₃, div_le_one w₃]; linarith
  have hn' := hn t₁ t₂ t₃ t₁0 t₁1 t₂0 t₂1 t₃0 t₃1
  have hd' := hd t₁ t₂ t₃ t₁0 t₁1 t₂0 t₂1 t₃0 t₃1
  have hdM' := hdM t₁ t₂ t₃ t₁0 t₁1 t₂0 t₂1 t₃0 t₃1
  rw [e₁, e₂, e₃] at hn' hd' hdM'
  have hg : g a b c = n a b c / d a b c := by
    rw [eq_div_iff hd'.ne', hgd a b c ha1 ha2 hb1 hb2 hc1 hc2]
  rw [hg]
  have hM : 0 < M := lt_of_lt_of_le hd' hdM'
  calc m / M ≤ m / d a b c := div_le_div_of_nonneg_left hm hd' hdM'
    _ ≤ n a b c / d a b c := div_le_div_of_nonneg_right hn' hd'.le

end
end QRH.ArviDensity
