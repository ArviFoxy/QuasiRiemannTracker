/- Copyright (c) 2026 Sil. Apache-2.0.
Seam B (WP-H): the grouped side bound of the cube-free second step, proved from Seam A.

`grouped_side_bound_of_leaf`: for every price with a Seam A leaf
`PricedPackedSource price Mmin (Mmax+1) (L+1)` (envelopes up to one unit above `Mmax`,
ordinary lengths up to `L+1`), the concrete second-step frame `gFrame L` satisfies the grouped
side bound with the amplitude `gAmp L` (`GroupedSideBoundA`).

Quantifier order (design §4): `ε`; then the mesh (from Seam A's mesh at `ε/8`, `1/2`, and the
price Lipschitz constant); then the structural data `θ` and the character `η`; then the
constants: Seam A's `(degree, S, C)` over the finite anchor family `anchors η`, the common
profile control, the spectral-mass and twisted-profile controls, and the label-reduction
constant; then `∀ᶠ Z` (Seam A, the dyadic class count `O(log² Z) ≤ Z^{ε/16}`, `log_Z 3`
small); then the source, the label group and `w₀` (Seam A is uniform in `w₀`).

Shape note. `Second.GroupedSideBound` (SeamBUse) has a FIXED amplitude `Src → ℝ`. The
ordinary profiles and heights of a second-step source are root data quantified after `Z`,
and the bound is polynomial in them with a degree and seminorm set chosen after `θ`; so the
amplitude must take the existential degree and seminorm set (FP:
`amplitude d.root d.t₀ d.V J control Cside`). `GroupedSideBoundA` is that shape. -/
import Submissions.density_split_third_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace QRH.DensitySplitThird.CubeFree.Packet.Grouped
open Candidate.FourthPower QRH.DensitySplitThird.CubeFree.FP QRH.DensitySplitThird.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional
open ProfileSeparation (commonPair pairWeight pairMajorant)
local notation "O" => HeckeFamily.O

/-- **Seam B from Seam A** for the concrete cube-free second-step frame. -/
theorem grouped_side_bound_of_leaf (L : ℝ) (hL : 0 ≤ L) (price : Price) (Mmin Mmax : ℝ)
    (hleaf : PricedPackedSource price Mmin (Mmax + 1) (L + 1)) :
    GroupedSideBoundA (gFrame L) (gAmp L) price Mmin Mmax := by
  intro ε hε
  obtain ⟨meshA, hmeshA, hA⟩ := hleaf (ε/8) (by positivity)
  have hlip := price.lip_nonneg
  refine ⟨min meshA (min (1/2) (ε / (8 * (3 + price.lip)))),
    lt_min hmeshA (lt_min (by norm_num) (by positivity)), ?_⟩
  intro mesh hmesh hmm θ η
  have hm1 : mesh ≤ meshA := hmm.trans (min_le_left _ _)
  have hm2 : mesh ≤ 1/2 := hmm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 : mesh ≤ ε / (8 * (3 + price.lip)) :=
    hmm.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmε : (3 + price.lip) * mesh ≤ ε/8 := by
    rw [le_div_iff₀ (by positivity)] at hm3
    linarith
  obtain ⟨degA, SA, CA, hCA, hevA⟩ := hA mesh hm1 (Fin θ.N) θ.rayM θ.Hray θ.hH θ.W θ.hW θ.hWs
    θ.bΦ θ.hbΦ DictIdx (anchors η) θ.η₀ θ.Q θ.hQ θ.hQ0 θ.hQt θ.hQ72
  obtain ⟨nP, CP, hCP, hctl⟩ := ProfileSeparation.commonPair_control SA
  obtain ⟨T₀, K₀, hK₀, hm₀⟩ := ProfileSeparation.pairMajorant_mass_control 0
  obtain ⟨TJ, KJ, hKJ, hmJ⟩ := ProfileSeparation.pairMajorant_mass_control (2*nP)
  obtain ⟨n₀, S₀, C₀, hC₀, -, htw₀⟩ :=
    ReferenceUniformApproximation.twisted_source_control θ.a θ.b θ.ha0 T₀
  obtain ⟨nJ, SJ, CJ, hCJ, -, htwJ⟩ :=
    ReferenceUniformApproximation.twisted_source_control θ.a θ.b θ.ha0 TJ
  obtain ⟨Cred, hCred, hred⟩ := label_reduction_frame θ (ε/8) (by positivity)
    (ε/(48 * max 1 θ.Bmask))
    (div_pos hε (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))))
  refine ⟨degA + 2*n₀ + 2*nJ, S₀ ∪ SJ, ctot CA CP Cred K₀ C₀ KJ CJ + 1, ?_, ?_⟩
  · have : 0 ≤ ctot CA CP Cred K₀ C₀ KJ CJ := by
      unfold ctot
      have := QuadraticInitialBound.diagonalControl_nonneg
        CenteredMomentFirstAmplificationChoice.ballProfile
      positivity
    linarith
  filter_upwards [hevA,
    eventually_dyadic_count ((Fintype.card DictIdx : ℝ) * 2^θ.N) L θ.b (ε/16) (by positivity),
    eventually_logb_le 3 (ε / (16 * (1 + 3*price.lip))) (by positivity),
    eventually_logb_le 3 (1/2) (by norm_num), eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2)).eventually_ge_atTop (2:ℝ)]
    with Z hZA hcount hl3 hl3' hZ1 hZ32
  have hl3e : (1 + 3*price.lip) * Real.logb Z 3 ≤ ε/16 := by
    rw [le_div_iff₀ (by positivity)] at hl3
    linarith
  intro r labels w₀ H hadm v
  have h := grouped_at price Mmin Mmax θ hL mesh hmesh hm2 η ε hε hmε degA SA CA hCA.le nP CP
    hctl T₀ K₀ hK₀.le hm₀ TJ KJ hKJ.le hmJ n₀ S₀ C₀ hC₀.le htw₀ nJ SJ CJ hCJ.le htwJ Cred
    hCred.le hred Z hZ1 hZA hcount hl3e hl3' hZ32 r labels w₀ H hadm v
  refine h.trans ?_
  have hZ0 : 0 < Z := by linarith
  have hamp : 0 ≤ gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) := by
    unfold gAmp
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans r.one_le_height) _)
  have hrest : 0 ≤ gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) *
      (1+‖v‖)^(2*(degA + 2*n₀ + 2*nJ)) *
      Z^(r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε) := by
    have := Real.rpow_nonneg hZ0.le (r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε)
    positivity
  have e1 : ctot CA CP Cred K₀ C₀ KJ CJ * gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) *
      (1+‖v‖)^(2*(degA + 2*n₀ + 2*nJ)) *
      Z^(r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε) =
      ctot CA CP Cred K₀ C₀ KJ CJ * (gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) *
      (1+‖v‖)^(2*(degA + 2*n₀ + 2*nJ)) *
      Z^(r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε)) := by ring
  have e2 : (ctot CA CP Cred K₀ C₀ KJ CJ + 1) *
      gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) *
      (1+‖v‖)^(2*(degA + 2*n₀ + 2*nJ)) *
      Z^(r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε) =
      (ctot CA CP Cred K₀ C₀ KJ CJ + 1) *
      (gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) *
      (1+‖v‖)^(2*(degA + 2*n₀ + 2*nJ)) *
      Z^(r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε)) := by ring
  change _ ≤ (ctot CA CP Cred K₀ C₀ KJ CJ + 1) *
      gAmp L θ mesh η Z r (degA + 2*n₀ + 2*nJ) (S₀ ∪ SJ) *
      (1+‖v‖)^(2*(degA + 2*n₀ + 2*nJ)) *
      Z^(r.colLog + r.twistLog + price.f w₀ (gP r) (∑ i, r.w i) H + ε)
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hrest

end
end QRH.DensitySplitThird.CubeFree.Packet.Grouped
