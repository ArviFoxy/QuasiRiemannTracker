/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Copyright (c) 2026 OpenAI. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FineAdaptiveSupplier
import Candidate.Local.Qrh.JointDetector.FinePointwisePrice

/-! The nonlinear price consumes the same actual zero/slot count and the same
LOW/HIGH decomposition. The selected operator estimate remains explicit. -/
namespace Qrh.JointDetector.FinePointwiseSupplier
noncomputable section
set_option autoImplicit false
open Set QRH.SilDensitySplit.CubeFree OAI.SevenEighths

/-- Scalar payment at each literal cut; no derivative of the cut is used. -/
theorem high_law : FineAdaptiveSupplier.HighLaw FinePointwisePrice.q0 FinePointwisePrice.highSup where
  floor_ge := le_rfl
  zero := by
    intro q ν P s M hq hν hs
    exact FinePointwisePrice.zero_energy_le_highSup hq hν le_rfl hs
  joint := by
    intro q ν δ P s M hq hν hδ hM hs
    exact FinePointwisePrice.jointRate_energy hq hν hδ hM hs
  full := by
    intro q ν P s M hq hν hs
    have hνg : ν ∈ Icc FinePointwisePrice.q0 (3/4) := ⟨hq.1.trans hν.1,hν.2⟩
    have hκ := FinePointwisePrice.slope_bounds hνg
    have hk0 := (FinePointwisePrice.slope_pos hνg).le
    have hext : 0 ≤ (ν-FinePointwisePrice.slope ν)*max (s-M/10) 0 :=
      mul_nonneg (sub_nonneg.mpr hκ.2) (le_max_right _ _)
    have hslot := mul_le_mul_of_nonneg_right
      (show ν-FinePointwisePrice.slope ν ≤ 1 by linarith [hν.2]) hs
    have hb := FinePointwisePrice.le_highSup hq.1 hν.1 hν.2 P s M
    unfold FinePointwisePrice.g at hb
    change (1-FinePointwisePrice.k ν)*M+ν*(P+s) ≤ M+FinePointwisePrice.highSup q P s M+s
    nlinarith

/-- All-real packed source for the literal nonlinear price. Count meshes are
chosen before the finite dictionary, while height degrees precede live heights. -/
theorem priced_source_of_whole_count
    (hwhole : FineNaturalCount.WholeJointCountOn (14/25))
    (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (qfun : ℝ → ℝ) (hq : ∀ w, qfun w ∈ Icc FinePointwisePrice.q0 (3/4))
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hB : 0 < B₀) (hB1 : B₀ ≤ 1) (hc : 0 < c₀)
    (hp : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (FinePointwisePrice.jointPrice B₀ L₀ c₀ hL qfun hq) (9/10) 4 4 :=
  FineAdaptiveSupplier.priced_source_of_whole_count hwhole
    FinePointwisePrice.q0 FinePointwisePrice.highSup high_law
    B₀ L₀ c₀ (9/10) 4 4 hL hβ ⟨hB,hB1,hc⟩ (by norm_num) (by norm_num) hp
    qfun hq (FinePointwisePrice.jointPrice B₀ L₀ c₀ hL qfun hq)
    (fun _ _ _ _ => rfl)

/-- Both old adaptive chains and the new nonlinear chain now require only
one explicit analytic input, the actual selected all-source norm estimate. -/
theorem priced_source (hnorm : FineNaturalCount.ActualSelectedSlotNorm)
    (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (qfun : ℝ → ℝ) (hq : ∀ w, qfun w ∈ Icc FinePointwisePrice.q0 (3/4))
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hB : 0 < B₀) (hB1 : B₀ ≤ 1) (hc : 0 < c₀)
    (hp : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (FinePointwisePrice.jointPrice B₀ L₀ c₀ hL qfun hq) (9/10) 4 4 :=
  priced_source_of_whole_count
    (FineNaturalCount.wholeJointCountOn_of_actualSelectedSlotNorm hnorm (14/25) le_rfl)
    B₀ L₀ c₀ hL qfun hq hβ hB hB1 hc hp

end
end Qrh.JointDetector.FinePointwiseSupplier

#print axioms Qrh.JointDetector.FinePointwiseSupplier.priced_source
