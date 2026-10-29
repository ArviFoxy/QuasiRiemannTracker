/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FineSourceChains.Common
import Candidate.Local.Qrh.JointDetector.FinePointwiseSupplier

/-! Close the finite chain's provider with the actual all-height packed
supplier, retaining its early mesh and arbitrary requested tolerance. -/
namespace Qrh.JointDetector.FinePackedProvider
noncomputable section
set_option autoImplicit false

theorem provider (hnorm : FineNaturalCount.ActualSelectedSlotNorm) :
    FineSourceChains.PackedProvider := by
  intro B0 L0 B L hL hβ hB hB1 hp
  simpa only [FinePointwiseLedger.stepData] using
    FinePointwiseSupplier.priced_source hnorm B0 L0 FineSourceChains.cap hL
      (FinePointwiseLedger.densQ FineSourceChains.phi B0 L0 L
        FineSourceChains.amp 0 (QRH.SilDensitySplit.Hybrid.cross B0 L0 B L))
      (FinePointwiseLedger.densQ_mem FineSourceChains.phi B0 L0 L
        FineSourceChains.amp 0 (QRH.SilDensitySplit.Hybrid.cross B0 L0 B L))
      hβ hB hB1 (by norm_num [FineSourceChains.cap]) hp

end
end Qrh.JointDetector.FinePackedProvider

#print axioms Qrh.JointDetector.FinePackedProvider.provider
