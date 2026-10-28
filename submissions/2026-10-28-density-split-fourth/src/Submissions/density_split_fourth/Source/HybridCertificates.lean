/- Copyright (c) 2026 Sil. Apache-2.0.
Both exact scalar hybrid transitions of the density-split argument (Section 5):
G(9999/10000, 129/50, 3/25) → G(9959/10000, 5/2, 1/10)   with A = 6/5,  D = 140;
G(9959/10000, 5/2, 1/10)    → G(4967/5000, 49/20, 1/10)  with A = 7/10, D = 70.
Arithmetic only; the analytic density-split step is not proved here. -/
import Submissions.density_split_fourth.Source.HybridCertificatesFirst
import Submissions.density_split_fourth.Source.HybridCertificatesSecond
import Submissions.density_split_fourth.Source.HybridCertificatesThird
import Submissions.density_split_fourth.Source.HybridFourthPhysical
import Submissions.density_split_fourth.Source.HybridFourthCount

set_option autoImplicit false
namespace QRH.DensitySplitThird

/-- The two hybrid transitions, each with all gates uniformly positive on `v ∈ [0, 1/20]`. -/
theorem hybridGates_chain :
    HybridGates (9999 / 10000) (129 / 50) (3 / 25) (9959 / 10000) (5 / 2) (1 / 10) (6 / 5) 140 ∧
      HybridGates (9959 / 10000) (5 / 2) (1 / 10) (4967 / 5000) (49 / 20) (1 / 10) (7 / 10) 70 :=
  ⟨hybridGates_first, hybridGates_second⟩

end QRH.DensitySplitThird
