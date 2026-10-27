/- Copyright (c) 2026 Sil. Apache-2.0.
Both exact scalar hybrid transitions of the density-split argument (Section 5):
G(9999/10000, 129/50, 3/25) → G(9959/10000, 5/2, 1/10)   with A = 6/5,  D = 140;
G(9959/10000, 5/2, 1/10)    → G(4967/5000, 49/20, 1/10)  with A = 7/10, D = 70.
Arithmetic only; the analytic density-split step is not proved here. -/
import Submissions.sil_density_split_20261026.Source.HybridCertificatesFirst
import Submissions.sil_density_split_20261026.Source.HybridCertificatesSecond

set_option autoImplicit false
namespace QRH.SilDensitySplit

/-- The two hybrid transitions, each with all gates uniformly positive on `v ∈ [0, 1/20]`. -/
theorem hybridGates_chain :
    HybridGates (9999 / 10000) (129 / 50) (3 / 25) (9959 / 10000) (5 / 2) (1 / 10) (6 / 5) 140 ∧
      HybridGates (9959 / 10000) (5 / 2) (1 / 10) (4967 / 5000) (49 / 20) (1 / 10) (7 / 10) 70 :=
  ⟨hybridGates_first, hybridGates_second⟩

end QRH.SilDensitySplit
