/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Uneven.BootstrapMonotone

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem physicalGain_monotone {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (S : ℝ) :
    Monotone (physicalGain d S) := by
  intro D D' hD
  exact FiniteGain.gain_mono (coefficient_nonneg hd0 hd1).1
    (coefficient_nonneg hd0 hd1).2 le_rfl hD

theorem physicalGain_width_error {d S T D : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hST : S ≤ T) :
    physicalGain d T D-d*(T-S) ≤ physicalGain d S D := by
  apply FiniteGain.gain_lower
  intro i
  have hi := FiniteGain.gain_le (slope d) (offset d) T D i
  have he := mul_nonneg (sub_nonneg.mpr (slope_le_density hd0 hd1 i)) (sub_nonneg.mpr hST)
  unfold physicalGain
  nlinarith only [hi,he]

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.physicalGain_monotone
#print axioms Sil.Uneven.Bootstrap.physicalGain_width_error
