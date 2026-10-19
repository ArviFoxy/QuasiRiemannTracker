/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.MainParameters
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule

set_option autoImplicit false
namespace OAI.SevenEighths.MainReconstruction
noncomputable section
open Cycle63InitialMass

/-- The smaller error reserve is paid using the actual capped loss unit. -/
theorem main_paid_error_loss (Mmin εaffine M reserve loss : ℝ)
    (hMmin : 0<Mmin) (hM : Mmin≤M)
    (hεcap : εaffine≤Mmin/1000000000)
    (hr : Sil.Uneven.MainSource.errorReserve≤reserve)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    -M*reserve+loss≤-M*(1/2000000000) := by
  have hu : geometryLossUnit Mmin εaffine≤εaffine/128 := min_le_left _ _
  have hres := mul_le_mul_of_nonneg_left hr (hMmin.trans_le hM).le
  norm_num [Sil.Uneven.MainSource.errorReserve] at hres
  linarith only [hu,hres,hεcap,hloss,hM,hMmin]

end
end OAI.SevenEighths.MainReconstruction
#print axioms OAI.SevenEighths.MainReconstruction.main_paid_error_loss
