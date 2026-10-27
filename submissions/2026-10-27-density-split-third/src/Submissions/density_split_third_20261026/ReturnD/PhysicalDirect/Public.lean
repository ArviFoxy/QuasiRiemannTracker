/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Public (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.DensitySplitThird.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.density_split_third_20261026.ReturnD.Schedule
import Submissions.density_split_third_20261026.ReturnD.PhysicalDirect.Active
import Submissions.density_split_third_20261026.ReturnD.PhysicalDirect.ActualBin
import Submissions.density_split_third_20261026.ReturnD.PhysicalDirect.Selection
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false

open QRH.Record1252270103Return

namespace QRH.DensitySplitThird.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [QRH.DensitySplitThird.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.DensitySplitThird.Return.GenericArithmetic

/-- The original positive physical slot dictionary is fine enough after every
allowed row-scale rescaling. No total-width or cardinality loss is added. -/
theorem rescaled_slot_mesh {n : ℕ} (lengths : Fin n → ℝ) (mesh d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (hmesh : 0 ≤ mesh)
    (hfine : ∀ j, lengths j ≤ mesh / 200) :
    ∀ j, lengths j / d ≤ mesh := by
  have hp : 0 < d := by linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

theorem source_slot_power (Z d width : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) :
    (Z ^ d) ^ (width / d) = Z ^ width := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ width hd]

end QRH.DensitySplitThird.Return.GenericPhysical.PhysicalDirect

