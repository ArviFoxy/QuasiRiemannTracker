/- Repeated marks: fork of Collet's generic return module PhysicalDirect.ChosenMesh (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Arbitrarily fine simultaneous source/count/probe data. Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.DensitySplitThird.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.density_split_third_20261026.ReturnD.Schedule
import Submissions.density_split_third_20261026.ReturnD.PhysicalDirect.Chosen
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.DensitySplitThird.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [QRH.DensitySplitThird.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open OAI.SevenEighths QRH.DensitySplitThird.Return.GenericArithmetic QRH.Record12518109Count

theorem exists_chosen_data_small_mesh (hgap : theta<HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (extraMesh : ℝ) (hmesh : 0<extraMesh) :
    ∃A : ChosenData,A.sourceMesh≤extraMesh := by
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hgap hκbeta (fun _=>extraMesh) (fun _ _=>hmesh)
  exact ⟨A,hA.le⟩
end
end QRH.DensitySplitThird.Return.GenericPhysical.PhysicalDirect
