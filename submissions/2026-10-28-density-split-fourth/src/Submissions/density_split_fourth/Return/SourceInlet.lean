/- Repeated marks: fork of Collet's final-stage module SourceInlet (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the two global faces are the count face C = (4967/5000, 49/20, 9999/100000)
and the physical face P = (9933999/10^7, 2451/1000, 31/500); the unused window faces
(`countWindow`, `physicalWindow`) and `source_on_root_interval` are removed. -/
import Submissions.density_split_fourth.Return.Constants
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensitySplitThird.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

def countGlobal : SourceFace := globalFace countCB countCL countCap
def fourthCountGlobal : SourceFace := globalFace fourthCountB fourthCountL countCap
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda physicalCap

/-- Choose one mesh for all three source roles before any live parameters. -/
theorem selected_sources_common_mesh
    (hC : UniformUnitFaceSource countGlobal)
    (hF : UniformUnitFaceSource fourthCountGlobal)
    (hP : UniformUnitFaceSource physicalGlobal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧ UnitFaceSource countGlobal mesh ε ∧
      UnitFaceSource fourthCountGlobal mesh ε ∧
      UnitFaceSource physicalGlobal mesh ε := by
  obtain ⟨c, hc, hcs⟩ := hC ε hε
  obtain ⟨f, hf, hfs⟩ := hF ε hε
  obtain ⟨p, hp, hps⟩ := hP ε hε
  refine ⟨min (min c f) p, lt_min (lt_min hc hf) hp, ?_, ?_, ?_⟩
  · exact hcs.mono_mesh ((min_le_left _ _).trans (min_le_left _ _))
  · exact hfs.mono_mesh ((min_le_left _ _).trans (min_le_right _ _))
  · exact hps.mono_mesh (min_le_right _ _)
end
end QRH.DensitySplitThird.Return
