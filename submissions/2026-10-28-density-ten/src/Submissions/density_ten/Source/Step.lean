/- Source-step wrapper from tracker PR89, included to make this submission
independent of its pending admission. AI-assisted OpenAI Codex; inherited credits.
Conditional on the preprint 7/8 theorem. Apache-2.0. -/
import Submissions.density_ten.Density.StepGates
import Submissions.density_ten.Density.Leaf
import Submissions.density_split_fine_chain.Source.ChainK15
set_option autoImplicit false
namespace QRH.DensityTen
noncomputable section
open QRH.SilDensitySplit

theorem density_step {B₀ L₀ c₀ B L c A D : ℝ}
    (h : HybridGates B₀ L₀ c₀ B L c A D)
    (hF : Density.DSFace B₀ L₀ c₀ B L c) (hL : 0 < L₀) (hB : 0 < B₀) (hc : 0 < c₀)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c := by
  have G := Density.dsGates h hF hL
  have hleaf := Density.density_priced_source B₀ L₀ c₀ L A D (Hybrid.cross B₀ L₀ B L) (9/10) (3+1) 4 hL hβ
    ⟨hB, hF.B₀_lt.le, hc⟩ (by norm_num) (by norm_num) hp
  have hI := CubeFree.Assembly.step_inputs_of_provider _ G 4 (fun _ hl =>
    CubeFree.Second.Provider.contrary_raw_side_provider G 4 le_rfl hl (CubeFree.Second.ProviderDiag.diag_supply G))
  exact CubeFree.cubefree_step _ G 4 hI hβ hp hleaf

end
end QRH.DensityTen
