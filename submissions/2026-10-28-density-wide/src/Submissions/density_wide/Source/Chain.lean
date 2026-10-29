/- Fifteen exactly certified density transitions from Jacob Sussman's PR86 source.
Uses Sil's analytic source step with the widened density API. OpenAI Codex-assisted.
All analytic conclusions are conditional on the preprint's 7/8 theorem. -/
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_wide.Density.StepGates
import Submissions.density_wide.Density.Leaf
import Submissions.density_wide.Source.Wide01
import Submissions.density_wide.Source.Wide02
import Submissions.density_wide.Source.Wide03
import Submissions.density_wide.Source.Wide04
import Submissions.density_wide.Source.Wide05
import Submissions.density_wide.Source.Wide06
import Submissions.density_wide.Source.Wide07
import Submissions.density_wide.Source.Wide08
import Submissions.density_wide.Source.Wide09
import Submissions.density_wide.Source.Wide10
import Submissions.density_wide.Source.Wide11
import Submissions.density_wide.Source.Wide12
import Submissions.density_wide.Source.Wide13
import Submissions.density_wide.Source.Wide14
import Submissions.density_wide.Source.Wide15

set_option autoImplicit false
namespace QRH.DensityWide
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

theorem final_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (977400389 / 1000000000 : ℝ) (4383001 / 2000000 : ℝ) (1 / 10 : ℝ) := by
  have s00 : QRH.Record1252270103Source.GlobalSource (9888151 / 10000000 : ℝ) (4683001 / 2000000 : ℝ) (1 / 10 : ℝ) := QRH.SilDensitySplit.K15.final_source hβ
  have s01 : QRH.Record1252270103Source.GlobalSource (98815053 / 100000000 : ℝ) (4663001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide01
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s00
  have s02 : QRH.Record1252270103Source.GlobalSource (987471991 / 1000000000 : ℝ) (4643001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide02
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s01
  have s03 : QRH.Record1252270103Source.GlobalSource (986779537 / 1000000000 : ℝ) (4623001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide03
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s02
  have s04 : QRH.Record1252270103Source.GlobalSource (493036607 / 500000000 : ℝ) (4603001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide04
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s03
  have s05 : QRH.Record1252270103Source.GlobalSource (492676537 / 500000000 : ℝ) (4583001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide05
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s04
  have s06 : QRH.Record1252270103Source.GlobalSource (984619161 / 1000000000 : ℝ) (4563001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide06
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s05
  have s07 : QRH.Record1252270103Source.GlobalSource (196774303 / 200000000 : ℝ) (4543001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide07
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s06
  have s08 : QRH.Record1252270103Source.GlobalSource (983110177 / 1000000000 : ℝ) (4523001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide08
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s07
  have s09 : QRH.Record1252270103Source.GlobalSource (982335187 / 1000000000 : ℝ) (4503001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide09
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s08
  have s10 : QRH.Record1252270103Source.GlobalSource (981546581 / 1000000000 : ℝ) (4483001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide10
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s09
  have s11 : QRH.Record1252270103Source.GlobalSource (98074439 / 100000000 : ℝ) (4463001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide11
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s10
  have s12 : QRH.Record1252270103Source.GlobalSource (122491081 / 125000000 : ℝ) (4443001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide12
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s11
  have s13 : QRH.Record1252270103Source.GlobalSource (489549691 / 500000000 : ℝ) (4423001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide13
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s12
  have s14 : QRH.Record1252270103Source.GlobalSource (978256621 / 1000000000 : ℝ) (4403001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide14
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s13
  have s15 : QRH.Record1252270103Source.GlobalSource (977400389 / 1000000000 : ℝ) (4383001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_Wide15
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s14
  exact s15

end
end QRH.DensityWide
