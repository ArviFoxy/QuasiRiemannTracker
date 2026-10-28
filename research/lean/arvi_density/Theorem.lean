/- The density-split leaf with a floor parameter, at the floor `qf = 3/5`.

`Density.density_priced_source` and `Density.dsGates` are the floor-`qf` analogues of PR 83's
`density_priced_source` and `dsGates` (`3/5 ≤ qf ≤ 3/4`, the HIGH row count being Collet's PR 67
vintage of `fixed_natural_dictionary_raw_density` at `4/5 ≤ a`); `Density.density_step` composes
them with Sil's generic engine. This file instantiates them at `qf = 3/5`, i.e. a density cut
`q ≥ 3/5` (real parts `a ≥ 4/5`) instead of `q ≥ 13/20`:

* `density_priced_source_three_fifths`: the Seam A leaf with the price `densityPrice (3/5) …`;
* `dsGates_three_fifths`: `HybridGates (3/5) …` and the face facts give the engine's `StepGates`;
* `density_step_three_fifths`: the engine's step `G(B₀,L₀,c₀) → G(B,L,c)`.

Sil's two certified transitions (floor `13/20`) are also certified at the floor `3/5`
(`HybridGates.ofSil_of_le`), so `sil_first_step_three_fifths` and `sil_second_step_three_fifths`
are concrete instances of `density_step_three_fifths`. -/
import Submissions.arvi_density.Density.Step
import Submissions.arvi_density.Density.Compat

set_option autoImplicit false
namespace QRH.ArviDensity
noncomputable section
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- **Density Seam A at the floor `qf = 3/5`.** -/
theorem density_priced_source_three_fifths (B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain : ℝ)
    (hL : 0 < L₀) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource
      (Density.densityPrice (3/5) B₀ L₀ c₀ L A D s₀ hL (by norm_num) (by norm_num))
      Mmin Mmax Lplain :=
  Density.density_priced_source (3/5) B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain hL (by norm_num) (by norm_num)
    hβ hface h0 h1 hparent

/-- **Step gates at the floor `qf = 3/5`.** -/
theorem dsGates_three_fifths {B₀ L₀ c₀ B L c A D : ℝ} (h : HybridGates (3/5) B₀ L₀ c₀ B L c A D)
    (hF : Density.DSFace B₀ L₀ c₀ B L c) (hL : 0 < L₀) :
    StepGates (Density.dsData (3/5) B₀ L₀ c₀ B L c A D hL (by norm_num) (by norm_num)) :=
  Density.dsGates h hF hL _ _

/-- **The density-split step at the floor `qf = 3/5`**, accepted by the generic cube-free engine. -/
theorem density_step_three_fifths (B₀ L₀ c₀ B L c A D : ℝ) (hL : 0 < L₀) (hB₀ : 0 < B₀)
    (h : HybridGates (3/5) B₀ L₀ c₀ B L c A D) (hF : Density.DSFace B₀ L₀ c₀ B L c)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c :=
  Density.density_step (3/5) B₀ L₀ c₀ B L c A D hL (by norm_num) (by norm_num) hB₀ h hF hβ hparent

/-- PR 83's first transition `G(9999/10000, 129/50, 3/25) → G(9959/10000, 5/2, 1/10)`
(`A = 6/5`, `D = 140`, certified with floor `13/20`, hence with floor `3/5`) as an instance of
`density_step_three_fifths`. -/
theorem sil_first_step_three_fifths (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (9999/10000) (129/50) (3/25)) :
    QRH.Record1252270103Source.GlobalSource (9959/10000) (5/2) (1/10) :=
  density_step_three_fifths _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (HybridGates.ofSil_of_le (by norm_num) QRH.SilDensitySplit.hybridGates_first)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ hβ hparent

/-- PR 83's second transition `G(9959/10000, 5/2, 1/10) → G(4967/5000, 49/20, 1/10)`
(`A = 7/10`, `D = 70`) as an instance of `density_step_three_fifths`. -/
theorem sil_second_step_three_fifths (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (9959/10000) (5/2) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (4967/5000) (49/20) (1/10) :=
  density_step_three_fifths _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (HybridGates.ofSil_of_le (by norm_num) QRH.SilDensitySplit.hybridGates_second)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ hβ hparent

#print axioms Density.density_priced_source
#print axioms Density.dsGates
#print axioms Density.density_step
#print axioms density_priced_source_three_fifths
#print axioms dsGates_three_fifths
#print axioms density_step_three_fifths
#print axioms sil_first_step_three_fifths
#print axioms sil_second_step_three_fifths
#print axioms Density.density_priced_source_thirteen_twentieths
#print axioms Density.dsGates_first_of_floor
#print axioms Density.dsGates_second_of_floor


/-- **The density-split step at any floor `qf ∈ [1/2, 3/4]`** (HIGH count from Collet's
3/4-range wrappers, `Density/NaturalEndpoint34.lean`). -/
theorem density_step_floor (qf B₀ L₀ c₀ B L c A D : ℝ) (hqf : 1/2 ≤ qf) (hqf' : qf ≤ 3/4)
    (hL : 0 < L₀) (hB₀ : 0 < B₀)
    (h : HybridGates qf B₀ L₀ c₀ B L c A D) (hF : Density.DSFace B₀ L₀ c₀ B L c)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c :=
  Density.density_step qf B₀ L₀ c₀ B L c A D hL hqf hqf' hB₀ h hF hβ hparent

end
end QRH.ArviDensity

#print axioms QRH.ArviDensity.density_step_floor
