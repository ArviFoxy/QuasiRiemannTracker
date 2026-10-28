/- The marked density-split step of this package at the floor `qf = 3/5`, with generated certificates.

`Density.density_step_marked` is the step `G(B₀,L₀,c₀) → G(B,L,c)` from `HybridGatesM qf …` (the gates of
`HybridGates` with the unmarked HIGH fields replaced by the marked HIGH gate, which pays the HIGH term with
PR 76's repeated-mark gain), the face facts `DSFace` and `22/23 ≤ B₀`. This file instantiates it at
`qf = 3/5` (real parts `a ≥ 4/5`) and applies it to certificates produced by
`research/density/gen_hybrid.py --marked --floor 3/5`:

* `k15_46_marked_step`: PR 86's transition 46,
  `G(4945703/5000000, 5866251/2500000, 1/10) → G(9888151/10000000, 4683001/2000000, 1/10)`
  (`A = 1/2`, `D = 5713/250`), certified with the marked HIGH gate (`Source.HybridMarkedK15_46`);
* `stretch_marked_step`: a transition from the same parent whose child has `B` lowered by `3/10000`
  (`A = 2/5`), `G(4945703/5000000, …) → G(4944203/5000000, 4683001/2000000, 1/10)`
  (`Source.HybridMarkedStretch46`). For it the unmarked gate `high_at_q` is negative at `v = 0`
  (`-0.0045`), so no `HybridGates` certificate exists, while the marked HIGH gate holds with reserve
  `41/25000` on all of `[0, c - s₀] × [q(v), 3/4] × [0, 1/2]`;
* `sil_first_step_marked`, `sil_second_step_marked`: PR 83's two certified transitions through
  `HybridGatesM.ofHybridGates` (every unmarked certificate is a marked one). -/
import Submissions.arvi_density.Density.StepMarked
import Submissions.arvi_density.Density.Compat
import Submissions.arvi_density.Source.HybridMarkedK15_46
import Submissions.arvi_density.Source.HybridMarkedStretch46

set_option autoImplicit false
namespace QRH.ArviDensity
noncomputable section
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- **The marked density-split step at the floor `qf = 3/5`.** -/
theorem density_step_marked_three_fifths (B₀ L₀ c₀ B L c A D : ℝ) (hB₀ : 22/23 ≤ B₀)
    (h : HybridGatesM (3/5) B₀ L₀ c₀ B L c A D) (hF : Density.DSFace B₀ L₀ c₀ B L c)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    QRH.Record1252270103Source.GlobalSource B L c :=
  Density.density_step_marked (3/5) B₀ L₀ c₀ B L c A D (by norm_num) (by norm_num) hB₀ h hF hβ hparent

/-- PR 86's transition 46 (`A = 1/2`, `D = 5713/250`) with the marked HIGH gate at the floor `3/5`. -/
theorem k15_46_marked_step (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (4945703 / 5000000) (5866251 / 2500000)
      (1 / 10)) :
    QRH.Record1252270103Source.GlobalSource (9888151 / 10000000) (4683001 / 2000000) (1 / 10) :=
  density_step_marked_three_fifths _ _ _ _ _ _ _ _ (by norm_num)
    hybridGatesM_HybridMarkedK15_46
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ hβ hparent

/-- A transition beyond the unmarked gates: the same parent, `B` lowered by `3/10000` (`A = 2/5`). -/
theorem stretch_marked_step (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (4945703 / 5000000) (5866251 / 2500000)
      (1 / 10)) :
    QRH.Record1252270103Source.GlobalSource (4944203 / 5000000) (4683001 / 2000000) (1 / 10) :=
  density_step_marked_three_fifths _ _ _ _ _ _ _ _ (by norm_num)
    hybridGatesM_HybridMarkedStretch46
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ hβ hparent

/-- PR 83's first transition (certified with floor `13/20`, hence with floor `3/5`) as a marked step. -/
theorem sil_first_step_marked (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (9999/10000) (129/50) (3/25)) :
    QRH.Record1252270103Source.GlobalSource (9959/10000) (5/2) (1/10) :=
  Density.density_step_marked_of_hybridGates (3/5) _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (HybridGates.ofSil_of_le (by norm_num) QRH.SilDensitySplit.hybridGates_first)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ hβ hparent

/-- PR 83's second transition as a marked step. -/
theorem sil_second_step_marked (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hparent : QRH.Record1252270103Source.GlobalSource (9959/10000) (5/2) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (4967/5000) (49/20) (1/10) :=
  Density.density_step_marked_of_hybridGates (3/5) _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (HybridGates.ofSil_of_le (by norm_num) QRH.SilDensitySplit.hybridGates_second)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ hβ hparent

end
end QRH.ArviDensity

#print axioms QRH.ArviDensity.HybridGatesM.ofHybridGates
#print axioms QRH.ArviDensity.le_gainC_of_facets
#print axioms QRH.ArviDensity.gHighM_scaled
#print axioms QRH.ArviDensity.Density.ds_ledger_marked
#print axioms QRH.ArviDensity.Density.dsGatesM
#print axioms QRH.ArviDensity.Density.density_step_marked
#print axioms QRH.ArviDensity.Density.density_step_marked_of_hybridGates
#print axioms QRH.ArviDensity.density_step_marked_three_fifths
#print axioms QRH.ArviDensity.HybridMarkedK15_46.markedHigh
#print axioms QRH.ArviDensity.hybridGatesM_HybridMarkedK15_46
#print axioms QRH.ArviDensity.hybridGatesM_HybridMarkedStretch46
#print axioms QRH.ArviDensity.k15_46_marked_step
#print axioms QRH.ArviDensity.stretch_marked_step
#print axioms QRH.ArviDensity.sil_first_step_marked
#print axioms QRH.ArviDensity.sil_second_step_marked
