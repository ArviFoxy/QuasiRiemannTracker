import Submissions.arvi_density_lab.Source.Gen_01
import Submissions.arvi_density_lab.Source.Gen_23
import Submissions.arvi_density_lab.Source.Gen_46
import Submissions.density_split_fine_chain.Source.ChainK15

/-! Test of the regenerated steps `Gen_01`, `Gen_23`, `Gen_46` (generator `research/density/gen_hybrid.py`):
(1) each generated theorem has literally the statement of PR 86's `hybridGates_HybridK15_NN`;
(2) each feeds PR 86's `K15.density_step` exactly as `ChainK15.final_source` does. -/

open QRH.SilDensitySplit
open QRH.Record1252270103Source

example : type_of% hybridGates_HybridK15_01 := QRH.ArviDensityLab.hybridGates_Gen_01
example : type_of% hybridGates_HybridK15_23 := QRH.ArviDensityLab.hybridGates_Gen_23
example : type_of% hybridGates_HybridK15_46 := QRH.ArviDensityLab.hybridGates_Gen_46

example (hβ : (51/100 : ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : GlobalSource (99999 / 100000 : ℝ) (5143 / 2000 : ℝ) (1397 / 10000 : ℝ)) :
    GlobalSource (2499583 / 2500000 : ℝ) (5133 / 2000 : ℝ) (1 / 10 : ℝ) :=
  K15.density_step QRH.ArviDensityLab.hybridGates_Gen_01
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) hβ hp

example (hβ : (51/100 : ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : GlobalSource (9956333 / 10000000 : ℝ) (12307501 / 5000000 : ℝ) (1 / 10 : ℝ)) :
    GlobalSource (1244239 / 1250000 : ℝ) (12282501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
  K15.density_step QRH.ArviDensityLab.hybridGates_Gen_23
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) hβ hp

example (hβ : (51/100 : ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : GlobalSource (4945703 / 5000000 : ℝ) (5866251 / 2500000 : ℝ) (1 / 10 : ℝ)) :
    GlobalSource (9888151 / 10000000 : ℝ) (4683001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
  K15.density_step QRH.ArviDensityLab.hybridGates_Gen_46
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) hβ hp

#print axioms QRH.ArviDensityLab.hybridGates_Gen_01
#print axioms QRH.ArviDensityLab.hybridGates_Gen_23
#print axioms QRH.ArviDensityLab.hybridGates_Gen_46
