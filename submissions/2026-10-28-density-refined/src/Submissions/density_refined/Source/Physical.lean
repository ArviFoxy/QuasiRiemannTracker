/- Based on Sil's density-split steps and Jacob Sussman's exact fine-chain instances (#86).
This is precisely the first 38 certified steps, exposed for the physical return.
Apache-2.0; AI-assisted (OpenAI Codex), 2026-10-28. -/
import Submissions.density_split_fine_chain.Source.ChainK15
set_option autoImplicit false
namespace QRH.DensityRefined
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.K15
theorem physical_source (hβ : (51/100 : ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (2478297 / 2500000 : ℝ) (5953751 / 2500000 : ℝ) (1 / 10 : ℝ) := by
  have s00 : QRH.Record1252270103Source.GlobalSource (99999 / 100000 : ℝ) (5143 / 2000 : ℝ) (1397 / 10000 : ℝ) := by
    simpa only [Face.Source, bootFace] using boot_source hβ
  have s01 : QRH.Record1252270103Source.GlobalSource (2499583 / 2500000 : ℝ) (5133 / 2000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_01
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s00
  have s02 : QRH.Record1252270103Source.GlobalSource (2499181 / 2500000 : ℝ) (5123 / 2000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_02
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s01
  have s03 : QRH.Record1252270103Source.GlobalSource (2498769 / 2500000 : ℝ) (25565001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_03
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s02
  have s04 : QRH.Record1252270103Source.GlobalSource (2498347 / 2500000 : ℝ) (25515001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_04
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s03
  have s05 : QRH.Record1252270103Source.GlobalSource (499583 / 500000 : ℝ) (25465001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_05
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s04
  have s06 : QRH.Record1252270103Source.GlobalSource (2497473 / 2500000 : ℝ) (25415001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_06
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s05
  have s07 : QRH.Record1252270103Source.GlobalSource (1997617 / 2000000 : ℝ) (25365001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_07
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s06
  have s08 : QRH.Record1252270103Source.GlobalSource (4993119 / 5000000 : ℝ) (25315001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_08
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s07
  have s09 : QRH.Record1252270103Source.GlobalSource (312011 / 312500 : ℝ) (12632501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_09
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s08
  have s10 : QRH.Record1252270103Source.GlobalSource (9982427 / 10000000 : ℝ) (12607501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_10
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s09
  have s11 : QRH.Record1252270103Source.GlobalSource (9980463 / 10000000 : ℝ) (12582501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_11
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s10
  have s12 : QRH.Record1252270103Source.GlobalSource (9978461 / 10000000 : ℝ) (12557501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_12
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s11
  have s13 : QRH.Record1252270103Source.GlobalSource (498821 / 500000 : ℝ) (12532501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_13
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s12
  have s14 : QRH.Record1252270103Source.GlobalSource (498717 / 500000 : ℝ) (12507501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_14
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s13
  have s15 : QRH.Record1252270103Source.GlobalSource (4986111 / 5000000 : ℝ) (12482501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_15
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s14
  have s16 : QRH.Record1252270103Source.GlobalSource (4985033 / 5000000 : ℝ) (12457501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_16
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s15
  have s17 : QRH.Record1252270103Source.GlobalSource (77874 / 78125 : ℝ) (12432501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_17
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s16
  have s18 : QRH.Record1252270103Source.GlobalSource (249141 / 250000 : ℝ) (24815001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_18
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s17
  have s19 : QRH.Record1252270103Source.GlobalSource (996337 / 1000000 : ℝ) (24765001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_19
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s18
  have s20 : QRH.Record1252270103Source.GlobalSource (4980531 / 5000000 : ℝ) (24715001 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_20
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s19
  have s21 : QRH.Record1252270103Source.GlobalSource (2489679 / 2500000 : ℝ) (12332501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_21
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s20
  have s22 : QRH.Record1252270103Source.GlobalSource (9956333 / 10000000 : ℝ) (12307501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_22
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s21
  have s23 : QRH.Record1252270103Source.GlobalSource (1244239 / 1250000 : ℝ) (12282501 / 5000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_23
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s22
  have s24 : QRH.Record1252270103Source.GlobalSource (4975727 / 5000000 : ℝ) (24515003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_24
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s23
  have s25 : QRH.Record1252270103Source.GlobalSource (9948959 / 10000000 : ℝ) (24465003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_25
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s24
  have s26 : QRH.Record1252270103Source.GlobalSource (9946427 / 10000000 : ℝ) (24415003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_26
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s25
  have s27 : QRH.Record1252270103Source.GlobalSource (4971929 / 5000000 : ℝ) (24365003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_27
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s26
  have s28 : QRH.Record1252270103Source.GlobalSource (2485313 / 2500000 : ℝ) (24315003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_28
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s27
  have s29 : QRH.Record1252270103Source.GlobalSource (9938609 / 10000000 : ℝ) (24265003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_29
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s28
  have s30 : QRH.Record1252270103Source.GlobalSource (993593 / 1000000 : ℝ) (24215003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_30
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s29
  have s31 : QRH.Record1252270103Source.GlobalSource (4966607 / 5000000 : ℝ) (24165003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_31
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s30
  have s32 : QRH.Record1252270103Source.GlobalSource (4965231 / 5000000 : ℝ) (24115003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_32
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s31
  have s33 : QRH.Record1252270103Source.GlobalSource (9927673 / 10000000 : ℝ) (24065003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_33
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s32
  have s34 : QRH.Record1252270103Source.GlobalSource (620303 / 625000 : ℝ) (6003751 / 2500000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_34
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s33
  have s35 : QRH.Record1252270103Source.GlobalSource (9921987 / 10000000 : ℝ) (5991251 / 2500000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_35
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s34
  have s36 : QRH.Record1252270103Source.GlobalSource (991909 / 1000000 : ℝ) (5978751 / 2500000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_36
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s35
  have s37 : QRH.Record1252270103Source.GlobalSource (9916157 / 10000000 : ℝ) (23865003 / 10000000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_37
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s36
  have s38 : QRH.Record1252270103Source.GlobalSource (2478297 / 2500000 : ℝ) (5953751 / 2500000 : ℝ) (1 / 10 : ℝ) :=
    density_step hybridGates_HybridK15_38
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s37
  exact s38
end
end QRH.DensityRefined
