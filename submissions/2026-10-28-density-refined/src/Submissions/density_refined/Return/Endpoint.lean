/- Based on Sil's density-split return, ArviFoxy's all-shift return, and
Hailey Collet's generic source machinery (Apache-2.0).
Separate proved count and physical sources; AI-assisted (OpenAI Codex), 2026-10-28.
The natural density cap uses the preprint's 7/8 theorem. -/
import Submissions.density_refined.Return.EndpointFromSources
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensityRefined.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

abbrev countSourceFace : SourceFace :=
  QRH.Record1252270103Source.globalFace (488842537/500000000) (4388001/2000000) (1/10)
abbrev physicalSourceFace : SourceFace :=
  QRH.Record1252270103Source.globalFace (2478297/2500000) (5953751/2500000) (1/10)

theorem source_restricts_count : countSourceFace.Restricts countGlobal := by
 constructor <;> norm_num [countSourceFace,QRH.Record1252270103Source.globalFace,countGlobal,
  QRH.Record1252270103Return.globalFace,countCB,countCL,countCap]

theorem source_restricts_physical : physicalSourceFace.Restricts physicalGlobal := by
 constructor <;> norm_num [physicalSourceFace,QRH.Record1252270103Source.globalFace,physicalGlobal,
  QRH.Record1252270103Return.globalFace,physicalB,physicalLambda,physicalCap]

theorem uniform_restrict {strong weak : SourceFace} (h : strong.Restricts weak)
 (hs : UniformUnitFaceSource strong) : UniformUnitFaceSource weak := by
 intro ε hε
 obtain ⟨mesh,hm,hsrc⟩ := hs ε hε
 exact ⟨mesh,hm,unit_source_restrict h hsrc⟩

lemma natural_cap_return : 2*HeckeZeroSupremum.beta-1≤naturalK/6 := by
 have hi := QRH.RepeatedMarks.beta_le_seven_eighths
 norm_num [naturalK]
 linarith

theorem beta_of_two_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤theta :=
 Final.beta_of_global_sources hC hP natural_cap_return

theorem beta_le_theta_of_sources
    (hcount : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (488842537/500000000) (4388001/2000000) (1/10))
    (hphysical : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (2478297/2500000) (5953751/2500000) (1/10)) :
    HeckeZeroSupremum.beta ≤ (8739461/10000000 : ℝ) := by
  rw [← theta_value]
  by_cases hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · exact beta_of_two_global_sources
      (uniform_restrict source_restricts_count (hcount hbeta))
      (uniform_restrict source_restricts_physical (hphysical hbeta))
  · have ht : (51/100:ℝ) ≤ theta := by norm_num [theta,c]
    exact (not_le.mp hbeta).le.trans ht

theorem dirichlet_of_sources
    (hcount : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (488842537/500000000) (4388001/2000000) (1/10))
    (hphysical : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (2478297/2500000) (5953751/2500000) (1/10))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8739461 / 10000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num)
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      ((beta_le_theta_of_sources hcount hphysical).trans_lt hs) hpole) χ s hs hpole
end
end QRH.DensityRefined.Return
