/- Copyright (c) 2026 Sil. Apache-2.0.
The return at theta = 174797/200000 from the global source G(99/100, 239/100, 1/10).
Adapted from PR76 `FinalReturn/EndpointFromGlobalSources.lean` and `Graph/Endpoint.lean`
(Repeated marks, Apache-2.0; forks of Collet's Record1252270103Graph, Apache-2.0).
The count face C = (4967/5000, 49/20, 9999/100000) and the physical face
P = (9933999/10^7, 2451/1000, 31/500) are literal subfaces of G. The natural cap
`2β − 1 ≤ naturalK/6 = 3/4` is the baseline's `β ≤ 7/8` (PR76 `Graph/NaturalCap.lean`).
The source G is a hypothesis here, under `51/100 ≤ β`; the complementary case is trivial. -/
import Submissions.density_split_third_20261026.Return.EndpointFromSources
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensitySplitThird.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

/-- The global face of the source G(99/100, 239/100, 1/10). -/
abbrev sourceFace : SourceFace := QRH.Record1252270103Source.globalFace (99/100) (239/100) (1/10)

theorem source_restricts_count : sourceFace.Restricts countGlobal := by
 constructor <;> norm_num [sourceFace,QRH.Record1252270103Source.globalFace,countGlobal,
  QRH.Record1252270103Return.globalFace,countCB,countCL,countCap]

theorem source_restricts_physical : sourceFace.Restricts physicalGlobal := by
 constructor <;> norm_num [sourceFace,QRH.Record1252270103Source.globalFace,physicalGlobal,
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

theorem beta_le_theta_of_source
    (hsrc : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99/100) (239/100) (1/10)) :
    HeckeZeroSupremum.beta ≤ (174797/200000 : ℝ) := by
  rw [← theta_value]
  by_cases hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · have hG : UniformUnitFaceSource sourceFace := hsrc hbeta
    exact beta_of_two_global_sources (uniform_restrict source_restricts_count hG)
      (uniform_restrict source_restricts_physical hG)
  · have ht : (51/100:ℝ) ≤ theta := by norm_num [theta,c]
    exact (not_le.mp hbeta).le.trans ht

/-- The Dirichlet transfer of `beta_le_theta_of_source` (as PR76 `Graph.dirichlet_of_step`). -/
theorem dirichlet_of_source
    (hsrc : (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
      QRH.Record1252270103Source.GlobalSource (99/100) (239/100) (1/10))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174797 / 200000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num)
    (fun η s hs hpole => HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η
      ((beta_le_theta_of_source hsrc).trans_lt hs) hpole) χ s hs hpole

end
end QRH.DensitySplitThird.Return
