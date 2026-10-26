/- The mixed-step proof: the endpoint from the mixed source step.

Fork of PR 76's `Graph/Endpoint.lean` (itself a fork of Collet's Record1252270103Graph/FinalSources
and Graph/Endpoint). The chain starts at Sil's fourth-power source face, runs through the
fan and the mixed face family (`Graph/MixedChain.lean`), and ends at the count face `faceC` and the
physical face `faceP`. The final return is `Submissions.arvi_mixed_step_20261026` (single stage,
`dMinus > 1/2`, `θ = 34971/40000`). -/
import Submissions.arvi_mixed_step.Graph.MixedChain
import Submissions.arvi_mixed_step_20261026.FinalReturn.EndpointFromGlobalSources
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Graph QRH.RepeatedMarks.Finite QRH.Record12518109Existence

lemma final_C_face3 :
    Record1252270103Source.globalFace (faceC.B:ℝ) (faceC.L:ℝ) (faceC.cap:ℝ)=
      QRH.RepeatedMarks.Return.countGlobal := by
  rw [faceC_B, faceC_L, faceC_cap]
  norm_num [Record1252270103Source.globalFace,QRH.RepeatedMarks.Return.countGlobal,
    QRH.Record1252270103Return.globalFace,QRH.RepeatedMarks.Return.countCB,
    QRH.RepeatedMarks.Return.countCL]

lemma final_P_face3 :
    Record1252270103Source.globalFace (faceP.B:ℝ) (faceP.L:ℝ) (faceP.cap:ℝ)=
      QRH.RepeatedMarks.Return.physicalGlobal := by
  rw [faceP_B, faceP_L, faceP_cap]
  norm_num [Record1252270103Source.globalFace,QRH.RepeatedMarks.Return.physicalGlobal,
    QRH.Record1252270103Return.globalFace,QRH.RepeatedMarks.Return.physicalB,
    QRH.RepeatedMarks.Return.physicalLambda]

theorem final_global_suppliers3 (step : NFStep3)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    UniformUnitFaceSource QRH.RepeatedMarks.Return.countGlobal ∧
    UniformUnitFaceSource QRH.RepeatedMarks.Return.physicalGlobal := by
  obtain ⟨hC,hP⟩ := mixed_chain_sources step hbeta QRH.RepeatedMarks.natural_cap
  change UniformUnitFaceSource _ at hC hP
  rw [final_C_face3] at hC
  rw [final_P_face3] at hP
  exact ⟨hC,hP⟩

theorem beta_of_step3 (step : NFStep3) :
    HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta := by
  by_cases hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta
  · obtain ⟨hC,hP⟩ := final_global_suppliers3 step hbeta
    exact QRH.RepeatedMarks.Return.beta_of_two_global_sources hC hP
  · have ht : (51/100:ℝ)≤QRH.RepeatedMarks.Return.theta := by
      norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c]
    exact (not_le.mp hbeta).le.trans ht

theorem dirichlet_of_step3 (step : NFStep3)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : QRH.RepeatedMarks.Return.theta<s.re) (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke
    (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
    (fun χ s hs hpole=>HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
      ((beta_of_step3 step).trans_lt hs) hpole) χ s hs hpole

end
end QRH.MixedStep.Graph
