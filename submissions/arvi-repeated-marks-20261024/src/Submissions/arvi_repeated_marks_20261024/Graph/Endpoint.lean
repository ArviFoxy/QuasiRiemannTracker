/- Repeated marks: the endpoint from the source steps.
Fork of Collet's Record1252270103Graph/FinalSources.lean and Graph/Endpoint.lean (Apache-2.0):
the final count face is node 58 and the final physical face is node 31 of the repeated-mark graph;
the seed step, the intermediate stage and the natural premise are Collet's, unchanged. -/
import Submissions.arvi_repeated_marks_20261024.Graph.Chain
import Submissions.arvi_repeated_marks_20261024.FinalReturn.EndpointFromGlobalSources
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Graph QRH.RepeatedMarks.Finite QRH.Record12518109Existence

lemma final_C_face :
    Record1252270103Source.globalFace (node58.B:ℝ) (node58.L:ℝ) (node58.cap:ℝ)=
      QRH.RepeatedMarks.Return.countGlobal := by
  norm_num [Record1252270103Source.globalFace,node58,QRH.RepeatedMarks.Return.countGlobal,
    QRH.Record1252270103Return.globalFace,QRH.RepeatedMarks.Return.countCB,
    QRH.RepeatedMarks.Return.countCL]

lemma final_P_face :
    Record1252270103Source.globalFace (node52.B:ℝ) (node52.L:ℝ) (node52.cap:ℝ)=
      QRH.RepeatedMarks.Return.physicalGlobal := by
  norm_num [Record1252270103Source.globalFace,node52,QRH.RepeatedMarks.Return.physicalGlobal,
    QRH.Record1252270103Return.globalFace,QRH.RepeatedMarks.Return.physicalB,
    QRH.RepeatedMarks.Return.physicalLambda]

theorem final_global_suppliers (seed : SeedStep) (step : NFStep2)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    UniformUnitFaceSource QRH.RepeatedMarks.Return.countGlobal ∧
    UniformUnitFaceSource QRH.RepeatedMarks.Return.physicalGlobal := by
  obtain ⟨hC,hP⟩ := chain_sources step hbeta (final_natural_cap seed hbeta)
  change UniformUnitFaceSource _ at hC hP
  rw [final_C_face] at hC
  rw [final_P_face] at hP
  exact ⟨hC,hP⟩

theorem beta_of_steps (seed : SeedStep) (step : NFStep2) :
    HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta := by
  by_cases hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta
  · obtain ⟨hC29C,hC29P⟩ := seed_global_suppliers seed hbeta
    obtain ⟨hC,hP⟩ := final_global_suppliers seed step hbeta
    exact QRH.RepeatedMarks.Return.beta_of_four_global_sources hC29C hC29P hC hP
  · have ht : (51/100:ℝ)≤QRH.RepeatedMarks.Return.theta := by
      norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c]
    exact (not_le.mp hbeta).le.trans ht

theorem dirichlet_of_steps (seed : SeedStep) (step : NFStep2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : QRH.RepeatedMarks.Return.theta<s.re) (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke
    (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
    (fun χ s hs hpole=>HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
      ((beta_of_steps seed step).trans_lt hs) hpole) χ s hs hpole

end
end QRH.RepeatedMarks.Graph
