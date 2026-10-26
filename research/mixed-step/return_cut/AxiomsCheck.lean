/- Check of the regenerated final return (package arvi_mixed_step_20261026): the top theorem, its
axioms, the constants it is instantiated with, and the interface for the source side. Compile from
the Lake project (REGENERATE.md):
  lake env lean /home/user/QuasiRiemannTracker/research/mixed-step/return_cut/AxiomsCheck.lean
The face constants below are those of ../faces_k92.json (Lean family, K = 9/2, mpiece7 node3). -/
import Submissions.arvi_mixed_step_20261026.FinalReturn.EndpointFromGlobalSources
import Submissions.hailey_collet_1252270103.Record1252270103Graph.GraphContract
set_option autoImplicit false
open QRH.RepeatedMarks.Return

-- the final return: two global sources and the natural cost give β ≤ θ
#check @QRH.RepeatedMarks.Return.Final.beta_of_global_sources
#print axioms QRH.RepeatedMarks.Return.Final.beta_of_global_sources
-- single stage: the natural cost from the baseline's β ≤ 7/8
#check @QRH.RepeatedMarks.Return.beta_of_two_global_sources
#print axioms QRH.RepeatedMarks.Return.beta_of_two_global_sources

-- the constants (each checked by the kernel)
example : QRH.RepeatedMarks.Return.theta = 34971/40000 := theta_value
example : QRH.RepeatedMarks.Return.h = 2011/2500 := rfl
example : QRH.RepeatedMarks.Return.naturalK = 9/2 := rfl
example : QRH.RepeatedMarks.Return.numeratorCap = 29/500 := rfl
example : QRH.RepeatedMarks.Return.GenericArithmetic.cap = 29/500 := rfl
example : countGlobal = QRH.Record1252270103Return.globalFace countCB countCL (3/40) := rfl
example : physicalGlobal = QRH.Record1252270103Return.globalFace physicalB physicalLambda (3/40) := rfl
example (j : ℕ) : countWindow j = ⟨countCB-j/4000,countCL,2/5,11/25,17/500,29/500⟩ := rfl
example : branchCap .C = 29/500 ∧ branchCap .capC = 29/500 := ⟨rfl, rfl⟩
example : countCB = 4553636084322336971646479/4724464025600000000000000 := rfl
example : countCL = 4954148591857540990249/2362232012800000000000 := rfl
example : physicalB = 74757332803822334159435159927/77405618595430400000000000000 := rfl
example : physicalLambda = 5033014753577776399373/2362232012800000000000 := rfl
#print QRH.RepeatedMarks.Return.theta
#print QRH.RepeatedMarks.Return.c
#print QRH.RepeatedMarks.Return.h
#print QRH.RepeatedMarks.Return.numeratorCap
#print QRH.RepeatedMarks.Return.countGlobal
#print QRH.RepeatedMarks.Return.physicalGlobal
#print QRH.RepeatedMarks.Return.countWindow
-- the relaxed schedule field (Relaxation 1) and the relaxed transport bounds (Relaxation 2)
#check @QRH.RepeatedMarks.Return.GenericArithmetic.PhysicalSchedule.dMinus_lower
#check @QRH.Record1252270103Return.Geometry.BoundsR.h_interval
#check @QRH.Record1252270103Return.Geometry.BoundsR.ly_coarse
#check @QRH.Record1252270103Return.Geometry.BoundsR.ell_interval

/-- The interface for the source side, as in PR 76's `Graph/Endpoint.lean`: Collet's graph predicate
`P s = GlobalSource s.B s.L s.cap` at two `Source` values with these exact `B`, `L`, `cap` (any `q`
and fees), for `β ≥ 51/100`, gives `β ≤ θ`. -/
theorem interface_beta (fC fP : Record1252270103Finite.Source)
    (hCB : fC.B = 4553636084322336971646479/4724464025600000000000000)
    (hCL : fC.L = 4954148591857540990249/2362232012800000000000) (hCc : fC.cap = 3/40)
    (hPB : fP.B = 74757332803822334159435159927/77405618595430400000000000000)
    (hPL : fP.L = 5033014753577776399373/2362232012800000000000) (hPc : fP.cap = 3/40)
    (hsrc : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta →
      QRH.Record1252270103Graph.P fC ∧ QRH.Record1252270103Graph.P fP) :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ QRH.RepeatedMarks.Return.theta := by
  by_cases hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta
  · obtain ⟨hC, hP⟩ := hsrc hβ
    have eC : QRH.Record1252270103Source.globalFace (fC.B:ℝ) (fC.L:ℝ) (fC.cap:ℝ) = countGlobal := by
      rw [hCB, hCL, hCc]
      norm_num [QRH.Record1252270103Source.globalFace, countGlobal,
        QRH.Record1252270103Return.globalFace, countCB, countCL]
    have eP : QRH.Record1252270103Source.globalFace (fP.B:ℝ) (fP.L:ℝ) (fP.cap:ℝ) = physicalGlobal := by
      rw [hPB, hPL, hPc]
      norm_num [QRH.Record1252270103Source.globalFace, physicalGlobal,
        QRH.Record1252270103Return.globalFace, physicalB, physicalLambda]
    change QRH.Record12518109Existence.UniformUnitFaceSource _ at hC hP
    rw [eC] at hC
    rw [eP] at hP
    exact beta_of_two_global_sources hC hP
  · have ht : (51/100:ℝ) ≤ QRH.RepeatedMarks.Return.theta := by
      norm_num [QRH.RepeatedMarks.Return.theta, QRH.RepeatedMarks.Return.c]
    exact (not_le.mp hβ).le.trans ht
#print axioms interface_beta
