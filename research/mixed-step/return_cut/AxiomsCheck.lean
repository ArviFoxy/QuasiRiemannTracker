/- Check of the regenerated final return (package arvi_mixed_step_20261026): the top theorem, its
axioms, and the constants it is instantiated with. Compile from the Lake project (REGENERATE.md):
  lake env lean /home/user/QuasiRiemannTracker/research/mixed-step/return_cut/AxiomsCheck.lean -/
import Submissions.arvi_mixed_step_20261026.FinalReturn.EndpointFromGlobalSources
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
example : QRH.RepeatedMarks.Return.numeratorCap = 29/500 := rfl
example : QRH.RepeatedMarks.Return.GenericArithmetic.cap = 29/500 := rfl
example : countGlobal = QRH.Record1252270103Return.globalFace countCB countCL (3/40) := rfl
example : physicalGlobal = QRH.Record1252270103Return.globalFace physicalB physicalLambda (3/40) := rfl
example (j : ℕ) : countWindow j = ⟨countCB-j/4000,countCL,2/5,11/25,17/500,29/500⟩ := rfl
example : branchCap .C = 29/500 ∧ branchCap .capC = 29/500 := ⟨rfl, rfl⟩
example : countCB = 517574273064321753867031/536870912000000000000000 := rfl
example : countCL = 563952501813603236449/268435456000000000000 := rfl
example : physicalB = 51846496626077474773381/53687091200000000000000 := rfl
example : physicalLambda = 114318071421667363757/53687091200000000000 := rfl
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
