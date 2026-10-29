/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/fine_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
Two full source providers remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.CountWindow
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission01
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission02
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission03
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission04
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission05
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission06
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission07
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission08
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission09
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission10
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission11
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission12
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission13
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission14
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission15
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission16
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission17
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission18
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission19
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission20
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission21
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission22
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission23
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission24
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission25
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission26
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission27
import Candidate.Local.Qrh.JointDetector.FineReturn.Rows.Admission28
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FineReturn
open QRH.Record1252270103Return
noncomputable section

def returnWindow01 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (9/32:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission01_all

def returnWindow02 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (9/32:ℝ)
 deltaHi := (21/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission02_all

def returnWindow03 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission03_all

def returnWindow04 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission04_all

def returnWindow05 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission05_all

def returnWindow06 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission06_all

def returnWindow07 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission07_all

def returnWindow08 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission08_all

def returnWindow09 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission09_all

def returnWindow10 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission10_all

def returnWindow11 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (453/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission11_all

def returnWindow12 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (453/1024:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission12_all

def returnWindow13 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission13_all

def returnWindow14 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission14_all

def returnWindow15 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission15_all

def returnWindow16 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (21/64:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission16_all

def returnWindow17 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission17_all

def returnWindow18 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission18_all

def returnWindow19 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission19_all

def returnWindow20 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission20_all

def returnWindow21 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission21_all

def returnWindow22 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission22_all

def returnWindow23 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission23_all

def returnWindow24 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission24_all

def returnWindow25 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (453/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission25_all

def returnWindow26 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (453/1024:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission26_all

def returnWindow27 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission27_all

def returnWindow28 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission28_all
def returnWindows : List ReturnCountWindow := [returnWindow01,returnWindow02,returnWindow03,returnWindow04,returnWindow05,returnWindow06,returnWindow07,returnWindow08,returnWindow09,returnWindow10,returnWindow11,returnWindow12,returnWindow13,returnWindow14,returnWindow15,returnWindow16,returnWindow17,returnWindow18,returnWindow19,returnWindow20,returnWindow21,returnWindow22,returnWindow23,returnWindow24,returnWindow25,returnWindow26,returnWindow27,returnWindow28]

end
end Qrh.JointDetector.FineReturn
