/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
set_option autoImplicit false
namespace QRH.RepeatedMarks.Return
noncomputable section
def c : ℝ := (125251/1000000:ℝ)
def h : ℝ := (799/1000:ℝ)
def physicalB : ℝ := (9808361219421/10000000000000:ℝ)
def physicalLambda : ℝ := (8971213120859/2500000000000:ℝ)
def countCB : ℝ := (1912184686337/2000000000000:ℝ)
def countCL : ℝ := (14483089485293/5000000000000:ℝ)
def naturalK : ℝ := (11243277/2500000:ℝ)
def theta : ℝ := 1-c
def ell : ℝ := 4*c-1/3
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 1-2*c
def ds : ℝ := 2*y/(1+6*kappa/25)
def dk : ℝ := 2*y/(2-physicalB+physicalLambda/25)
def dp : ℝ := h+1/10000000000
def d0 : ℝ := 1/200
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (d/25) ((2*y-(2-physicalB)*d)/physicalLambda)
def rowFee : ℝ := 1/1000000000
inductive Edge | oldSmall | oldPeak | oldSwitch | newSwitch | newTop | newKink
 deriving DecidableEq
def edgeD : Edge → ℝ
 | .oldSmall => d0
 | .oldPeak => y
 | .oldSwitch | .newSwitch => ds
 | .newTop => dp
 | .newKink => dk
def edgeC (e : Edge) : ℝ := match e with
 | .oldSmall | .oldPeak | .oldSwitch => oldCapacity (edgeD e)
 | .newSwitch | .newTop | .newKink => newCapacity (edgeD e)
theorem c_value : c = (125251/1000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem theta_value : theta = (874749/1000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem h_value : h = (799/1000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem ell_value : ell = (125753/750000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem x_value : x = (276503/750000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem y_value : y = (21734/46875:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem kappa_value : kappa = (374749/500000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem ds_value : ds = (17387200/22122741:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem dk_value : dk = (695488000000000/872027465993733:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem dp_value : dp = (7990000001/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem d0_value : d0 = (1/200:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldSmall : edgeC .oldSmall = (1250/1124247:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldPeak : edgeD .oldPeak = (21734/46875:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldPeak : edgeC .oldPeak = (347744/3372741:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (17387200/22122741:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (695488/22122741:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newSwitch : edgeD .newSwitch = (17387200/22122741:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newSwitch : edgeC .newSwitch = (695488/22122741:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newTop : edgeD .newTop = (7990000001/10000000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newTop : edgeC .newTop = (33901618398946453658263/1076545574503080000000000:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeD_newKink : edgeD .newKink = (695488000000000/872027465993733:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem edgeC_newKink : edgeC .newKink = (27819520000000/872027465993733:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee]
theorem capacity_join : oldCapacity ds = newCapacity ds ∧ newCapacity ds = ds/25 := by
 norm_num [oldCapacity,newCapacity,ds,y,ell,c,kappa,physicalB,physicalLambda,h]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
end
end QRH.RepeatedMarks.Return
