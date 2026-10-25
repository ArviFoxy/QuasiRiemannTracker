/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
set_option autoImplicit false
namespace QRH.RepeatedMarks.Return
noncomputable section
def c : ℝ := (313187/2500000:ℝ)
def h : ℝ := (401/500:ℝ)
def physicalB : ℝ := (24135235200543153139938524804093/25122521280728268800000000000000:ℝ)
def physicalLambda : ℝ := (920014297669090958043/306671402352640000000:ℝ)
def countCB : ℝ := (1466689488397397859949977091/1533357011763200000000000000:ℝ)
def countCL : ℝ := (889034918041606397407/306671402352640000000:ℝ)
def naturalK : ℝ := (9/2:ℝ)
def theta : ℝ := 1-c
def ell : ℝ := 4*c-1/3
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 1-2*c
def numeratorCap : ℝ := (9/200:ℝ)
def ds : ℝ := 2*y/(1+6*kappa*numeratorCap)
def dk : ℝ := 2*y/(2-physicalB+physicalLambda*numeratorCap)
def dp : ℝ := h+1/10000000000
def d0 : ℝ := 1/200
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)
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
theorem c_value : c = (313187/2500000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem theta_value : theta = (2186813/2500000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem h_value : h = (401/500:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem ell_value : ell = (314561/1875000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem x_value : x = (685811/1875000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem y_value : y = (218657/468750:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem kappa_value : kappa = (936813/1250000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem ds_value : ds = (349851200/450881853:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem dk_value : dk = (70313153736706573708820480000000/88504044203522164103373571187721:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem dp_value : dp = (8020000001/10000000000:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem d0_value : d0 = (1/200:ℝ) := by norm_num [c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_oldSmall : edgeC .oldSmall = (3125/2810439:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_oldPeak : edgeD .oldPeak = (218657/468750:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_oldPeak : edgeC .oldPeak = (874628/8431317:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (349851200/450881853:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (5247768/150293951:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_newSwitch : edgeD .newSwitch = (349851200/450881853:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_newSwitch : edgeC .newSwitch = (5247768/150293951:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_newTop : edgeD .newTop = (8020000001/10000000000:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_newTop : edgeC .newTop = (74929572185160284896385553406293154412279/2261027137951557938486476800000000000000000:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeD_newKink : edgeD .newKink = (70313153736706573708820480000000/88504044203522164103373571187721:ℝ) := by norm_num [edgeD,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem edgeC_newKink : edgeC .newKink = (1054697306050598605632307200000/29501348067840721367791190395907:ℝ) := by norm_num [edgeC,edgeD,oldCapacity,newCapacity,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap]
theorem capacity_join : oldCapacity ds = newCapacity ds ∧ newCapacity ds = numeratorCap*ds := by
 norm_num [oldCapacity,newCapacity,ds,y,ell,c,kappa,physicalB,physicalLambda,h,numeratorCap]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
end
end QRH.RepeatedMarks.Return
