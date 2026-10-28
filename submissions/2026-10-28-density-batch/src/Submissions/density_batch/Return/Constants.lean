/- Four-step research batch; theta = 436972583/500000000.
AI-assisted by OpenAI Codex; conditional on the preprint 7/8 theorem.
Constants use the inherited Sil/Collet/ArviFoxy/Sussman return formulas (Apache-2.0). -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace QRH.DensityBatch.Return
noncomputable section
def c : ℝ := (63027417/500000000:ℝ)
def h : ℝ := (402563361/500000000:ℝ)
def physicalB : ℝ := (6195261783/6250000000:ℝ)
def physicalLambda : ℝ := (2379/1000:ℝ)
def physicalCap : ℝ := (31/500:ℝ)
def countCB : ℝ := (97697347983/100000000000:ℝ)
def countCL : ℝ := (4370501/2000000:ℝ)
def countCap : ℝ := (9999/100000:ℝ)
def naturalK : ℝ := (9/2:ℝ)
/-- The natural tail slope floor `s_minus` and the plain floor `m_minus` of the count windows. -/
def sMinus : ℝ := (3/100:ℝ)
def mMinus : ℝ := (377/1000:ℝ)
def theta : ℝ := 1-c
def ell : ℝ := 4*c-1/3
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappa : ℝ := 1-2*c
/-- The physical marked cap actually used, `s_P = 3/50`. -/
def numeratorCap : ℝ := (3/50:ℝ)
/-- The fixed switch `d_m = 19/25` (not the capacity join). -/
def dm : ℝ := (19/25:ℝ)
def dp : ℝ := h+1/10000000000
def d0 : ℝ := 1/200
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)
/-- The certificate reserve (`reserve` in hybrid-0873995-certificate.json). -/
def reserve : ℝ := 1/100000000
inductive Edge | oldSmall | oldSwitch | newSwitch | newTop
 deriving DecidableEq
def edgeD : Edge → ℝ
 | .oldSmall => d0
 | .oldSwitch | .newSwitch => dm
 | .newTop => dp
def edgeC (e : Edge) : ℝ := match e with
 | .oldSmall | .oldSwitch => oldCapacity (edgeD e)
 | .newSwitch | .newTop => newCapacity (edgeD e)
theorem c_value : c = (63027417/500000000:ℝ) := rfl
theorem theta_value : theta = (436972583/500000000:ℝ) := by norm_num [theta,c]
theorem h_value : h = (402563361/500000000:ℝ) := rfl
theorem ell_value : ell = (64082251/375000000:ℝ) := by norm_num [ell,c]
theorem x_value : x = (548638921/1500000000:ℝ) := by norm_num [x,ell,c,h]
theorem y_value : y = (27801283/60000000:ℝ) := by norm_num [y,ell,c,h]
theorem kappa_value : kappa = (186972583/250000000:ℝ) := by norm_num [kappa,c]
theorem dp_value : dp = (8051267221/10000000000:ℝ) := by norm_num [dp,h]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,d0]
theorem edgeC_oldSmall : edgeC .oldSmall = (625000/560917749:ℝ) := by
 norm_num [edgeC,edgeD,oldCapacity,d0,y,ell,c,h,kappa]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (19/25:ℝ) := by norm_num [edgeD,dm]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (2551675/68683806:ℝ) := by
 norm_num [edgeC,edgeD,oldCapacity,dm,y,ell,c,h,kappa]
theorem edgeD_newSwitch : edgeD .newSwitch = (19/25:ℝ) := by norm_num [edgeD,dm]
theorem edgeC_newSwitch : edgeC .newSwitch = (57/1250:ℝ) := by
 norm_num [edgeC,edgeD,newCapacity,dm,y,ell,c,h,numeratorCap,physicalB,physicalLambda]
theorem edgeD_newTop : edgeD .newTop = (8051267221/10000000000:ℝ) := by norm_num [edgeD,dp,h]
theorem edgeC_newTop : edgeC .newTop = (21474622319445745129/446062500000000000000:ℝ) := by
 norm_num [edgeC,edgeD,newCapacity,dp,y,ell,c,h,numeratorCap,physicalB,physicalLambda]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
end
end QRH.DensityBatch.Return
