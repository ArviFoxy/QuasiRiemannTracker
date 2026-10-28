/- Ten successive exact improvements; theta = 2731076077/3125000000.
Substantially AI-assisted by OpenAI Codex; conditional on the preprint 7/8 theorem.
Inherited Sil/Collet/ArviFoxy/Sussman return formulas and licenses retained. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace QRH.DensityTen.Return
noncomputable section
def c : ℝ := (393923923/3125000000:ℝ)
def h : ℝ := (8059999999/10000000000:ℝ)
def physicalB : ℝ := (396418568023/400000000000:ℝ)
def physicalLambda : ℝ := (9501/4000:ℝ)
def physicalCap : ℝ := (31/500:ℝ)
def countCB : ℝ := (9767125183289/10000000000000:ℝ)
def countCL : ℝ := (4364251/2000000:ℝ)
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
/-- The physical marked cap actually used, `s_P = 61/1000`. -/
def numeratorCap : ℝ := (61/1000:ℝ)
/-- The fixed switch `d_m = 19/25` (not the capacity join). -/
def dm : ℝ := (19/25:ℝ)
def dp : ℝ := h+1/10000000000
def d0 : ℝ := 1/200
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappa)
def newCapacity (d : ℝ) : ℝ := min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)
/-- The certificate reserve (`reserve` in hybrid-0873995-certificate.json). -/
def reserve : ℝ := (1/500000000:ℝ)
inductive Edge | oldSmall | oldSwitch | newSwitch | newTop
 deriving DecidableEq
def edgeD : Edge → ℝ
 | .oldSmall => d0
 | .oldSwitch | .newSwitch => dm
 | .newTop => dp
def edgeC (e : Edge) : ℝ := match e with
 | .oldSmall | .oldSwitch => oldCapacity (edgeD e)
 | .newSwitch | .newTop => newCapacity (edgeD e)
theorem c_value : c = (393923923/3125000000:ℝ) := rfl
theorem theta_value : theta = (2731076077/3125000000:ℝ) := by norm_num [theta,c]
theorem h_value : h = (8059999999/10000000000:ℝ) := rfl
theorem ell_value : ell = (400521769/2343750000:ℝ) := by norm_num [ell,c]
theorem x_value : x = (54733393231/150000000000:ℝ) := by norm_num [x,ell,c,h]
theorem y_value : y = (69633213553/150000000000:ℝ) := by norm_num [y,ell,c,h]
theorem kappa_value : kappa = (1168576077/1562500000:ℝ) := by norm_num [kappa,c]
theorem dp_value : dp = (403/500:ℝ) := by norm_num [dp,h]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,d0]
theorem edgeC_oldSmall : edgeC .oldSmall = (3906250/3505728231:ℝ) := by
 norm_num [edgeC,edgeD,oldCapacity,d0,y,ell,c,h,kappa]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (19/25:ℝ) := by norm_num [edgeD,dm]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (12633213553/336549910176:ℝ) := by
 norm_num [edgeC,edgeD,oldCapacity,dm,y,ell,c,h,kappa]
theorem edgeD_newSwitch : edgeD .newSwitch = (19/25:ℝ) := by norm_num [edgeD,dm]
theorem edgeC_newSwitch : edgeC .newSwitch = (1159/25000:ℝ) := by
 norm_num [edgeC,edgeD,newCapacity,dm,y,ell,c,h,numeratorCap,physicalB,physicalLambda]
theorem edgeD_newTop : edgeD .newTop = (403/500:ℝ) := by norm_num [edgeD,dp,h]
theorem edgeC_newTop : edgeC .newTop = (69135757163807/1425150000000000:ℝ) := by
 norm_num [edgeC,edgeD,newCapacity,dp,y,ell,c,h,numeratorCap,physicalB,physicalLambda]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
end
end QRH.DensityTen.Return
