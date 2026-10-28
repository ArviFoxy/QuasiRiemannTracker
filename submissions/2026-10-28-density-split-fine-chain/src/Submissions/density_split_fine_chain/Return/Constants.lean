/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/
/- Modified by Sil (2026-10-26): constants of the return at theta = 174799/200000 (h = 8053/10000,
count face C = (4967/5000, 49/20, 9999/100000), physical face P = (9933999/10^7, 2451/1000, 31/500),
physical slot cap 3/50, fixed switch dm = 19/25, natural tail s_minus = 3/100, m_minus = 19/50,
certificate reserve 1/10^8); only the four conductor edges used by the Lean return are kept. -/
/- Modified for the 46-step density-split chain (27 Oct 2026): constants of the return at theta = 4369779/5000000 (h = 8051/10000, count face C = (9888151/10000000, 4683001/2000000, 9999/100000), physical face P = (9888151/10000000, 4683001/2000000, 31/500), m_minus = 377/1000); every other constant, the windows and the layout are Sil's. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace QRH.SilDensitySplit.Return
noncomputable section
def c : ℝ := (630221/5000000:ℝ)
def h : ℝ := (8051/10000:ℝ)
def physicalB : ℝ := (9888151/10000000:ℝ)
def physicalLambda : ℝ := (4683001/2000000:ℝ)
def physicalCap : ℝ := (31/500:ℝ)
def countCB : ℝ := (9888151/10000000:ℝ)
def countCL : ℝ := (4683001/2000000:ℝ)
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
theorem c_value : c = (630221/5000000:ℝ) := rfl
theorem theta_value : theta = (4369779/5000000:ℝ) := by norm_num [theta,c]
theorem h_value : h = (8051/10000:ℝ) := rfl
theorem ell_value : ell = (640663/3750000:ℝ) := by norm_num [ell,c]
theorem x_value : x = (685769/1875000:ℝ) := by norm_num [x,ell,c,h]
theorem y_value : y = (1737799/3750000:ℝ) := by norm_num [y,ell,c,h]
theorem kappa_value : kappa = (1869779/2500000:ℝ) := by norm_num [kappa,c]
theorem dp_value : dp = (8051000001/10000000000:ℝ) := by norm_num [dp,h]
theorem edgeD_oldSmall : edgeD .oldSmall = (1/200:ℝ) := by norm_num [edgeD,d0]
theorem edgeC_oldSmall : edgeC .oldSmall = (6250/5609337:ℝ) := by
 norm_num [edgeC,edgeD,oldCapacity,d0,y,ell,c,h,kappa]
theorem edgeD_oldSwitch : edgeD .oldSwitch = (19/25:ℝ) := by norm_num [edgeD,dm]
theorem edgeC_oldSwitch : edgeC .oldSwitch = (625598/16828011:ℝ) := by
 norm_num [edgeC,edgeD,oldCapacity,dm,y,ell,c,h,kappa]
theorem edgeD_newSwitch : edgeD .newSwitch = (19/25:ℝ) := by norm_num [edgeD,dm]
theorem edgeC_newSwitch : edgeC .newSwitch = (57/1250:ℝ) := by
 norm_num [edgeC,edgeD,newCapacity,dm,y,ell,c,h,numeratorCap,physicalB,physicalLambda]
theorem edgeD_newTop : edgeD .newTop = (8051000001/10000000000:ℝ) := by norm_num [edgeD,dp,h]
theorem edgeC_newTop : edgeC .newTop = (33816351072664453/702450150000000000:ℝ) := by
 norm_num [edgeC,edgeD,newCapacity,dp,y,ell,c,h,numeratorCap,physicalB,physicalLambda]
theorem geometry_mellin : theta-(4+y-x)/6 = x/2+(y-x)/12 := by
 norm_num [theta,x,y,ell,h,c]
end
end QRH.SilDensitySplit.Return
