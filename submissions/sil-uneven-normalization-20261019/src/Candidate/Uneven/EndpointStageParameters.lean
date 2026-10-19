/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountWindows
import Candidate.Uneven.WarmupPhysicalGuards
import Candidate.Uneven.RoundedPhysicalGuards

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.UnevenEndpoint
noncomputable section

/-- This configuration contains only a finite stage, never an analytic premise. -/
class Configuration where
  stage : MainCount.Stage

inductive SourcePlane where
  | A | C
  deriving DecidableEq

instance : Fintype SourcePlane := ⟨{.A,.C}, by intro P; cases P <;> simp⟩

variable [config : Configuration]

def theta : ℝ := match config.stage with
  | .warmup => Sil.Uneven.WarmupRows.theta
  | .final => Sil.Uneven.RoundedRows.theta
def h : ℝ := match config.stage with
  | .warmup => Sil.Uneven.WarmupRows.h
  | .final => Sil.Uneven.RoundedRows.h
def incumbent : ℝ := match config.stage with
  | .warmup => 87483/100000
  | .final => 4374143/5000000
def upperPadding : ℝ := match config.stage with
  | .warmup => 1/10000000000
  | .final => 1/10000000000000000
def reserve : ℝ := match config.stage with
  | .warmup => 1/10000000
  | .final => 1/20000000000000

def ell : ℝ := 11/3-4*theta
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def dMinus : ℝ := h-3/2000
def dPlus : ℝ := h+upperPadding
def frozenKappa : ℝ := 2*incumbent-1
def kappaStar : ℝ := 2*theta-1
def kappa0 : ℝ := 93709/125000
def plainKappa : ℝ := 3/4
def slotClip : ℝ := 399999/10000000
def physicalSwitch : ℝ := 3/2000
def plainLower : ℝ := 81/200
def plainUpper : ℝ := 45/100
def widthLower : ℝ := 17/500
def widthUpper : ℝ := 1/25
def countBuffer : ℝ := reserve/1000
def countLoss : ℝ := reserve/100
def effectiveReserve : ℝ := 99*reserve/100

namespace SourcePlane
def mainPlane (P : SourcePlane) : Sil.Uneven.MainSource.Plane :=
  match config.stage,P with
  | .warmup,.A => .A2 | .warmup,.C => .C2
  | .final,.A => .A | .final,.C => .C
def B (P : SourcePlane) : ℝ := P.mainPlane.B
def lambda (P : SourcePlane) : ℝ := P.mainPlane.lambda

theorem mainPlane_incumbent (P : SourcePlane) :
    P.mainPlane.incumbent=frozenKappa := by
  cases config with
  | mk stage => cases stage <;> cases P <;>
      norm_num [mainPlane,frozenKappa,incumbent,Sil.Uneven.MainSource.Plane.incumbent]
end SourcePlane

theorem parameter_gates :
    (874/1000:ℝ) < theta ∧ theta < incumbent ∧ incumbent ≤ 7/8 ∧
    1/6 < ell ∧ ell < 1/5 ∧ 1/2 < dMinus ∧ dMinus < dPlus ∧ dPlus < 1 ∧
    0 < y ∧ y < 1/2 ∧ dPlus < 2*y ∧
    7/10 < frozenKappa ∧ frozenKappa ≤ kappa0 ∧
    0 < reserve ∧ 0 < countBuffer ∧ 0 < effectiveReserve := by
  cases config with
  | mk stage => cases stage <;>
      norm_num [theta,h,incumbent,ell,y,dMinus,dPlus,upperPadding,frozenKappa,kappa0,
        reserve,countBuffer,effectiveReserve,
        Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,
        Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h]

theorem count_loss_reserve {z loss : ℝ} (hz : 0 ≤ z) (hzhi : z ≤ 1)
    (hl : loss ≤ countLoss) : 3*z*loss/4 ≤ reserve-effectiveReserve := by
  have hr : 0 < reserve := parameter_gates.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh := mul_le_mul_of_nonneg_left hl hz
  unfold countLoss effectiveReserve at *
  nlinarith [mul_le_mul_of_nonneg_right hzhi hr.le]

end
end OAI.SevenEighths.UnevenEndpoint
#print axioms OAI.SevenEighths.UnevenEndpoint.parameter_gates
#print axioms OAI.SevenEighths.UnevenEndpoint.SourcePlane.mainPlane_incumbent
#print axioms OAI.SevenEighths.UnevenEndpoint.count_loss_reserve
