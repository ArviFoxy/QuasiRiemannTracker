/- Mixed source step, L2 transfer: new in this submission; uses Collet's and the baseline's definitions by import.

Small interface facts about the residual input.

* `residualInputAt s J η t`: the residual input carrying the Hecke character
  `η` (e.g. `childCharacter τ ξ`) and height `t`, as consumed by Collet's
  second transform (`Γ = rowWeight s.η … 1 1 s.t`). Its tuple and column
  coefficients are literally those of `residualInput s J`.
* `sourceRadius_residual`: the residual source radius times the selected
  window `∏_J hi_j P_j` is the original source radius. -/
import Submissions.arvi_mixed_step.Transfer.Split

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic QRH.Record1252270103Source.High
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residual input with a prescribed Hecke character and height. -/
def residualInputAt (s : Input ι) (J : Finset ι) (η : HeckeFamily.Character) (t : ℝ) :
    Input {i // i ∉ J} :=
  { residualInput s J with η := η, t := t }

@[simp] theorem residualInputAt_η (s : Input ι) (J : Finset ι) (η : HeckeFamily.Character)
    (t : ℝ) : (residualInputAt s J η t).η = η := rfl

@[simp] theorem residualInputAt_t (s : Input ι) (J : Finset ι) (η : HeckeFamily.Character)
    (t : ℝ) : (residualInputAt s J η t).t = t := rfl

theorem residualInputAt_pools (s : Input ι) (J : Finset ι) (η : HeckeFamily.Character) (t : ℝ) :
    (residualInputAt s J η t).pools = (residualInput s J).pools := rfl

theorem tupleCoefficient_residualInputAt (s : Input ι) (J : Finset ι)
    (η : HeckeFamily.Character) (t : ℝ) (modifier : Tuple {i // i ∉ J} → ℂ) (R L : Ideal O) :
    CoupledFirst.tupleCoefficient (residualInputAt s J η t) modifier R L =
      CoupledFirst.tupleCoefficient (residualInput s J) modifier R L := rfl

theorem coefficient_residualInputAt (s : Input ι) (J : Finset ι)
    (η : HeckeFamily.Character) (t : ℝ) (modifier : Tuple {i // i ∉ J} → ℂ) (R L : Ideal O) :
    CoupledFirst.coefficient (residualInputAt s J η t) modifier R L =
      CoupledFirst.coefficient (residualInput s J) modifier R L := rfl

/-- The source radius splits along the selected block. -/
theorem sourceRadius_residual (s : Input ι) (J : Finset ι) :
    sourceRadius (residualInput s J) * ∏ j ∈ J, s.hi j * s.P j = sourceRadius s := by
  unfold sourceRadius
  have hhi : (∏ i, s.hi i) = (∏ j ∈ J, s.hi j) * ∏ i : {i // i ∉ J}, s.hi i.val := by
    rw [prod_split J s.hi, Finset.prod_coe_sort J s.hi]
  have hP : (∏ i, s.P i) = (∏ j ∈ J, s.P j) * ∏ i : {i // i ∉ J}, s.P i.val := by
    rw [prod_split J s.P, Finset.prod_coe_sort J s.P]
  rw [hhi, hP, Finset.prod_mul_distrib]
  change (∏ i : {i // i ∉ J}, s.hi i.val) * s.b₁ * s.b₂ * (s.X₁ * s.X₂) *
      (∏ i : {i // i ∉ J}, s.P i.val) * ((∏ j ∈ J, s.hi j) * ∏ j ∈ J, s.P j) = _
  ring

end
end QRH.MixedStep.Transfer
