/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Core.InitialMainRemainderGap
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: the actual downward affine
source budget pays the six MAIN enlargement powers before any slot count; positive raw scales below
one remain allowed.

The MAIN remainder gap at the mixed amplifier. Collet's gap `A + 6a + 3e ≤ 1` comes from
`RealGeometry.parent_budget_room` (`T + 4e < B₀·F`, `F = 1 - 6a`). The mixed step's first layer has
the scale `F' = 1 - 6r - 6d = 1 - 6·Amix` (`MixedGeometry.parent_budget_room` with `sourceF3Real`),
so the gap holds with `Amix = r + d` in place of `a`: `A + 6·Amix + 3e ≤ 1`. The scale enters as a
real `F` with `0 ≤ F` and `F + 6·Amix ≤ 1` (equality for `F = sourceF3Real`, positivity from
`MixedGeometry.amp_small`). This pays the zero term's `+4δ` (design `L45_DESIGN.md` §3 F6): the
residual MAIN radius at `(volume s₀.restrict J, 3(a+δ))` costs `4(amp - a) + 2κ ≤ 6(Amix - a)`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialMainRemainderGap

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open Record1252270103Finite Record1252270103StepScalar

/-- The mixed node gap: the first-layer budget at the mixed scale `F` pays six mixed amplifiers. -/
theorem node_amplification_gap_mx (n low : Source) (b width A D Amix F : ℝ)
    (hroom : sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*F)
    (hF0 : 0≤F) (hFA : F+6*Amix≤1)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ)) (hB : (low.B:ℝ)≤1) (hD : 0≤D)
    (hw : width≤PhysicalLowGuard.step n)
    (hA : A≤D*(sourceTReal n b+b+(n.L:ℝ)*width)) :
    A+6*(D*Amix)+3*D*(n.allowance:ℝ)≤D := by
  have hstep : 0≤PhysicalLowGuard.step n:=by
    dsimp only [PhysicalLowGuard.step]
    positivity
  have hwidth := PhysicalLowGuard.step_budget n he hL width 0 0 0 0 hw hstep hstep hstep hstep
  simp only [add_zero,mul_zero] at hwidth
  have hB' := mul_le_mul_of_nonneg_right hB hF0
  have hnode : sourceTReal n b+b+(n.L:ℝ)*width+6*Amix+3*(n.allowance:ℝ)≤1 := by
    linarith only [hroom,hB',hwidth,hFA]
  have hh:=mul_le_mul_of_nonneg_left hnode hD
  nlinarith only [hh,hA]

section Initial
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal HeckeFamily.O) [NeZero rayM]
local instance initialMainGapFiniteQuotient_mx : Finite (HeckeFamily.O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (HeckeFamily.O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal HeckeFamily.O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

/-- Actual initial volume, actual source face and actual width cell give the mixed gap. -/
theorem initial_main_amplification_gap_mx (n low : Source) (b width Amix F : ℝ)
    (hZ1 : 1<Z)
    (hroom : sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*F)
    (hF0 : 0≤F) (hFA : F+6*Amix≤1)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ)) (hB : (low.B:ℝ)≤1)
    (hw : width≤PhysicalLowGuard.step n)
    (hadm : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hlo : b-(n.allowance:ℝ)-width≤∑i,w i) (hhi : (∑i,w i)≤b) :
    Real.logb Z (volume (s))+6*Amix+3*(n.allowance:ℝ)≤1 := by
  have hv:=initial_log_volume_node_bound rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
    p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod n b width hZ1 hL hadm hlo hhi
  simpa only [one_mul,mul_one] using node_amplification_gap_mx n low b width
    (Real.logb Z (volume (s))) 1 Amix F hroom hF0 hFA he hL hB (by norm_num) hw (by simpa using hv)
end Initial
end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.node_amplification_gap_mx
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_main_amplification_gap_mx
