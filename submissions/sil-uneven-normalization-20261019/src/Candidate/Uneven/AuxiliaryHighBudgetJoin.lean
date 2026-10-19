import Candidate.Uneven.AuxiliaryHighParameters
import Candidate.Target830.High.BalancedMass
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryCellGeometry
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.AuxiliaryAffineAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.AuxiliaryPhysical
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open CenteredMomentEnergyFirstAnnularAdmission

/-- One numerical coefficient works for every original-width cell. -/
theorem geometry_affine_main_amplifier_bound  (beta : ℝ)
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤beta ∧ beta≤Sil.Uneven.AuxiliarySource.widthHi) :
    let a:=Sil.Uneven.AuxiliarySource.amp beta
    0≤(amplifierCap 2 0 1+6*a)/(a/2) ∧
      (amplifierCap 2 0 1+6*a)/(a/2)≤2000000 := by
  intro a
  have hg:=Sil.Uneven.AuxiliarySource.scheduling_guards  hb
  have hlo : Sil.Uneven.AuxiliarySource.amplifierMinimum≤a:=hg.2.2.1
  have ha : 0<a:=lt_of_lt_of_le hg.2.1 hlo
  constructor
  · unfold amplifierCap; positivity
  · apply (div_le_iff₀ (show 0<a/2 by positivity)).mpr
    norm_num only [amplifierCap,max_eq_left (by norm_num : (0:ℝ)≤2)]
    norm_num [Sil.Uneven.AuxiliarySource.amplifierMinimum] at hlo
    linarith

/-- Fold the fixed amplifier coefficient after the prime average has
already been paid in both branches. There is no second prime factor. -/
theorem geometry_amplified_branch_join (main error Kmain Kerror control a : ℝ)
    (ha : 0≤a) (ha' : a≤2000000) (hKm : 0≤Kmain) (hc : 0≤control)
    (hm : main≤Kmain*control) (he : error≤Kerror*control) :
    a*main+error≤(2000000*Kmain+Kerror)*control := by
  have h₁:=mul_le_mul_of_nonneg_left hm ha
  have h₂:=mul_le_mul_of_nonneg_right ha' (mul_nonneg hKm hc)
  nlinarith

/-- Both orientations use the same E and reciprocal physical compensator.
The asymmetric fixed support constant is absorbed into E. -/
theorem geometry_physical_side_join (reflected : Bool) (C K control budget : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (hK : 0≤K) (hc : 0≤control)
    (hb : budget≤K*geometryHighFactor reflected C key*control) :
    let E:=K*(1+2*C^2)*control
    budget ≤ (if reflected then E/geometryDCompensator key
      else E*geometryDCompensator key) := by
  intro E
  have hh:=(geometryDCompensator_pos key).le
  cases reflected
  · simp only [geometryHighFactor,Bool.false_eq_true,ite_false] at hb ⊢
    dsimp only [E]
    nlinarith [mul_nonneg (mul_nonneg hK hc) hh]
  · simp only [geometryHighFactor,ite_true] at hb ⊢
    dsimp only [E]
    rw [div_eq_mul_inv]
    have hnonneg : 0≤K*C^2*control*(geometryDCompensator key)⁻¹ := by positivity
    nlinarith

end
end OAI.SevenEighths.AuxiliaryHigh
#print axioms OAI.SevenEighths.AuxiliaryHigh.geometry_affine_main_amplifier_bound
#print axioms OAI.SevenEighths.AuxiliaryHigh.geometry_amplified_branch_join
#print axioms OAI.SevenEighths.AuxiliaryHigh.geometry_physical_side_join
