/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/
import Candidate.Uneven.FineSchedule
import Candidate.Cycle63.Marked.GeometryRawGates
import Candidate.Uneven.SaturatedTail

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.SaturatedPlain
noncomputable section
open Marked830Plain Cycle63MarkedPlain
open Sil.Uneven.Saturated
open scoped BigOperators

theorem raw_fee (D S r mesh normfee heightfee : ℝ)
    (hD : D≤130) (hS : S≤1/25) (hr : r≤1)
    (hmesh : mesh≤ fineRawRate) (hnorm : normfee≤1/1000000000000)
    (hheight : heightfee≤1/1000000000000) :
    D*fineRawRate+2*fineRawBin*S+
      131*(402*fineRawRate+mesh+fineRawRate+fineRawRate)+fineRawPad*r+
      normfee+heightfee≤ fineHighRawFee := by
  norm_num [fineRawRate,fineRawBin,fineRawPad,fineHighRawFee] at *
  linarith

theorem raw_bound_paid (Z tau D S delta normfee C Q : ℝ) (I J : ℕ)
    (hZ : 1≤ Z) (htau : 0≤ tau) (hC : 0≤ C)
    (hD0 : 0≤ D) (hD : D≤130) (hS : S≤1/25)
    (hd0 : 31/50≤ delta) (hd : delta≤3/4)
    (hnorm : normfee≤1/1000000000000) (hheight : tau*(J:ℝ)≤1/1000000000000)
    (hbound : Q≤ C*(1+geometryRawHeight Z tau I)^J*
      Z^(D*(rho delta+fineRawRate)+(delta+2*fineRawBin)*S+
        131*(402*fineRawRate+fineRawMesh+fineRawRate+fineRawRate)+fineRawPad*rho delta-
        min (physicalGain delta S D)
          (D*(1/100)*(6*(rho delta+fineRawRate-3/200)-1-fineRawTail)))) :
    Z^normfee*Q≤(C*(1+2*Real.pi+6*(I+1:ℕ))^J)*
      Z^(D*rho delta+delta*S-physicalGain delta S D+fineHighRawFee) := by
  have hp : 0<Z := zero_lt_one.trans_le hZ
  have hr : rho delta≤1 := by
    unfold rho
    have hh : 0≤10*delta/(3*(5-2*delta)) := div_nonneg (by linarith) (by linarith)
    linarith
  have htail := tail_absorbs_gain (S:=S) hd0 hd hD0
    (show 0≤ fineRawRate by norm_num [fineRawRate])
    (show fineRawTail≤1/1000 by norm_num [fineRawTail])
  rw [min_eq_left htail] at hbound
  let E:=D*(rho delta+fineRawRate)+(delta+2*fineRawBin)*S+
    131*(402*fineRawRate+fineRawMesh+fineRawRate+fineRawRate)+fineRawPad*rho delta-
      physicalGain delta S D
  have hfee:=raw_fee D S (rho delta) fineRawMesh normfee (tau*(J:ℝ)) hD hS hr
    fine_raw_mesh_gates.2.2 hnorm hheight
  have he : E+normfee+tau*(J:ℝ)≤ D*rho delta+delta*S-physicalGain delta S D+fineHighRawFee := by
    dsimp only [E]
    nlinarith only [hfee]
  calc
    _ ≤ Z^normfee*(C*(1+geometryRawHeight Z tau I)^J*Z^E) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hp.le _)
    _ ≤ Z^normfee*(C*((1+2*Real.pi+6*(I+1:ℕ))^J*Z^(tau*(J:ℝ)))*Z^E) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      exact mul_le_mul_of_nonneg_left (geometry_raw_height_power hZ htau I J) hC
    _ = (C*(1+2*Real.pi+6*(I+1:ℕ))^J)*Z^(E+normfee+tau*(J:ℝ)) := by
      rw [Real.rpow_add hp,Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) (by positivity)

end
end OAI.SevenEighths.SaturatedPlain
#print axioms OAI.SevenEighths.SaturatedPlain.raw_bound_paid
