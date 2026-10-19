/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedGain

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem rescaled_power_padded
    (U Y D Dmax pad d q S loss : ℝ)
    (hU : 1≤ U) (hY : 0<Y) (hD : 0<D) (hDmax : D≤ Dmax)
    (hd0 : 0≤ d) (hd : d<5/6)
    (hbase : U^D=Y*U^pad) (hloss : 0≤ loss) :
    (U^D)^(fullCount d (S/D)+q*(S/D)+loss) ≤
      U^(q*S-physicalGain d S D+Dmax*loss+pad*rho d)*Y^(rho d) := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hYeq : Y=U^(D-pad) := by
    rw [Real.rpow_sub hUp]
    apply (eq_div_iff (Real.rpow_pos_of_pos hUp pad).ne').mpr
    exact hbase.symm
  have hgain := physicalGain_rescale (S:=S) hd0 hd hD
  have hexp : D*(fullCount d (S/D)+q*(S/D)+loss)=
      q*S-physicalGain d S D+D*loss+D*rho d := by
    have hcancel : D*(S/D)=S := mul_div_cancel₀ _ hD.ne'
    linear_combination q*hcancel-hgain
  rw [←Real.rpow_mul hUp.le,hexp,hYeq,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_right hDmax hloss
  linarith

theorem root_power_transport {d U Y D q pad S A r loss : ℝ}
    (hd0 : 31/50≤ d) (hd : d≤3/4) (hU : 1≤ U) (hY : 1≤ Y)
    (hD : 0≤ D) (hq : q≤1) (hpad : 0≤ pad) (hloss : 0≤ loss)
    (hbase : Y=U^(D*q)) :
    U^(A-physicalGain d S (D*q+pad))*Y^r ≤
      U^(A+(3/200)*D-physicalGain d S D)*Y^(r+loss-3/200) := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hg := physicalGain_root (S:=S) hd0 hd hD hq hpad
  calc
    _ ≤ U^(A-physicalGain d S (D*q+pad))*Y^(r+loss) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by positivity)
    _ ≤ _ := by
      rw [hbase,←Real.rpow_mul hUp.le,←Real.rpow_mul hUp.le,
        ←Real.rpow_add hUp,←Real.rpow_add hUp]
      apply Real.rpow_le_rpow_of_exponent_le hU
      nlinarith only [hg]

theorem exception_envelope {d U Y D S A r : ℝ}
    (hd0 : 31/50≤ d) (hd : d≤3/4) (hU : 1≤ U) (hY : 1≤ Y)
    (hD : 0≤ D) (hr : 3/200≤ r) :
    U^A ≤ U^(A+(3/200)*D-physicalGain d S D)*Y^(r-3/200) := by
  have hg := physicalGain_le_cap (S:=S) hd0 hd hD
  calc
    _ ≤ U^(A+(3/200)*D-physicalGain d S D) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hY (by linarith))

end Sil.Uneven.Saturated
#print axioms Sil.Uneven.Saturated.rescaled_power_padded
#print axioms Sil.Uneven.Saturated.root_power_transport
#print axioms Sil.Uneven.Saturated.exception_envelope
