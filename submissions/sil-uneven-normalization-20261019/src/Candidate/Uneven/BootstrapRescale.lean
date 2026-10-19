/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/
import Candidate.Uneven.BootstrapCore

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem rescaled_power_padded
    (U Y D Dmax pad d q S loss : ℝ)
    (hU : 1 ≤ U) (hY : 0<Y) (hD : 0<D) (hDmax : D ≤ Dmax)
    (hbase : U^D=Y*U^pad) (hloss : 0 ≤ loss) :
    (U^D)^(count d (S/D)+q*(S/D)+loss) ≤
      U^(q*S-physicalGain d S D+Dmax*loss+pad*Saturated.rho d)*Y^(Saturated.rho d) := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hYeq : Y=U^(D-pad) := by
    rw [Real.rpow_sub hUp]
    apply (eq_div_iff (Real.rpow_pos_of_pos hUp pad).ne').mpr
    exact hbase.symm
  have hgain : D*physicalGain d (S/D) 1=physicalGain d S D := FiniteGain.gain_rescale hD
  have hexp : D*(count d (S/D)+q*(S/D)+loss)=
      q*S-physicalGain d S D+D*loss+D*Saturated.rho d := by
    have hcancel : D*(S/D)=S := mul_div_cancel₀ _ hD.ne'
    unfold count
    linear_combination q*hcancel-hgain
  rw [←Real.rpow_mul hUp.le,hexp,hYeq,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_right hDmax hloss
  linarith

theorem root_power_transport {d U Y D q pad S A r loss : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50) (hU : 1 ≤ U) (hY : 1 ≤ Y)
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq : q ≤ 1) (hpad : 0 ≤ pad) (hloss : 0 ≤ loss)
    (hbase : Y=U^(D*q)) :
    U^(A-physicalGain d S (D*q+pad))*Y^r ≤
      U^(A+(3/200)*D-physicalGain d S D)*Y^(r+loss-3/200) := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hg := physicalGain_root hd0 hd hS hD hq0 hq hpad
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
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50) (hU : 1 ≤ U) (hY : 1 ≤ Y)
    (hD : 0 ≤ D) (hr : 3/200 ≤ r) :
    U^A ≤ U^(A+(3/200)*D-physicalGain d S D)*Y^(r-3/200) := by
  have hg := physicalGain_cap (S:=S) hd0 hd hD
  calc
    _ ≤ U^(A+(3/200)*D-physicalGain d S D) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow hY (by linarith))

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.rescaled_power_padded
#print axioms Sil.Uneven.Bootstrap.root_power_transport
#print axioms Sil.Uneven.Bootstrap.exception_envelope
