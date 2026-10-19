/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Actual Target830 source specialization; predecessor OpenAI/Hailey Collet attribution retained. Apache-2.0. -/
import Candidate.Uneven.EndpointPublic
import Candidate.Uneven.EndpointData
import Candidate.Cycle25.Numerator.PhysicalFront

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Source
variable [config : Configuration]
open OAI.SevenEighths.UnevenEndpoint
open OAI OAI.SevenEighths OAI.SevenEighths.UnevenEndpoint.Physical HeckeFamily

lemma source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤ a) (hatop : a≤7/8) :
    0≤(2*a-1)/2 ∧ (2*a-1)/2≤1 ∧
    1-a-6*D.e≤1/2-(2*a-1)/2 ∧
    -(1/100:ℝ)≤1/2-(2*a-1)/2 ∧
    1+4*D.e≤(a+16*D.e)+(1/2-(2*a-1)/2) := by
  have he:=D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

lemma source_complex_profile_norm (D : BaselineData) (F : BaselineSourceData D) (r : ℝ) :
    ‖F.W r‖≤1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded r).1]
  exact (F.bounded r).2

lemma source_cutoff_le_base (b : ℝ) (hb : 0≤ b) :
    ∀ᶠU:ℝ in atTop,1< U ∧ ∀d:ℝ,(1/2:ℝ)≤ d → b*U^(y/d)≤ U := by
  have he : ∀ᶠU:ℝ in atTop,b≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0< d:=by linarith
  have hy : y/d≤19/20 := by
    apply (div_le_iff₀ hdp).mpr
    have hy : y≤19/40:=by
      cases config with
      | mk stage => cases stage <;> norm_num [y,h,ell,theta,Sil.Uneven.WarmupRows.theta,
          Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end OAI.SevenEighths.UnevenEndpoint.Physical.Source

#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.Source.source_packet_lines
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.Source.source_complex_profile_norm
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.Source.source_cutoff_le_base
