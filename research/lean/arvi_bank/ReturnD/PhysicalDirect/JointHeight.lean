/- Repeated marks: fork of Collet's generic return module PhysicalDirect.JointHeight (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- A single height is chosen after the physical and count polynomial degrees.
Adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<81/100 in the bank fork, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_bank.ReturnD and QRH.ArviDensity.Return (no other change). -/
import Submissions.arvi_bank.ReturnD.Schedule
import Submissions.arvi_bank.ReturnD.PhysicalDirect.SourceMoments
import Submissions.arvi_bank.ReturnD.PhysicalDirect.MomentMono
import Submissions.arvi_bank.ReturnD.PhysicalDirect.Chosen
set_option autoImplicit false
open QRH.Record1252270103Return

namespace QRH.ArviDensity.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [QRH.ArviDensity.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical
open Filter OAI OAI.SevenEighths HeckeFamily QRH.ArviDensity.Return.GenericArithmetic
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open QRH.ArviDensity.Return.GenericPhysical.FinalAssembly
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount

theorem actual_joint_height (A : ChosenData) (hgap : theta<HeckeZeroSupremum.beta)
    (haffine : ∀w∈scheme.windows,WeightedAffineFineInput A.F w.face)
    (Jw : ℝ) (hJw : 0≤Jw) :
    ∀η : Character,∃τ : ℝ,HeightAdmissible A.D A.P Jw τ ∧
      ∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ)) := by
  intro η
  have hb : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)<theta := by linarith [QRH.ArviDensity.Return.Geometry.BoundsN.theta_bounds.1]
    linarith
  have hk : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ := by
    rw [←A.kappa_exact];exact A.kappa_incumbent
  obtain ⟨J,hJ,C,hC,hbound⟩ := actual_source_moments A.D A.F A.counts hb A.kappa_exact.ge hk A.fine haffine η
  obtain ⟨τ,hheight⟩ := choose_height A.D A.P (J+Jw) (by positivity)
  have hw : HeightAdmissible A.D A.P Jw τ := height_admissible_mono hheight (by linarith)
  have hc : HeightAdmissible A.D A.P J τ := height_admissible_mono hheight (by linarith)
  refine ⟨τ,hw,max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ hc.1 (by linarith [hc.2.1]),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J A.D.t hC.le hZ hc.1.le hJ
    (by linarith [hc.2.2.2.2.2])).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end QRH.ArviDensity.Return.GenericPhysical.PhysicalDirect
