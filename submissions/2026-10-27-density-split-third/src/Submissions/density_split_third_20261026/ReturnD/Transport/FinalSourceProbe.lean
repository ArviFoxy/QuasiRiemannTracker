/- Repeated marks: fork of Collet's generic return module Transport.FinalSourceProbe (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Modified by Sil (2026-10-26): forked into QRH.DensitySplitThird.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.density_split_third_20261026.ReturnD.Transport.Transport.SourceCorrection
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericData
import Submissions.hailey_collet_1252270103.Record1252270103Return.Low.Probe
import Submissions.density_split_third_20261026.ReturnD.Transport.Transport.PrincipalSignal
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Continuation

set_option autoImplicit false
namespace QRH.DensitySplitThird.Return.GenericPhysical.FinalAssembly
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.DensitySplitThird.Return.Geometry.BoundsN]
open scoped Classical ContDiff
open QRH.Record1252270103Return.Geometry
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical QRH.Record1252270103Return.GenericPhysical PrincipalSignalComparison
open QRH.DensitySplitThird.Return.GenericPhysical.Assembly

def sourceProbe (D : BaselineData) (F : BaselineSourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  Record1252270103Low.normalizedProbe F.modulus ⊤ F.S F.maximal D.length 1 2
    (fun _=>F.w) F.W F.W η

theorem sourceProbe_low (D : BaselineData) (F : BaselineSourceData D)
    (loss : ℝ) (hloss : 0< loss) (η : Character) :
    sourceProbe D F η=O[atTop](fun Z : ℝ=>Z^(Assembly.signal theta+loss)) := by
  have hh := Record1252270103Low.normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss D.length D.slots_pos
    D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  have he : Assembly.signal theta = Geometry.signal theta := by
    dsimp [Assembly.signal,Assembly.signalShift,QRH.DensitySplitThird.ReturnT.Transport.Assembly.signal,Geometry.signal,Geometry.signalShift]
    rw [QRH.DensitySplitThird.ReturnT.Transport.Assembly.signalShift_eq]
    change theta + -(4+(y-x))/6=theta + -(4+y-x)/6
    ring
  rw [he]
  exact hh

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|theta< s.re} ∧
    (∀s : ℂ,theta< s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact QRH.DensitySplitThird.ReturnT.Transport.Transport.actual_source_analytic S hS η

theorem fixed_source_contract (D : BaselineData) (F : BaselineSourceData D)
    (loss sigma : ℝ) (hloss : 0< loss)
    (herror : ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-sigma))) :
    Cycle25.PrimitiveProbeContract theta Assembly.signalShift loss sigma := by
  intro η _
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  simpa only [Assembly.signal,QRH.DensitySplitThird.ReturnT.Transport.Assembly.signal] using sourceProbe_low D F loss hloss η
end
end QRH.DensitySplitThird.Return.GenericPhysical.FinalAssembly

