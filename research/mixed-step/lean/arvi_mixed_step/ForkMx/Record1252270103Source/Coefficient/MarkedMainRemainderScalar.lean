/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Coefficient.MarkedMainRemainderScalar
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: the literal MAIN radius and
balanced first-label normalization pay the zero and discarded-tail exponents; no earlier numerical
beta range is used.

`actual_main_radius_exponent` with the label of the first layer and a free (second-layer) volume
`V`: the MAIN radius of the transfer residual is read at `logb Z V`, its label at the original
columns. Collet's proof is unchanged (`actual_main_radius_power` takes any volume exponent). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.MarkedMainRemainderScalar

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily Cycle61InitialMass Cycle61Moment Cycle61SecondZero CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstExceptionalPrefactor CenteredMomentRankinRadical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open Record12518109Natural (balancedGeometrySide)
open QRH.Record1252270103Source.Pool
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The MAIN radius of a first-layer label at a free volume `V`. -/
theorem actual_main_radius_exponent_mx (reflected : Bool) (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (Z M ξ a reserve V : ℝ) (hZ : 1<Z) (hK : 0<Z^M) (hV : 0<V)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^M) Z ξ hK bin)) :
    firstMainRadius reflected (Z^M) V Z ξ (3*a) reserve
      (FirstFamily.firstLabel s modifier R seed (Z^M) Z ξ hK bin j)=
    Z^(mainBaseExponent reflected M (Real.logb Z V)
      (geometryExponents s modifier R seed (Z^M) Z ξ j.1.val)+
        6*a+frequencyLoss Z 32 ξ+reserve) := by
  let l:=FirstFamily.firstLabel s modifier R seed (Z^M) Z ξ hK bin j
  let A:=Real.logb Z V
  let v:=geometryExponents s modifier R seed (Z^M) Z ξ j.1.val
  have hs:=FirstFamily.label_supported s modifier R seed (Z^M) Z ξ hK bin j
  have hVe:V=Z^A:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hV).symm
  have he:Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)=v 4 := by
    change Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)=
      Real.logb Z ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm:ℝ)
    rw [first_projector_span]
  change firstMainRadius reflected (Z^M) V Z ξ (3*a) reserve l=_
  conv_lhs => rw [hVe]
  rw [actual_main_radius_power reflected l hs.1 hs.2.1 hs.2.2 Z M A a ξ reserve hZ]
  change Z^(_)=Z^(mainBaseExponent reflected M A v+6*a+frequencyLoss Z 32 ξ+reserve)
  rw [he]
  congr 1
  have hc:Real.logb Z (l.1.1.absNorm:ℝ)=v 0:=rfl
  have hd:Real.logb Z (l.1.2.absNorm:ℝ)=v 1:=rfl
  have hr:Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)=v 3:=rfl
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hc,hd,hr,mainBaseExponent] <;> ring

end
end QRH.Record1252270103Source.MarkedMainRemainder
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.actual_main_radius_exponent_mx
