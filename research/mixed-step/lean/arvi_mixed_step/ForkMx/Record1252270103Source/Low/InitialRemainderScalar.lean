/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Low.InitialRemainderScalar
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: actual first MAIN scalar
admissions, with the counted common radical distinct from the active conductor; no source estimate
is assumed.

The MAIN remainder admissions with two parents and two amplitudes. The scalar (side, radical) is the
first layer's at `A₀ = logb Z (volume s₀)`; the MAIN radius is the second layer's, at the residual
volume `Av = logb Z V` and the radius amplitude `amp`; the pool weight is at the actual amplitude
`a`. With `hshift : amp - a ≤ A₀ - Av + κ` the radius costs `4(amp - a) + 2κ` more than Collet's
(the design's `+4δ`), so the volume gap becomes `A₀ + 6a + 4(amp-a) + 2κ + 3e ≤ 1`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalar
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Coefficient.MarkedMainRemainderScalar
import Submissions.arvi_mixed_step.Downstream.Shift

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily Cycle61InitialMass ActualEisensteinCubic
open CenteredMomentFirstExceptionalPrefactor CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open QRH.Record1252270103Source.Admission
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.MarkedMainRemainder
open QRH.Record1252270103Source.Pool
open Record12518109Natural (balancedGeometrySide)
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residual MAIN radius against the first-layer side: the radius volume is the residual's,
the side volume the original's. -/
theorem actual_log_radius_payment_mx (reflected : Bool) (s₀ : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (Z M ξ amp reserve V : ℝ) (hZ : 1<Z) (hK : 0<Z^M) (hV : 0<V)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s₀ modifier R seed (Z^M) Z ξ hK bin)) :
    let v:=geometryExponents s₀ modifier R seed (Z^M) Z ξ j.1.val
    let A₀:=Real.logb Z (volume s₀)
    Real.logb Z (firstMainRadius reflected (Z^M) V Z ξ (3*amp) reserve
      (FirstFamily.firstLabel s₀ modifier R seed (Z^M) Z ξ hK bin j))
      -balancedGeometrySide reflected A₀ v+v 2≤2*Real.logb Z V-A₀-M+6*amp+frequencyLoss Z 32 ξ+reserve := by
  dsimp only
  rw [actual_main_radius_exponent_mx reflected s₀ modifier R seed Z M ξ amp reserve V hZ hK hV bin j,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    QRH.MixedStep.Downstream.balanced_side_eq reflected (Real.logb Z (volume s₀)) (Real.logb Z V)]
  have hb:=actual_main_base_payment reflected s₀ modifier R seed (Z^M) Z ξ M
    (Real.logb Z V) hZ j.1.val
  dsimp only at hb
  linarith only [hb]

/-- Three allowances in the mixed volume gap leave one allowance after paying the visible mass,
zero, pool, frequency and reserve errors, now with the residual radius. -/
theorem remainder_power_payment_mx
    (Z A₀ Av a amp κ allowance omega B epsMass epsZero loss saving weight Hlog side radical : ℝ)
    (hZ : 1<Z) (ha : 0≤a) (hamp : a≤amp) (hκ0 : 0≤κ) (he : 0≤allowance) (hz : 0≤epsZero)
    (hlog : Hlog-side+radical≤2*Av-A₀-1+6*amp+omega)
    (hshift : amp-a≤A₀-Av+κ)
    (hgap : A₀+6*a+4*(amp-a)+2*κ+3*allowance≤1)
    (herr : omega+B*epsMass+loss+epsZero≤2*allowance)
    (hweight : weight≤Z^(-a+loss)) :
    weight*Z^(B*epsMass+(Hlog+epsZero*Av)-side)≤Z^((-a-allowance)-radical) ∧
    weight*Z^(B*epsMass+(Hlog-saving)-side)≤Z^((-a-allowance-saving)-radical) := by
  have hAv : Av≤1:=by linarith only [hgap,hshift,ha,hamp,hκ0,he]
  have hzA : epsZero*Av≤epsZero:=by simpa using mul_le_mul_of_nonneg_left hAv hz
  have pay (power target : ℝ) (hh : (-a+loss)+power≤target) : weight*Z^power≤Z^target := by
    calc
      _≤Z^(-a+loss)*Z^power:=mul_le_mul_of_nonneg_right hweight
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _=Z^((-a+loss)+power):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm
      _≤Z^target:=Real.rpow_le_rpow_of_exponent_le hZ.le hh
  constructor
  · apply pay
    linarith only [hlog,hgap,herr,hzA,hshift]
  · apply pay
    linarith only [hlog,hgap,herr,hz,hshift]

/-- Mixed `hpzero`/`hptail` for `selected_remainder_sums_mx`. -/
theorem actual_remainder_admissions_mx (reflected : Bool) (s₀ : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (Z ξ a amp κ V reserve allowance B epsMass epsZero loss saving weight : ℝ)
    (hZ : 1<Z) (hK : 0<Z^(1:ℝ)) (hV : 0<V)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin))
    (ha : 0≤a) (hamp : a≤amp) (hκ0 : 0≤κ) (he : 0≤allowance) (hz : 0≤epsZero)
    (hshift : amp-a≤Real.logb Z (volume s₀)-Real.logb Z V+κ)
    (hgap : Real.logb Z (volume s₀)+6*a+4*(amp-a)+2*κ+3*allowance≤1)
    (herr : frequencyLoss Z 32 ξ+reserve+B*epsMass+loss+epsZero≤2*allowance)
    (hweight : weight≤Z^(-a+loss)) :
    let v:=geometryExponents s₀ modifier R seed (Z^(1:ℝ)) Z ξ j.1.val
    let A₀:=Real.logb Z (volume s₀)
    let Hlog:=Real.logb Z (firstMainRadius reflected (Z^(1:ℝ)) V Z ξ (3*amp) reserve
      (FirstFamily.firstLabel s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin j))
    weight*Z^(B*epsMass+(Hlog+epsZero*Real.logb Z V)-balancedGeometrySide reflected A₀ v)
      ≤Z^((-a-allowance)-v 2) ∧
    weight*Z^(B*epsMass+(Hlog-saving)-balancedGeometrySide reflected A₀ v)
      ≤Z^((-a-allowance-saving)-v 2) := by
  dsimp only
  apply remainder_power_payment_mx Z (Real.logb Z (volume s₀)) (Real.logb Z V) a amp κ allowance
    (frequencyLoss Z 32 ξ+reserve) B epsMass epsZero loss saving weight _ _ _ hZ ha hamp hκ0 he hz
  · have hh:=actual_log_radius_payment_mx reflected s₀ modifier R seed Z 1 ξ amp reserve V hZ hK hV bin j
    dsimp only at hh
    linarith only [hh]
  · exact hshift
  · exact hgap
  · exact herr
  · exact hweight

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.actual_log_radius_payment_mx
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.remainder_power_payment_mx
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.actual_remainder_admissions_mx
