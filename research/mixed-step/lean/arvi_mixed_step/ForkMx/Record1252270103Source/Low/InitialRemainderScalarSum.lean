/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Low.InitialRemainderScalarSum
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: actual selected first-column
remainder sums after pool, allocation and label counting; the only outstanding admissions are
geometric and numerical.

**MAIN remainder twin (zero and tail sums), generic form.** Two parents and two amplitudes:
* first layer `s₀`: columns, labels, balanced scalar at `logb Z (volume s₀)`, side and radical,
  `H0`, the pool radius `literalFirstRadius … (volume s₀)` and the MAIN-prefactor allocation card;
* second layer `s` (the transfer residual): allocations, frozen coefficients, children, `volume s`
  and the MAIN radius `firstMainRadius … (volume s) … (3·amp)`;
* the pool `P` at the actual amplitude `a`.
The node fact is the mixed volume gap `A₀ + 6a + 4(amp - a) + 2κ + 3e ≤ 1` together with the shift
`amp - a ≤ A₀ - logb Z (volume s) + κ`; the targets are Collet's (`-a-e+2ε`, `-a-e-saving+2ε`). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalarSum
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Low.InitialRemainderScalar
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Coefficient.MarkedMainRemainderSum

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily Cycle61InitialMass Cycle61Moment CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentSourceInputTailUniform (plainControl)
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.Pool
open QRH.Record1252270103Source.MarkedMainRemainder
open QRH.Record1252270103Source.ExceptionalPrice
local notation "O"=>HeckeFamily.O

private theorem zero_restore_mx (k sc band card P rad f pc h q v d : ℝ) (hk : k≠0) :
    sc*(band*card/P*rad)*f*pc^2*h*q*v/d =
      k/16*(sc*(card*f*(4*pc)^2*q)*(band*P⁻¹*rad/k)*(h*v)/d) := by
  calc
    _=(k*k⁻¹)*(sc*(band*card/P*rad)*f*pc^2*h*q*v/d):=by rw [mul_inv_cancel₀ hk,one_mul]
    _=_:=by ring

private theorem tail_restore_mx (k sc band card P rad f pc h q v d : ℝ) (hk : k≠0) :
    sc*(band*card/P*rad)*f*pc^2*h*q*v/d =
      k/4*(sc*(card*f*(2*pc)^2*q)*(band*P⁻¹*rad/k)*(h*v)/d) := by
  calc
    _=(k*k⁻¹)*(sc*(band*card/P*rad)*f*pc^2*h*q*v/d):=by rw [mul_inv_cancel₀ hk,one_mul]
    _=_:=by ring

/-- Collet's `eventual_actual_remainder_sums` with two parents and two amplitudes. -/
theorem eventual_actual_remainder_sums_mx (N : ℕ) (Cs Cann ell epsMass epsZero epsCount : ℝ)
    (hCs : 1≤Cs) (hCann : 0<Cann) (hell : 0<ell)
    (hmass : 0<epsMass) (hzero : 0≤epsZero) (hcount : 0<epsCount) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι₀ ι : Type}[Fintype ι₀][DecidableEq ι₀][Fintype ι](s₀ : Input ι₀)(s : Input ι)
      (modifier : Tuple ι₀→ℂ)(R seed : Ideal O)
      (W W₁ W₂ : 𝓢(ℝ,ℂ))(ξ a amp κ reserve allowance loss saving : ℝ)(hK : 0<Z^(1:ℝ)),
      Fintype.card ι₀≤N→Fintype.card ι≤N→(∀i,s.M i≤Cs)→s.upper≤2→1≤s₀.lower→
      Squarefree seed→seed≠0→s₀.W₁ 0=0→s₀.W₂ 0=0→sourceRadius s₀≤Z^(2:ℝ)→
      (∀x,s₀.W₁ x≠0→(1/4:ℝ)≤x)→(∀x,s₀.W₂ x≠0→(1/4:ℝ)≤x)→
      0≤a→a≤amp→0≤κ→0≤allowance→
      amp-a≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ→
      Real.logb Z (volume s₀)+6*a+4*(amp-a)+2*κ+3*allowance≤1→
      frequencyLoss Z 32 ξ+reserve+2*epsMass+loss+epsZero≤2*allowance→
    ∀(P : Finset (Ideal O))(mesh BD Bsource : ℝ)(depth : ℕ),
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j),
        (column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin)
        (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let C:=fun j=>geometryColumnIdeal reflected s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j)
    let label:=fun j=>FirstFamily.firstLabel s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j)
    let Hmain:=fun j=>firstMainRadius reflected (Z^(1:ℝ)) (volume s) Z ξ (3*amp) reserve (label j)
    let radius:=fun j=>literalFirstRadius reflected (Z^(1:ℝ)) (volume s₀) Z ξ reserve (label j)
    let H0:=fun j=>(geometryFirstSource s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j).1).H0
    let scalar:=fun j=>balancedColumnScalar reflected s₀ modifier R seed (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s₀)) hK bin
      (fun q=>normPhase (coordinateBlock s₀ modifier R seed W (Z^(1:ℝ)) Z ξ q)) (column j)
    let factor:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t : J→ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→
    let amplitude:=fun j=>‖scalar j‖^2*
      (((bands (H0 j)).card:ℝ)*((actualAllocations s₀.pools (C j)).card:ℝ)^2/(P.card:ℝ)*
        ((radius j+6*a)/ell))*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) W₁ W₂)^2*
        Hmain j*(Cann/((C j).absNorm:ℝ))^(1+epsZero)*(volume s)^epsZero/
          ((column j).2.1.val.absNorm:ℝ))≤
      Czero*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*factor*
        Z^(-a-allowance+2*epsCount)/(seed.absNorm:ℝ)) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) W₁ W₂)^2*
        Hmain j*(volume (child s (C j) R (alloc j) (τ j) (t j))/volume s)*Z^(-saving)/
          ((column j).2.1.val.absNorm:ℝ))≤
      Ctail*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*factor*
        Z^(-a-allowance-saving+2*epsCount)/(seed.absNorm:ℝ)) := by
  obtain ⟨Cz,Ct,hCz,hCt,hbound⟩:=selected_remainder_sums_mx N Cs 2 Cann 1 (1/4) 2 4
    epsMass epsZero epsCount hCs (by norm_num) hCann (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hmass hzero hcount
  have hcw:=weightConstant_pos ell hell
  refine ⟨weightConstant ell/16*Cz,weightConstant ell/4*Ct,by positivity,by positivity,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι₀ ι _ _ _ s₀ s modifier R seed W W₁ W₂ ξ a amp κ reserve allowance loss saving hK
    hN₀ hN hM hu hlo hs hs0 hz₁ hz₂ hsource hs₁ hs₂ ha hamp hκ0 he hshift hgap herr
    P mesh BD Bsource depth hpool reflected bin J _ column hinj hlive hcap C label Hmain radius H0
    scalar factor hr0 hr alloc τ t hf amplitude
  have hH0 (j:J):0<H0 j := lt_trans zero_lt_one
    (actual_first_H0_and_frequency s₀ modifier R seed (Z^(1:ℝ)) Z ξ hK bin (column j)).1
  let weight:=fun j=>mainWeight P ell (H0 j) (radius j) a/weightConstant ell
  have hw (j:J):0≤weight j ∧ weight j≤Z^(-a+loss):=
    normalized_pool_weight P Z a ell mesh loss BD Bsource depth hpool hell (H0 j) (radius j)
      (hH0 j) (hr0 j) (hr j)
  have hp (j:J):=actual_remainder_admissions_mx reflected s₀ modifier R seed Z ξ a amp κ (volume s)
    reserve allowance 2 epsMass epsZero loss saving (weight j) hz.1 hK (volume_pos s) bin (column j)
    ha hamp hκ0 he hzero hshift hgap herr (hw j).2
  have hb:=hz.2 s₀ s modifier R seed W W₁ W₂ 1 ξ hK hN₀ hN hM hu hlo hs hs0 hz₁ hz₂
    hsource hs₁ hs₂ reflected bin J column hinj hlive hcap alloc τ t weight
      (fun j=>Real.logb Z (Hmain j)+epsZero*Real.logb Z (volume s))
      (fun j=>Real.logb Z (Hmain j)-saving) (-a-allowance) (-a-allowance-saving)
      hf (fun j=>(hw j).1) (fun j=>(hp j).1) (fun j=>(hp j).2)
  have hH (j:J):0<Hmain j :=
    first_main_radius_pos reflected (Z^(1:ℝ)) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hz.1) (label j)
  have hcne:=ne_of_gt hcw
  constructor
  · have hh:=mul_le_mul_of_nonneg_left hb.1 (by positivity : 0≤weightConstant ell/16)
    refine (show _=weightConstant ell/16*(_) from ?_).trans_le (hh.trans_eq (by ring))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [zero_power_identity Z (Hmain j) (volume s) epsZero hz.1 (hH j) (volume_pos s)]
    dsimp only [amplitude,weight,mainWeight,zeroAllocationFactor_mx]
    exact zero_restore_mx _ _ _ _ _ _ _ _ _ _ _ _ hcne
  · have hh:=mul_le_mul_of_nonneg_left hb.2 (by positivity : 0≤weightConstant ell/4)
    refine (show _=weightConstant ell/4*(_) from ?_).trans_le (hh.trans_eq (by ring))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [tail_power_identity Z (Hmain j) saving hz.1 (hH j)]
    dsimp only [amplitude,weight,mainWeight,tailAllocationFactor_mx]
    exact tail_restore_mx _ _ _ _ _ _ _ _ _ _ _ _ hcne

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.eventual_actual_remainder_sums_mx
