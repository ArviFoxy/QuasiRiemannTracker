/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Core.ExceptionalFrozenSum
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: full first-key payment with
the original frozen coefficient, child volume, MAIN prefactor and Fourier scale; every residual
projector remains summed.

Two parents, two amplitudes (design `L45_DESIGN.md` §3 F6):
* first layer `s₀`: columns, labels, the balanced scalar at `logb Z (volume s₀)`, the counting, and
  the allocation card of the MAIN prefactor (`mainExtra s₀ …`);
* second layer `s`: the allocation, its frozen coefficient, the child, `volume s`, the MAIN radius
  and Fourier scale at `(volume s, 3·amp)`;
* the pool `P` at the actual amplitude `a` (`FixedCellPoolData P Z a …`, ball factor `radius+6a`).
The per-label price is `(vol child)^{1/3}·MAIN_v^{5/6}·Z^{-a}/Z^{left(A₀)}` (Collet's
`frozen_first_payment` is generic in the scalar and is applied at `amp` with the loss shifted by
`amp - a`); `hshift` and the mixed centered gate pay it. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFrozenSum
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.ExceptionalFirstSum

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open Record1252270103Second
open OAI.SevenEighths.Record1252270103Source.Collision
open High.CoupledFirst Admission Pool
local notation "O"=>HeckeFamily.O

/-- **Mixed frozen first-key sum** (two parents `s₀`, `s`; pool amplitude `a`, radius
amplitude `amp`). -/
theorem selected_frozen_first_sum_mx (N : ℕ)(lo ap B Bseed εcount εcard ell lower radiusMax : ℝ)
    (hlo : 0<lo)(hap : 0<ap)(hB : 0≤B)(hBseed : 0≤Bseed)(hcount : 0<εcount)
    (hcard : 0<εcard)(hell : 0<ell)(hlower : 0<lower)(hmax : 0≤radiusMax) :
    ∃Ctotal : ℝ,0<Ctotal ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι₀ ι : Type}[Fintype ι₀][DecidableEq ι₀][Fintype ι](s₀ : Input ι₀)(s : Input ι)
      (A₁ A₂ Dmark Kmark R seed : Ideal O)(F : Ideal O→ℂ)(W : 𝓢(ℝ,ℂ))
      (K : ℚ)(n : Source)(b ξ reserve poolLoss plainError Amix a κ amp : ℝ),
      sourceTReal n b+b+9*Amix+(n.highFee:ℝ)<5/6+(499/1000)*(49/100-(K:ℝ)*b)→
      Fintype.card ι₀≤N→lo≤s₀.lower→
      Squarefree seed→seed≠0→s₀.W₁ 0=0→s₀.W₂ 0=0→sourceRadius s₀≤Z^B→
      (∀x,s₀.W₁ x≠0→ap≤x)→(∀x,s₀.W₂ x≠0→ap≤x)→
      Real.logb Z (volume s₀)≤sourceTReal n b+b+plainError→
      amp-a≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ→amp≤Amix→
      plainError+5*(frequencyLoss Z 32 ξ+reserve)/6+(εcard+poolLoss+ξ/12)+2*κ≤2*Amix-a→
    let modifier:=markedSourceModifier A₁ A₂ Dmark Kmark F
    ∀(hZ : 1<Z)(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s₀ modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s₀ modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s₀ modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^Bseed)→
    let label:=fun j=>FirstFamily.firstLabel s₀ modifier R seed (Z^1) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)
    let C:=fun j=>if reflected then (label j).1.2 else (label j).1.1
    let scalar:=fun j=>balancedColumnScalar reflected s₀ modifier R seed (Z^1) Z ξ 1
      (Real.logb Z (volume s₀)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin
      (fun q=>normPhase (coordinateBlock s₀ modifier R seed W (Z^1) Z ξ q)) (column j)
    let Hmain:=fun j=>firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label j)
    let Rmain:=fun j=>frequencyRadius
      (firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N (label j)) Z ξ
    ∀(alloc:∀j,actualAllocations s.pools (C j))(τ:J→Character)(t H0 radius:J→ℝ)
      (P:Finset (Ideal O))(mesh BD Bsource:ℝ)(depth:ℕ),
      FixedCellPoolData P Z a ell mesh poolLoss BD Bsource depth→
      (∀j,0<H0 j)→(∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤radiusMax)→
    let extra:=fun j=>((bands (H0 j)).card:ℝ)*((actualAllocations s₀.pools (C j)).card:ℝ)^2/
      (P.card:ℝ)*((radius j+6*a)/ell)
    (∑j,(‖scalar j‖^2*extra j*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2/volume s)*
      (Hmain j/lower)*(max 1 (Z^(49/100-(K:ℝ)*b)/((C j).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
      volume (child s (C j) R (alloc j) (τ j) (t j))*(4*Rmain j)^(1/6:ℝ)/
      ((column j).2.1.val.absNorm:ℝ))≤
      Ctotal*forcedProfileCost s*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^(-(n.highFee:ℝ)-4*Amix+2*εcount)/(seed.absNorm:ℝ) := by
  obtain ⟨A,hA,hpref⟩:=uniform_first_main_prefactor N B εcard ell lower radiusMax hB hcard hell hlower hmax
  obtain ⟨C,hC,hcountZ⟩:=selected_first_radical_sum_mx N lo ap B Bseed εcount hlo hap hB hBseed hcount
  let fixed:ℝ:=(4:ℝ)^(1/6:ℝ)*((2:ℝ)^N)^(1/3:ℝ)
  have hfixed : 0<fixed := by dsimp only [fixed];positivity
  refine ⟨C*A*fixed,by positivity,?_⟩
  filter_upwards [hcountZ] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι₀ ι inst₀ dec₀ inst s₀ s A₁ A₂ Dmark Kmark R seed F W K n b ξ reserve poolLoss plainError
    Amix a κ amp hgate hN hslower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hlog hshift hamp herr modifier hZ
    reflected bin J instJ column hinj hlive hcap label Cfirst scalar Hmain Rmain alloc τ t H0 radius
    P mesh BD Bsource depth hpool hH0 hr0 hr extra
  let G:=forcedProfileCost s*A*fixed
  have hG : 0≤G := mul_nonneg (mul_nonneg (forcedProfileCost_nonneg s) hA.le) hfixed.le
  have point(j:J) :
      (‖scalar j‖^2*extra j*‖frozenCoefficient (alloc j).val (Cfirst j) R s.ν s.W s.P‖^2/volume s)*
        (Hmain j/lower)*(max 1 (Z^(49/100-(K:ℝ)*b)/((Cfirst j).absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*
        volume (child s (Cfirst j) R (alloc j) (τ j) (t j))*(4*Rmain j)^(1/6:ℝ)/
        ((column j).2.1.val.absNorm:ℝ)≤
      G*(balancedFirstHighMass reflected s₀ modifier R seed W 1 Z ξ 0
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)*
        firstRadialFactor_mx reflected (label j) Z (volume s) (49/100-(K:ℝ)*b) amp a ξ reserve
          (εcard+poolLoss+ξ/12)/((column j).2.1.val.absNorm:ℝ)) := by
    have hsup:=FirstFamily.label_supported s₀ modifier R seed (Z^1) Z ξ _ bin (column j)
    have hc : Cfirst j≠0 := by cases reflected <;> first | exact hsup.1.1 | exact hsup.2.1.1
    have hn:=FirstFamily.label_common_bounds s₀ modifier R seed (Z^1) Z ξ _ bin hs hz₁ hz₂ (column j)
    have hnc : ((Cfirst j).absNorm:ℝ)≤Z^B := by
      cases reflected
      · exact hn.2.2.1.trans hsource
      · exact hn.2.2.2.trans hsource
    have he0 : 0≤extra j := by
      dsimp only [extra]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
        (div_nonneg (hr0 j) hell.le)
    have he:=hpref s₀ hN (Cfirst j) P Z a mesh poolLoss BD Bsource depth hc hnc hpool
      (H0 j) (radius j) (hH0 j) (hr0 j) (hr j)
    have hh:=frozen_first_payment s reflected (label j) hsup.1 hsup.2.1 R (alloc j) (τ j) (t j)
      (scalar j) N Z (49/100-(K:ℝ)*b) amp ξ reserve (extra j) lower A (εcard+poolLoss+(amp-a))
      (zero_lt_one.trans hZ) he0 hlower hA.le (by
        convert he using 1 <;> try rfl
        congr 2
        ring)
    rw [firstRadialFactor_shift_mx reflected (label j) Z (volume s) (49/100-(K:ℝ)*b) amp a ξ reserve
      (εcard+poolLoss+ξ/12) _ (by ring)] at hh
    have hd:=div_le_div_of_nonneg_right hh (Nat.cast_nonneg ((column j).2.1.val.absNorm))
    have hmass : balancedFirstHighMass reflected s₀ modifier R seed W 1 Z ξ 0
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)=
        ‖scalar j‖^2/((Cfirst j).absNorm:ℝ) := by
      unfold High.CoupledFirst.balancedFirstHighMass
      change ‖scalar j‖^2*((Cfirst j).absNorm:ℝ)^((0:ℝ)-1)=_
      norm_num [Real.rpow_neg_one,div_eq_mul_inv]
    rw [hmass]
    convert hd using 1 <;> dsimp only [G,fixed] <;> ring
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>point j)
  rw [←Finset.mul_sum] at hsum
  have hh:=hz.2 s₀ A₁ A₂ Dmark Kmark R seed F W K n b ξ reserve (εcard+poolLoss+ξ/12)
    plainError (volume s) Amix a κ amp hgate hN hslower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hlog
    (volume_pos s) hshift hamp herr hZ reflected bin J column hinj hlive hcap
  have hb:=hsum.trans (mul_le_mul_of_nonneg_left hh hG)
  convert hb using 1 <;> dsimp only [G,fixed] <;> ring

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.selected_frozen_first_sum_mx
