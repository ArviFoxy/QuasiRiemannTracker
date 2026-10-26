/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Low.InitialRemainderScalarSumNode
(Hailey Collet). Original note: actual selected first-column
remainder sums after pool, allocation and label counting; the only outstanding admissions are
geometric and numerical.

**MAIN remainder twin on the transfer residual.** The first layer is the canonical initial input
`s₀`; the second layer is the transfer residual `s := s₀.restrict J` (a canonical initial input of
the restricted slot data); the pool has the actual width `a`; the MAIN radius uses `amp` with
`a ≤ amp ≤ Amix` and the δ-shift `amp - a ≤ Σ_{j∈J} w j + κ`, `0 ≤ κ ≤ Amix - a`.
The node facts are plain hypotheses: the first-layer budget at the mixed scale `F`
(`sourceTReal n b + b + 4e < B₀·F`, `0 ≤ F`, `F + 6·Amix ≤ 1`: `MixedGeometry.parent_budget_room`
with `F = sourceF3Real n low b = 1 - 6·Amix`, and `MixedGeometry.amp_small`). They give the mixed
volume gap, which pays the zero term's `+4δ`. Constants are uniform in all slot types, hence in `J`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalarSumNode
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Low.InitialRemainderScalarSum
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.InitialMainRemainderGap
import Submissions.arvi_mixed_step.Downstream.MainRestrict

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
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
open ConcretePrimeRowBridge CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103Low QRH.Record1252270103Source.InitialPhysical
open Record1252270103Finite Record1252270103StepScalar
local notation "O"=>HeckeFamily.O

variable (rayM : Ideal O) [NeZero rayM]
local instance remainderNodeFiniteQuotient_mx : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot)
variable (hsW : Function.support Wslot⊆Set.Icc (1:ℝ) 2)

/-- Mixed MAIN remainder sums on the transfer residual (two parents, two amplitudes). -/
theorem eventual_initial_remainder_sums_mx (N : ℕ) (ell epsMass epsZero epsCount : ℝ)
    (hell : 0<ell) (hmass : 0<epsMass) (hzero : 0≤epsZero) (hcount : 0<epsCount) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](hZ : 0<Z)(η η₀ : Character)(R₀ : Ideal O)
      (θ : ι→RayQuotient.Characters rayM H)(w v : ι→ℝ)(ht : ℝ)(p : Profiles (1/4) (9/4))
      (X₁ X₂ Y₁ Y₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)(hY₁ : 0<Y₁)(hY₂ : 0<Y₂)
      (hprod : Y₁*Y₂=X₁*X₂),
    let s₀:=initialInput rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(n low : Source)(b width Amix F a κ : ℝ),
      sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*F→0≤F→F+6*Amix≤1→
      0≤(n.allowance:ℝ)→0≤(n.L:ℝ)→(low.B:ℝ)≤1→width≤PhysicalLowGuard.step n→
      (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
        (length Z X₁) (length Z X₂) (∑i,w i) 1→
      b-(n.allowance:ℝ)-width≤∑i,w i→(∑i,w i)≤b→Fintype.card ι≤N→
      0≤a→0≤κ→κ≤Amix-a→
    ∀(Jset : Finset ι)(amp : ℝ),a≤amp→amp≤Amix→amp-a≤(∑j∈Jset,w j)+κ→
    let s:=s₀.restrict Jset
    let allowance:=(n.allowance:ℝ)
    let Cann:=initialCann N
    ∀(modifier : Tuple ι→ℂ)(R : Ideal O)(W : 𝓢(ℝ,ℂ))(ξ reserve loss saving : ℝ)(hK : 0<Z^(1:ℝ)),
      frequencyLoss Z 32 ξ+reserve+2*epsMass+loss+epsZero≤2*allowance→
    ∀(P : Finset (Ideal O))(mesh BD Bsource : ℝ)(depth : ℕ),
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j),
        (column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin)
        (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let C:=fun j=>geometryColumnIdeal reflected s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j)
    let label:=fun j=>FirstFamily.firstLabel s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j)
    let Hmain:=fun j=>firstMainRadius reflected (Z^(1:ℝ)) (volume s) Z ξ (3*amp) reserve (label j)
    let radius:=fun j=>literalFirstRadius reflected (Z^(1:ℝ)) (volume s₀) Z ξ reserve (label j)
    let H0:=fun j=>(geometryFirstSource s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j).1).H0
    let scalar:=fun j=>balancedColumnScalar reflected s₀ modifier R 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s₀)) hK bin
      (fun q=>normPhase (coordinateBlock s₀ modifier R 1 W (Z^(1:ℝ)) Z ξ q)) (column j)
    let factor:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t : J→ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→
    let amplitude:=fun j=>‖scalar j‖^2*
      (((bands (H0 j)).card:ℝ)*((actualAllocations s₀.pools (C j)).card:ℝ)^2/(P.card:ℝ)*
        ((radius j+6*a)/ell))*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2
    (∀j,sourceRadius (child s (C j) R (alloc j) (τ j) (t j))≤
      (Cann/((C j).absNorm:ℝ))*volume s) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(Cann/((C j).absNorm:ℝ))^(1+epsZero)*(volume s)^epsZero/
          ((column j).2.1.val.absNorm:ℝ))≤
      Czero*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance+2*epsCount)) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(volume (child s (C j) R (alloc j) (τ j) (t j))/volume s)*Z^(-saving)/
          ((column j).2.1.val.absNorm:ℝ))≤
      Ctail*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance-saving+2*epsCount)) := by
  obtain ⟨Cz,Ct,hCz,hCt,hbound⟩:=eventual_actual_remainder_sums_mx N
    (initialSlotBound Wslot hW hsW) (initialCann N) ell epsMass epsZero epsCount
    (initialSlotBound_ge_one Wslot hW hsW) (initialCann_pos N) hell hmass hzero hcount
  refine ⟨Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [hbound,eventual_radius_absorption N 1 (by norm_num)] with Z hz hrad
  refine ⟨hz.1,?_⟩
  intro ι _ _ hZ η η₀ R₀ θ w v ht p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod s₀
    n low b width Amix F a κ hroom hF0 hFA he hL hB hw hadm hlo hhi hN ha hκ0 hκ
    Jset amp hamplo hamp hshiftw s allowance Cann
    modifier R W ξ reserve loss saving hK herr P mesh BD Bsource depth hpool
    reflected bin J _ column hinj hlive hcap C label Hmain radius H0 scalar factor hr0 hr
    alloc τ t hf amplitude
  have hgap₀:=initial_main_amplification_gap_mx rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
    p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod n low b width Amix F hz.1 hroom hF0 hFA he hL hB hw
    hadm hlo hhi
  have hgap:Real.logb Z (volume s₀)+6*a+4*(amp-a)+2*κ+3*allowance≤1:=by
    dsimp only [allowance]
    linarith
  have hvol:volume s₀≤Z := by
    have hlog:Real.logb Z (volume s₀)≤1:=by linarith only [hgap,ha,hamplo,hκ0,he]
    calc
      _=Z^(Real.logb Z (volume s₀)):=(Real.rpow_logb hZ hz.1.ne' (volume_pos s₀)).symm
      _≤Z^(1:ℝ):=Real.rpow_le_rpow_of_exponent_le hz.1.le hlog
      _=Z:=Real.rpow_one Z
  have hsource:sourceRadius s₀≤Z^(2:ℝ) := by
    have hid:=initial_source_radius_identity rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
      p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    calc
      _=(2:ℝ)^Fintype.card ι*(9/4)^2*volume s₀:=hid
      _≤(2:ℝ)^N*(9/4)^2*Z:=mul_le_mul
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN) (sq_nonneg _))
        hvol (volume_pos s₀).le (by positivity)
      _≤Z^(2:ℝ):=by convert hrad.2 using 1 <;> norm_num
  have hcardv:Fintype.card {i // i∉Jset}≤N:=(Fintype.card_subtype_le _).trans hN
  have hlogv:Real.logb Z (volume s)=Real.logb Z (volume s₀)-∑ j∈Jset,w j:=
    QRH.MixedStep.Downstream.logb_volume_restrict s₀ Jset Z hz.1 w (fun _=>rfl)
  have hshift:amp-a≤Real.logb Z (volume s₀)-Real.logb Z (volume s)+κ:=by
    rw [hlogv]
    linarith
  have hb:=hz.2 s₀ s modifier R 1 W (p.profile 0) (p.profile 1) ξ a amp κ reserve allowance loss
    saving hK hN hcardv (fun _=>le_rfl) le_rfl le_rfl squarefree_one one_ne_zero
    (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    hsource (fun x hx=>(p.support 0 hx).1) (fun x hx=>(p.support 1 hx).1)
    ha hamplo hκ0 he hshift hgap herr P mesh BD Bsource depth hpool reflected bin J column hinj
    hlive hcap hr0 hr alloc τ t hf
  refine ⟨?_,by simpa only [map_one,Nat.cast_one,div_one] using hb⟩
  intro j
  have hC:C j≠0 := by
    cases reflected
    · exact (geometryFirstSource s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j).1).hC.1
    · exact (geometryFirstSource s₀ modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j).1).hD.1
  have hc:=selected_child_radius_cap s N 2 2 (9/4) hcardv (by norm_num) (by norm_num)
    (by norm_num) (fun _=>show (0:ℝ)≤2 by norm_num) (fun _=>le_rfl) le_rfl
    (show (0:ℝ)≤9/4 by norm_num) (show (0:ℝ)≤9/4 by norm_num) le_rfl le_rfl
    (C j) R hC (alloc j) (τ j) (t j) (hf j)
  have hcann:(2:ℝ)^N*(9/4)^2*2^N=Cann:=by dsimp only [Cann,initialCann];rw [mul_pow];ring
  rw [hcann] at hc
  exact hc

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.eventual_initial_remainder_sums_mx
