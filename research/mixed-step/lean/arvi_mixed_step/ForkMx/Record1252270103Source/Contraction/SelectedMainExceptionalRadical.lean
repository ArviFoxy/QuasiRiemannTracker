/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Contraction.SelectedMainExceptionalRadical
(Hailey Collet). Original notes: adapted for the actual MAIN
frozen-one constructor from the retained LOW cap/aggregate chain; inherited upstream notices remain
required; actual canonical initial and modified first-label exceptional caps.

Collet's `eventually_initial_family_radical` for the two-parent MAIN complement family: the family
lives on the second-layer input, its column data are abstract (first layer), and the pool is at the
actual amplitude `a` (see `SelectedMainExceptionalInitial` of this fork). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Contraction.SelectedMainExceptionalRadical
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Contraction.SelectedMainExceptionalInitial

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction.SelectedMainExceptional
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open ActualEisensteinCubic
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional ConcretePrimeRowBridge
open Cycle61InitialMass Record1252270103Second OAI.SevenEighths.Record1252270103Source
open QRH.Record1252270103Low InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized ForcedCost Pool Admission.FirstFamily
open High.GlobalPhysical SecondSectorDatum
local notation "O"=>HeckeFamily.O
local instance mainRadicalDecidableEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance mainRadicalSumDecidableEq_mx {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open QRH.Record1252270103Source.InitialRegularToTruncated
open Low.SelectedExceptionalNormalizedMasked
open CenteredMomentSecondHeightFamily

/-- The initial exceptional norm bound of the two-parent MAIN complement family. -/
theorem eventually_initial_family_radical_mx {α:Type*}[Fintype α]
    (N:ℕ)(Bface lam cap:ℝ)(hB:Bface≤1)(hlam:1≤lam)(hcap:cap≤1)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)
    (hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (η η₀:Character)(R₀:Ideal O)(hR:R₀≠0)
    (Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (a ell mesh loss ξ:ℝ)(depth:ℕ)
    (hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<a)(hloss:0<loss)(hdepth:(2:ℝ)/ell≤depth)
    (W:𝓢(ℝ,ℂ))(decay:ℕ)(ε εL power:ℝ)(hε:0<ε)(hεL:0<εL)
    (hpower0:0≤power)(hpower:power<1/2):
    ∃J:Finset α→ℕ,∃T:Finset α→Finset (ℕ×ℕ),(∀A,(0,0)∈T A) ∧
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃C₀ K₀ Cphys:Finset α→ℝ,(∀A,0<C₀ A ∧ 0<K₀ A ∧ 0≤Cphys A) ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{Label:Type*}[Fintype Label],
    ∀(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
    Fintype.card α≤N→(∀i,0≤w i)→(∀i,w i≤mesh)→
    (globalFace Bface lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
    1≤Y₂→Y₂≤X₁→Y₂≤X₂→
    let s:=initialInput rayM H hH Wslot hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(C seed:Label→Ideal O)(hseed:∀l,Squarefree (seed l))(τ:Label→Character)
      (K Tsec:Label→ℝ)(hK:∀l,0<K l),
      (∀l,C l≠0)→(∀l,((C l).absNorm:ℝ)≤Z^(2:ℝ))→
      (∀l,((τ l).modulus.absNorm:ℝ)≤Z^(5:ℝ))→(∀l,frequencyRadius (Tsec l) Z ξ≤Z^(3:ℝ))→
    ∀(alloc:∀l,actualAllocations s.pools (C l))(ht:Label→ℝ)(amplitude:Label→ℝ)
      (χ₀:Label→RayCharacter),
    let m:=fixedBadMask*idealGenerator R₀
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^a)
    let f:=mainAllocatedFamily s W (p.profile 0) (p.profile 1) Z R₀ C seed
      alloc τ ht P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      K Tsec (fun _=>volume s) amplitude ξ hK χ₀ m
    ‖∑q,f.phase Q q*(f.block Q q).value W‖≤
      ∑q,‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
        familyPayment f (f.retainedRadial Q (fun q=>Y₂/((C q.1).absNorm:ℝ))) Q
          J T C₀ K₀ Cphys ε εL power decay q := by
  have hell0:0<ell:=hmesh.trans_lt hgap
  have hamp:0<a:=hell0.trans hell
  obtain ⟨J,T,hT,hp⟩:=exceptional_complete_family_radical (α:=α) W decay
    (1/4) (9/4) ε εL 5 13 4 4 12 a 2 12 ell power 4 depth
    (by norm_num) (by norm_num) hε hεL (by norm_num) (by norm_num) hamp.le hell0 hpower0 hpower
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,K₀,Cphys,hpos,hp⟩:=hp Q hQ0 hQ hQ72
  refine ⟨C₀,K₀,Cphys,hpos,?_⟩
  filter_upwards [eventually_initial_first_family_polynomialCaps_mx N Bface lam cap hB hlam hcap
    rayM H hH Wslot hW hsW η η₀ R₀ hR Sbad hbad a ell mesh loss ξ depth
    hmesh hgap hell hloss hdepth W] with Z hcapZ
  refine ⟨hcapZ.1,?_⟩
  intro hZ Label instLabel θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hwm hadm hy₂ hl₁ hl₂ s C seed hseed τ K Tsec hK hC hCcap hchar hradius
    alloc ht amplitude χ₀ m P f
  have hc:=hcapZ.2 hZ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hwm hadm hy₂ hl₁ hl₂ C seed hseed τ K Tsec hK hC hCcap hchar hradius
    alloc ht amplitude χ₀ m Q
  have hm:m≠0:=mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R₀ hR)
  have hml:goodLambda∣m:=(dvd_mul_right goodLambda (2:O)).trans (dvd_mul_right _ _)
  have hm2:(2:O)∣m:=(dvd_mul_left (2:O) goodLambda).trans (dvd_mul_right _ _)
  exact hp Z hZ (fun l=>liveIndices (alloc l).val) f hm hml hm2
    (f.retainedRadial Q (fun q=>Y₂/((C q.1).absNorm:ℝ))) hc

end
end QRH.Record1252270103Source.Contraction.SelectedMainExceptional
#print axioms QRH.Record1252270103Source.Contraction.SelectedMainExceptional.eventually_initial_family_radical_mx
