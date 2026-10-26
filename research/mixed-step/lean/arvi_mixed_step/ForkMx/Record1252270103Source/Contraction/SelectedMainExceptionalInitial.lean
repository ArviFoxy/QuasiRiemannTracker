/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Contraction.SelectedMainExceptionalInitial
(Hailey Collet, Apache-2.0; inherited notices retained). Original notes: adapted for the actual MAIN
frozen-one constructor from the retained LOW cap/aggregate chain; inherited upstream notices remain
required; actual canonical initial and modified first-label exceptional caps.

Two parents (design `L45_DESIGN.md` §3 F6): the MAIN complement family lives on the second-layer
input (the transfer residual, itself a canonical initial input), while its column data (common
ideal `C`, projector seed, character `τ`, MAIN radius `K`, Fourier scale `Tsec`) come from the
first layer. Collet's statement reads them from the family input's own columns; here they are
abstract, with exactly the caps Collet's proof extracts from the columns as hypotheses
(`C ≠ 0`, `N(C) ≤ Z²`, `N(mod τ) ≤ Z⁵`, `frequencyRadius Tsec ≤ Z³`, `K > 0`, squarefree seeds).
The pool is at the actual amplitude `a` (`P = primePool … (Z^a)`, `ell < a`); `K`/`Tsec` may use
any radius amplitude. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Contraction.SelectedMainExceptionalInitial

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
local instance mainInitialDecidableEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance mainInitialSumDecidableEq_mx {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open QRH.Record1252270103Source.InitialRegularToTruncated

/-- Collet's `eventually_initial_first_family_polynomialCaps` with abstract (first-layer) column
data and the pool at the actual amplitude `a`. One threshold serves every input type and label
type. -/
theorem eventually_initial_first_family_polynomialCaps_mx
    (N:ℕ)(Bface lam cap:ℝ)(hB:Bface≤1)(hlam:1≤lam)(hcap:cap≤1)
    (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)
    (hH:RayOrthogonality.globalUnits rayM≤H)
    (Wslot:ℝ→ℂ)(hW:ContDiff ℝ ∞ Wslot)(hsW:Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (η η₀:Character)(R₀:Ideal O)(hR:R₀≠0)
    (Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (a ell mesh loss ξ:ℝ)(depth:ℕ)
    (hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<a)(hloss:0<loss)(hdepth:(2:ℝ)/ell≤depth)
    (W:𝓢(ℝ,ℂ)):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{α Label:Type*}[Fintype α][Fintype Label],
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
      (χ₀:Label→RayCharacter)(m:O)(Q:Ideal O),
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^a)
    let f:=mainAllocatedFamily s W (p.profile 0) (p.profile 1) Z R₀ C seed
      alloc τ ht P hseed (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
      K Tsec (fun _=>volume s) amplitude ξ hK χ₀ m
    PolynomialCaps f (f.retainedRadial Q (fun q=>Y₂/((C q.1).absNorm:ℝ)))
      Q (1/4) (9/4) 5 13 4 4 12 a 2 12 ell 4 depth := by
  filter_upwards [eventually_initial_caps N Bface lam cap hB hlam hcap,
    eventually_fixed_cell_pool rayM H hH Sbad hbad a ell mesh loss 12 2 depth hmesh hgap hell hloss,
    eventually_ge_atTop (R₀.absNorm:ℝ),eventually_ge_atTop ((9/4:ℝ)^2),
    eventually_ge_atTop (4:ℝ),
    eventually_ge_atTop ((CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*2)]
    with Z hbase hpool hRcap hplainConst hfour hfixed
  refine ⟨hbase.1,?_⟩
  intro hZ α Label instα instLabel θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    hN hw hwm hadm hy₂ hl₁ hl₂ s C seed hseed τ K Tsec hK hC hCcap hchar hradius
    alloc ht amplitude χ₀ m Q P f
  have hZ0:=zero_lt_one.trans hZ
  have hb:=hbase.2 hZ rayM H hH Wslot hW hsW η η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod hN hw hadm hy₂ hl₁ hl₂
  have hz₁:s.W₁ 0=0:=initial_plain_zero p (by norm_num) 0
  have hz₂:s.W₂ 0=0:=initial_plain_zero p (by norm_num) 1
  have hscales:∀i,1≤s.P i:=fun i=>Real.one_le_rpow hZ.le (hw i)
  have hplain:(9/4:ℝ)^2*(s.X₁*s.X₂)≤Z^(2:ℝ):=by
    have hh: s.X₁*s.X₂≤Z:=(plain_product_le_volume s hscales).trans hb.2.2.2.1
    calc
      _≤Z*Z:=mul_le_mul hplainConst hh (mul_pos s.X₁_pos s.X₂_pos).le hZ0.le
      _=_:=by norm_num;ring
  have hcorners:=long_reference_all_corners X₁ X₂ Y₁ Y₂ hY₂ hprod hl₁ hl₂
  exact mainAllocatedFamily_polynomialCaps s W (p.profile 0) (p.profile 1) Z R₀ C
    seed alloc τ ht P hseed hz₁ hz₂ K Tsec (fun _=>volume s) amplitude ξ hK χ₀ m
    Q (1/4) (9/4) a ell mesh loss 2 depth hZ (by norm_num) hR hRcap hC hCcap rfl rfl
    (p.support 0) (p.support 1) le_rfl le_rfl (by norm_num [s,initialInput]) (by norm_num [s,initialInput])
    (fun _=>by norm_num [s,initialInput]) hscales hb.2.1 (by
      intro I hI
      apply hb.2.2.2.2 I
      simpa only [s,finiteColumns,Finset.mem_image,Fintype.mem_piFinset] using hI) hplain hpool hdepth
    (fun q hq i I hI=>hpool.avoids_canonical_slot rayM H (w i) (hwm i) q hq I hI)
    hchar hradius hfour hfixed Y₂ hY₂ hcorners.1 hcorners.2.1 hcorners.2.2.1 hcorners.2.2.2

end
end QRH.Record1252270103Source.Contraction.SelectedMainExceptional
#print axioms QRH.Record1252270103Source.Contraction.SelectedMainExceptional.eventually_initial_first_family_polynomialCaps_mx
