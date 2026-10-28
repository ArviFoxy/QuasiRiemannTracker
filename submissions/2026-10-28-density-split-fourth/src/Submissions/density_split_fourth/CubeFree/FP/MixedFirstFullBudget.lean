/- Copyright (c) 2026 Sil. Apache-2.0.
The actual first positive energy, with all four numerical suppliers and
the exact two-side reference normalization. 
Modified by Sil (2026-10-26): cube-free first-step budget, balanced (CF (6.4)): alpha is a parameter with 0 <= alpha < 2/3; all four parts at the uncompleted child scale childScale Z kappa n (KL = KR); the exceptional part is WP-J's uniform_fixed_pair_components_balanced at a reference length Lref <= Z^lref (alpha-loss (2/3-alpha)*lref, factor (L/Lref)^(2/3)), under N D <= N C^3, N C <= N D^3; the nonexceptional part has an explicit side exponent supplied by AllocatedSupply; costs are normalized by balancedReference = reference*N G/N Gopp and the pairing is twisted by theta = log_Z(N C/N D); the nonexceptional exponent expo w G Gopp tau W takes the opposite common factor and is gated by PairGate (expo <= enon + log_Z N G - log_Z N Gopp on pairs of equal prime support).
-/
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstExceptionalApplication
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstReferencePair
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstInactiveConductor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.FP.MixedFirstFullBudget
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open ActualEisensteinCubic CenteredMomentRankinRadical
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstMixedAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstWindowBudgets
open CenteredMomentFirstDiscardedEnergy CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSmoothedWindowEnergy
open CenteredMomentGaussEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedFirstLiveSource
open MixedInnerExceptionalBlock
open MixedFirstFourParts MixedFirstActualNonexceptional MixedFirstAllocatedRemainders
open MixedFirstNonexceptionalAllocation MixedFirstReferencePair MixedFirstInactiveConductor
open MixedFirstExceptionalNormalization MixedFirstExceptionalApplication
open MixedHeightEnvelope ReferencePrimeEnclosure MixedCompletedRows
open QuadraticInitialBound
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- These finite controls are selected before the fixed original
character, profiles, heights and every common/allocation label. -/
structure Controls where
  nonexceptionalDegree : ℕ
  nonexceptionalControl : Finset (ℕ×ℕ)
  exceptionalDegree : ℕ
  exceptionalControl : Finset (ℕ×ℕ)
  tailControl : Finset (ℕ×ℕ)

/-- Numerical constants only. No source or energy estimate is a field. -/
structure Constants where
  source : ℝ
  physical : ℝ
  geometry : ℝ
  nonexceptionalCount : ℝ
  zero : ℝ
  tail : ℝ
  kernel : ℝ
  exceptional : ℝ
  exceptionalSum : ℝ
  exceptionalCount : ℝ
  source_pos : 0<source
  physical_pos : 0<physical
  geometry_pos : 0<geometry
  nonexceptionalCount_pos : 0<nonexceptionalCount
  zero_pos : 0<zero
  tail_pos : 0<tail
  kernel_nonneg : 0≤kernel
  exceptional_pos : 0<exceptional
  exceptionalSum_pos : 0<exceptionalSum
  exceptionalCount_pos : 0<exceptionalCount

def canonicalProfile (U : Controls) (c : Constants) (s : Source ι a b)
    (t V : ℝ) : ℝ :=
  c.source*diagonalControl ballProfile*
    (sourceControl U.nonexceptionalControl s.W₁*sourceControl U.nonexceptionalControl s.W₂)^2*
    sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))^U.nonexceptionalDegree

def zeroCost (c : Constants) (s : Source ι a b) (G Dart : Id)
    (Z ε δ X Kchild W : ℝ) : ℝ :=
  (16*Kchild*W^3)*‖paperRadialFourier ballProfile 0‖*
    (c.zero*(G.absNorm:ℝ)^δ*(∏i,s.M i)^2*(profileCap s)^2*X^(1+ε)/
      ((G.absNorm:ℝ)*(Dart.absNorm:ℝ)))

/-- Cube-free: the nonexceptional (second-step) exponent `e` is an explicit argument;
FP's native value is `κ·∑w + 2ε + δ`. -/
def nonexceptionalCost (U : Controls) (c : Constants) (s : Source ι a b)
    (G Dart : Id) (τ : Character)
    (Z δ e t V tp W : ℝ) : ℝ :=
  c.nonexceptionalCount*(G.absNorm:ℝ)^δ*
    fullCost s.P s.M U.nonexceptionalDegree c.physical c.geometry Z
      e (canonicalProfile U c s t V) b s.T tp W Dart s.d*
      (τ.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2

def tailCost (U : Controls) (c : Constants) (s : Source ι a b)
    (G Dart : Id) (Z δ saving : ℝ) : ℝ :=
  c.tail*(G.absNorm:ℝ)^δ*(∏i,s.M i)^2*(profileCap s)^2*
    U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)/
      ((G.absNorm:ℝ)*(Dart.absNorm:ℝ))

/-- Cube-free (CF (6.4), WP-M `balancedBudget`): the balanced side reference
`reference·N G/N Gopp`; the product of the two side references is unchanged. -/
def balancedReference (s : Source ι a b) (τ : Character) (G Gopp : Id) (Z : ℝ) : ℝ :=
  reference τ G Gopp (sourceVolume s) Z*((G.absNorm:ℝ)/(Gopp.absNorm:ℝ))

/-- Four numerical costs, in exactly the order of FourParts.components. The exceptional
entry is WP-J's balanced supplier at the reference length `Lref`, multiplied back by the
balanced reference. -/
def rawCosts (U : Controls) (c : Constants) (s : Source ι a b)
    (η τ : Character) (G Gopp Dart Q : Id) (enon : ℝ)
    (Bnorm Z ε δ εsum Lref t V tp X Kfirst Kchild Cfirst ξfirst κpad W saving : ℝ) : Fin 4→ℝ :=
  ![zeroCost c s G Dart Z ε δ X Kchild W,
    nonexceptionalCost U c s G Dart τ Z δ enon t V tp W,
    balancedReference s τ G Gopp Z*
      (numericalCost s η G Dart Q U.exceptionalDegree U.exceptionalControl
        Bnorm ε δ εsum δ c.kernel c.exceptional c.exceptionalSum c.exceptionalCount
        Z Kfirst Cfirst ξfirst κpad W tp*(s.L/Lref)^(2/3:ℝ)),
    tailCost U c s G Dart Z δ saving]

def normalizedCosts (U : Controls) (c : Constants) (s : Source ι a b)
    (η τ : Character) (G Gopp Dart Q : Id) (enon : ℝ)
    (Bnorm Z ε δ εsum Lref t V tp X Kfirst Kchild Cfirst ξfirst κpad W saving : ℝ) : Fin 4→ℝ :=
  fun i=>rawCosts U c s η τ G Gopp Dart Q enon Bnorm Z ε δ εsum Lref t V tp X
    Kfirst Kchild Cfirst ξfirst κpad W saving i/balancedReference s τ G Gopp Z

/-- From a balanced bound `x/r·(q/p) ≤ y` back to `x ≤ r·(p/q)·y`. -/
theorem le_balanced {x r p q y : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q)
    (h : x/r*(q/p)≤y) : x≤r*(p/q)*y := by
  have hpos : 0<r*(p/q) := by positivity
  calc x=(x/r*(q/p))*(r*(p/q)) := by field_simp
    _≤y*(r*(p/q)) := mul_le_mul_of_nonneg_right h hpos.le
    _=_ := by ring

theorem reference_pos (s : Source ι a b) (τ : Character) (G Gopp : Id)
    (hG : G≠0) (Z : ℝ) (hZ : 0<Z) : 0<reference τ G Gopp (sourceVolume s) Z := by
  have hv := sourceVolume_pos s
  have hτ : 0<(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  unfold reference
  positivity

/-- Elementary sum expansion; the two index sets are independent, so
zero/exceptional and tail/nonexceptional cross terms are included. -/
private theorem sqrt_pair_sum (A B : Fin 4→ℝ) (hA : ∀i,0≤A i) (hB : ∀j,0≤B j) :
    Real.sqrt ((∑i,A i)*(∑j,B j))≤∑i,∑j,Real.sqrt (A i*B j) := by
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _=>hA i))]
  have hleft := CenteredMomentFirstWindowBudgets.sqrt_sum_le Finset.univ A (fun i _=>hA i)
  have hright := CenteredMomentFirstWindowBudgets.sqrt_sum_le Finset.univ B (fun j _=>hB j)
  apply (mul_le_mul hleft hright (Real.sqrt_nonneg _) (by positivity)).trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (Real.sqrt_mul (hA i) (B j)).symm

/-- Structural two-side normalization at INDEPENDENT child scales.
The four numerical bounds in this private helper are discharged below
by the four actual suppliers, not exported as analytic premises. -/
private theorem actual_reference_from_costs (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (seed Dart : Id)
    (η : Character) (m A : O) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (χ ξ : RayCharacter) (F : FixedPair η C D hC E χ ξ)
    (hseedC : seed∣C) (hseedD : seed∣D)
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (windows : Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z tleft tright KL KR W Tsec ξsec : ℝ)
    (hK : 0<K) (hA : 0<A₀) (hB : 0<B₀) (hZ : 1<Z)
    (hKL : 0<KL) (hKR : 0<KR) (hW : 0<W)
    (hwin : ∀i y,windows i y≠0→|y|≤M)
    (hn : block η m A t (sourceColumns s) (sourceCoefficient s ha seed)
      C D hC hD E rows Φ windows K K₀ H₀ A₀ B₀≠0)
    (Q : Id) (msecond : O) (χ₀ : RayCharacter) (left right : Fin 4→ℝ)
    (hleft : ∀i,components s ha hb cover C Dart F.left tleft KL W Tsec Z ξsec Q msecond χ₀ i≤left i)
    (hright : ∀i,components s ha hb cover D Dart F.right tright KR W Tsec Z ξsec Q msecond χ₀ i≤right i)
    (ϑ : ℝ) :
    ‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
      Real.sqrt (actualEnergy s ha D C hC seed Dart F.left tleft KL W*
        actualEnergy s ha C D hD seed Dart F.right tright KR W)≤
    ‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
      (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*
        ∑i : Fin 4,∑j : Fin 4,
          Real.sqrt ((left i/(reference F.left C D (sourceVolume s) Z*Z^ϑ))*
            (right j/(reference F.right D C (sourceVolume s) Z*Z^(-ϑ)))) := by
  have hl0 (i : Fin 4) : 0≤left i :=
    (components_nonneg s ha hb cover C Dart F.left tleft KL W Tsec Z ξsec Q msecond χ₀ i).trans (hleft i)
  have hr0 (i : Fin 4) : 0≤right i :=
    (components_nonneg s ha hb cover D Dart F.right tright KR W Tsec Z ξsec Q msecond χ₀ i).trans (hright i)
  have hl := (actual_energy_four_parts s ha hb cover D C seed Dart hD hC hCD.symm hseedC
    F.left tleft KL W Tsec Z ξsec hKL hW Q msecond χ₀).trans
      (Finset.sum_le_sum (fun i _=>hleft i))
  have hr := (actual_energy_four_parts s ha hb cover C D seed Dart hC hD hCD hseedD
    F.right tright KR W Tsec Z ξsec hKR hW Q msecond χ₀).trans
      (Finset.sum_le_sum (fun i _=>hright i))
  have henergy (G Gopp : Id) (hG : Supported G) (τ : Character) (v Kc : ℝ) (hKc : 0<Kc) :
      0≤actualEnergy s ha Gopp G hG seed Dart τ v Kc W := by
    dsimp only [actualEnergy]
    apply div_nonneg _ hW.le
    have hs := gaussEnergy_hasSum_re Finset.univ
      (CenteredMomentFirstPhysicalSource.element Gopp G hG.1 (sourceColumns s))
      (CenteredMomentFirstPhysicalSource.element_supported Gopp G hG.1 (sourceColumns s))
      (fun I : CenteredMomentFirstPhysicalSource.columns Gopp G hG.1 (sourceColumns s)=>
        originalResidual s ha seed G Dart I*heightCoeff τ v I)
      ballProfile (16*Kc*W^4) (by positivity)
    rw [←hs.tsum_eq]
    exact tsum_nonneg (fun z=>mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  have hz0 : 0<Z := zero_lt_one.trans hZ
  have hrefL0 := reference_pos s F.left C D hC.1 Z hz0
  have hrefR0 := reference_pos s F.right D C hD.1 Z hz0
  -- (6.4): the two side references are twisted by `Z^ϑ` and `Z^(-ϑ)`; their product is unchanged.
  have hrefL : 0<reference F.left C D (sourceVolume s) Z*Z^ϑ :=
    mul_pos hrefL0 (Real.rpow_pos_of_pos hz0 _)
  have hrefR : 0<reference F.right D C (sourceVolume s) Z*Z^(-ϑ) :=
    mul_pos hrefR0 (Real.rpow_pos_of_pos hz0 _)
  let EL := ∑i,left i/(reference F.left C D (sourceVolume s) Z*Z^ϑ)
  let ER := ∑i,right i/(reference F.right D C (sourceVolume s) Z*Z^(-ϑ))
  have hEL : 0≤EL := Finset.sum_nonneg (fun i _=>div_nonneg (hl0 i) hrefL.le)
  have hER : 0≤ER := Finset.sum_nonneg (fun i _=>div_nonneg (hr0 i) hrefR.le)
  have hsumL : (∑i,left i)=(reference F.left C D (sourceVolume s) Z*Z^ϑ)*EL := by
    dsimp only [EL]
    rw [←Finset.sum_div]
    field_simp [hrefL.ne']
  have hsumR : (∑i,right i)=(reference F.right D C (sourceVolume s) Z*Z^(-ϑ))*ER := by
    dsimp only [ER]
    rw [←Finset.sum_div]
    field_simp [hrefR.ne']
  have hroot := Real.sqrt_le_sqrt (mul_le_mul hl hr
    (henergy D C hD F.right tright KR hKR) (Finset.sum_nonneg (fun i _=>hl0 i)))
  rw [hsumL,hsumR] at hroot
  have htw : (reference F.left C D (sourceVolume s) Z*Z^ϑ)*EL*
      ((reference F.right D C (sourceVolume s) Z*Z^(-ϑ))*ER)=
      (reference F.left C D (sourceVolume s) Z*EL)*(reference F.right D C (sourceVolume s) Z*ER) := by
    have hp : Z^ϑ*Z^(-ϑ)=1 := by rw [←Real.rpow_add hz0];simp
    calc _=(reference F.left C D (sourceVolume s) Z*EL)*(reference F.right D C (sourceVolume s) Z*ER)*
          (Z^ϑ*Z^(-ϑ)) := by ring
      _=_ := by rw [hp,mul_one]
  rw [htw] at hroot
  have hphysical := actual_source_reference_pair s ha seed η m A t C D hC hD hCD E χ ξ F
    rows Φ windows K K₀ H₀ A₀ B₀ M Z EL ER hK hA hB hZ hEL hER hwin hn
  have hpref : 0≤‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
      (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm := by
    have := fixedPresentationCost_pos.le
    have := (pairNorm_pos s.hd.1 s.hd.2).le
    positivity
  calc
    _≤‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
        Real.sqrt ((reference F.left C D (sourceVolume s) Z*EL)*
          (reference F.right D C (sourceVolume s) Z*ER)) :=
      mul_le_mul_of_nonneg_left hroot (div_nonneg (norm_nonneg _) (sourceVolume_pos s).le)
    _≤_ := hphysical.trans (mul_le_mul_of_nonneg_left
      (sqrt_pair_sum _ _ (fun i=>div_nonneg (hl0 i) hrefL.le)
        (fun i=>div_nonneg (hr0 i) hrefR.le)) hpref)

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Cube-free pair gate on a nonexceptional exponent (balanced normalization, CF (3.1)):
on pairs with a common prime support, `e G Gopp τ ≤ enon + log_Z N G - log_Z N Gopp`. -/
def PairGate (Z enon : ℝ) (e : Id→Id→Character→ℝ) : Prop :=
  ∀(G Gopp : Id)(τ : Character),CompletedGauss.primeSupport G=CompletedGauss.primeSupport Gopp→
    e G Gopp τ≤enon+Real.logb Z (G.absNorm:ℝ)-Real.logb Z (Gopp.absNorm:ℝ)

/-- **Second-step interface of the first-step budget (cube-free).** The nonexceptional
(allocated) part of one first side is bounded at an arbitrary exponent
`expo w G Gopp τ Wblock` (side data: slot widths, genuine common factor, opposite common
factor, side character, selected scale). The shape is that of FP `uniform_actual_allocated_part`; constants come after the
original character `η₀` and before `Z`. FP's native route is `allocatedSupply_native`;
the cube-free large branch is to be supplied from the grouped second step
(`Second.SideSupply`, Seam B), not from per-label native bounds. -/
def AllocatedSupply (Holes : ℕ) (W : ℝ→ℂ)
    (a b L Lslot Lcap Cap BR BG BH Bcap Meta δG lo hi Lradius Cr : ℝ) (ha : 0<a) (hb : 1≤b)
    (Q : Id) (expo : (ι→ℝ)→Id→Id→Character→ℝ→ℝ) : Prop :=
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃Cs Cp Cg Ccount : ℝ,0<Cs ∧ 0<Cp ∧ 0<Cg ∧ 0<Ccount ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s→
      (s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bcap→
    ∀cover : OriginalEnclosure s,∀G Gopp D : Id,G≠0→(G.absNorm:ℝ)≤Z^BG→Squarefree D→
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      (η.modulus.absNorm:ℝ)≤Z^Meta→0<K→0<Wblock→m≠0→
      ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→frequencyRadius Tsec Z ξ≤Cr*Z^Lradius→
    let A := Cs*diagonalControl ballProfile*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
      sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))^degree
    allocatedPart s ha (zero_le_one.trans hb) cover G D η tp K Wblock Tsec Z ξ Q m χ₀≤
      Ccount*(G.absNorm:ℝ)^δG*
        fullCost s.P s.M degree Cp Cg Z (expo w G Gopp η Wblock) A b s.T tp Wblock D s.d*
        (η.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2

/-- FP's native supply (exponent `κ·∑w + ε + δ + εg`), through the rerouted
`uniform_actual_allocated_part`. -/
theorem allocatedSupply_native
    (N Holes : ℕ) (hι : Fintype.card ι≤N) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bcap Meta ε δ δG lo hi κ Lradius Cr εg ζ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBcap : 0≤Bcap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) (hδG : 0<δG)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg) (hζ : 0<ζ)
    (hMcap : Lradius+Meta+Bcap+ζ≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    AllocatedSupply (ι:=ι) M Hray hHray Holes W a b L Lslot Lcap Cap BR BG BH Bcap Meta δG lo hi
      Lradius Cr ha hb Q (fun (w : ι→ℝ) _ _ _ _=>κ*(∑i,w i)+ε+δ+εg) := by
  have h := uniform_actual_allocated_part (ι:=ι) M Hray hHray N Holes hι W
    a b Mcap L Lslot Lcap Cap BR BG BH Bcap Meta ε δ δG lo hi κ Lradius Cr εg ζ
    hWs hW ha haUpper hb hM hLslot hLcap hCap hBR hBG hBH hBcap hCapb hLordinary
    hε hδ hδG hLradius hCr hεg hζ hMcap hβ hκ Q hQt hQ72 hQM
  obtain ⟨degree,control,h⟩ := h
  refine ⟨degree,control,fun η₀ hη₀=>?_⟩
  obtain ⟨Cs,Cp,Cg,Ccount,h1,h2,h3,h4,hev⟩ := h η₀ hη₀
  refine ⟨Cs,Cp,Cg,Ccount,h1,h2,h3,h4,hev.mono fun Z hZ=>⟨hZ.1,?_⟩⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hs hR hH hholes hHR hX₁ hX₂ hY₁ hY₂
    hsrc cover G _ D
  exact hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hs hR hH hholes hHR hX₁ hX₂ hY₁
    hY₂ hsrc cover G D

/-- All four ACTUAL suppliers, followed by the genuine two-side
reference normalization. There is no energy or source-bound premise.
The remaining inequalities concern only original source geometry and
the chosen physical cutoffs. KL and KR are never identified.

This is the full first positive-source budget, not the final mixed
moment: annular Fourier assembly and its outer finite sums remain. -/
theorem uniform_full_budget
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi α ξsecond saving : ℝ)
    (ha : 0<a) (hb : 1≤b) (hL : 0≤L) (hBH : 0≤BH)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hε : 0<ε) (hδ : 0<δ)
    (hα0 : 0≤α) (hα23 : α<2/3) (hgap : α+2*δ<1) (hξsecond : 0<ξsecond)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (expo : (ι→ℝ)→Id→Id→Character→ℝ→ℝ)
    (hsupply : AllocatedSupply (ι:=ι) M Hray hHray Holes Wslot a b L Lslot Lcap Cap BR BG BH Bsource
      (Bη+BG+ε) δ lo hi Mgeom 1 ha hb Q expo) :
    ∃U : Controls,∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      (s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bsource→poolCap s≤Z^Btail→
      (∏i,s.P i)≤Z^Pexp→(s.Fhole.absNorm:ℝ)≤Z^BH→
    ∀cover : OriginalEnclosure s,∀(η : Character)(C D : Id)(hC : Supported C)(hD : Supported D),
      CompletedGauss.primeSupport C=CompletedGauss.primeSupport D→
      (η.modulus.absNorm:ℝ)≤Z^Bη→(C.absNorm:ℝ)≤Z^BG→(D.absNorm:ℝ)≤Z^BG→
    ∀(E : Finset (CommonIndex C D)),E∈inactiveSubsets C D→
    ∀(χ ξ : RayCharacter)(F : FixedPair η C D hC E χ ξ),
    ∀(Kfirst Tfirst Cfirst ξfirst κpad W : ℝ),0<Kfirst→0<W→1≤Cfirst→0≤ξfirst→
      Tfirst≤Cfirst*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s)→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀Dart : Id,Squarefree Dart→Dart≠0→(Dart.absNorm:ℝ)≤Z^Btail→
    ∀(tleft tright Tsecond X : ℝ),0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→
      1≤X→(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤X→
      X≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→Tsecond≤Z^Btail→
    ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n→
    (D.absNorm:ℝ)≤(C.absNorm:ℝ)^3→(C.absNorm:ℝ)≤(D.absNorm:ℝ)^3→
    ∀Lref lref : ℝ,0<Lref→Lref≤s.L→0≤lref→Lref≤Z^lref→
    let KL:=MixedFirstExceptionalWindow.childScale Z κpad n
    let KR:=MixedFirstExceptionalWindow.childScale Z κpad n
    KL≤Z^Btail→KR≤Z^Btail→X^2/(16*KL*W^4)≤Tsecond→X^2/(16*KR*W^4)≤Tsecond→
    let left:=rawCosts U c s η F.left C D Dart Q (expo w C D F.left W) (normExponent L Pexp ε)
      Z ε δ (ε+(2/3-α)*lref) Lref t V tleft X Kfirst KL Cfirst ξfirst κpad W saving
    let right:=rawCosts U c s η F.right D C Dart Q (expo w D C F.right W) (normExponent L Pexp ε)
      Z ε δ (ε+(2/3-α)*lref) Lref t V tright X Kfirst KR Cfirst ξfirst κpad W saving
    (∀i,components s ha (zero_le_one.trans hb) cover C Dart F.left tleft KL W Tsecond Z ξsecond Q msecond χ₀ i≤left i) ∧
    (∀i,components s ha (zero_le_one.trans hb) cover D Dart F.right tright KR W Tsecond Z ξsecond Q msecond χ₀ i≤right i) ∧
    ∀seed : Id,seed∣C→seed∣D→∀(m A : O)(tphys : ℝ)(rows : Finset O)(Φ : 𝓢(ℝ,ℂ))
      (windows : Fin 4→ℝ→ℂ)(K₀ H₀ A₀ B₀ Mwindow : ℝ),0<A₀→0<B₀→
      (∀i y,windows i y≠0→|y|≤Mwindow)→
      block η m A tphys (sourceColumns s) (sourceCoefficient s ha seed)
        C D hC hD E rows Φ windows Kfirst K₀ H₀ A₀ B₀≠0→
    ‖scalar C D hC E Kfirst A₀ B₀‖/sourceVolume s*
      Real.sqrt (actualEnergy s ha D C hC seed Dart F.left tleft KL W*
        actualEnergy s ha C D hD seed Dart F.right tright KR W)≤
    ‖inactiveWeight C D E‖*(Real.exp Mwindow/(a^2/pairNorm s.d))*fixedPresentationCost*Kfirst*
      (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*
        ∑i : Fin 4,∑j : Fin 4,
          Real.sqrt ((left i/balancedReference s F.left C D Z)*
            (right j/balancedReference s F.right D C Z)) := by
  obtain ⟨Jn,cn,hn⟩ := hsupply
  obtain ⟨Czero,hCzero,hzero⟩ := uniform_allocated_zero N ε δ hε hδ
  obtain ⟨ct,Ctail,hCtail,htail⟩ := uniform_allocated_discarded N Btail ξsecond saving δ hBtail hξsecond hδ
  obtain ⟨Je,ce,hce,Ckernel,hCkernel,he⟩ := uniform_fixed_pair_components_balanced N
    α a b ε δ ε δ ε L Pexp Bη BR BG BH Mgeom
    hα0 hα23 ha (zero_le_one.trans hb) hε hδ hgap hε hδ hε hL hPexp hBH hMgeom
  obtain ⟨Ae,Csum,CcountE,hAe,hCsum,hCcountE,he⟩ := he Q (NeZero.ne Q) hQt hQ72
  let U : Controls:=⟨Jn,cn,Je,ce,ct⟩
  refine ⟨U,?_⟩
  intro η₀ hη₀
  obtain ⟨Cs,Cp,Cg,CcountN,hCs,hCp,hCg,hCcountN,hn⟩ := hn η₀ hη₀
  let c : Constants:=⟨Cs,Cp,Cg,CcountN,Czero,Ctail,Ckernel,Ae,Csum,CcountE,
    hCs,hCp,hCg,hCcountN,hCzero,hCtail,hCkernel,hAe,hCsum,hCcountE⟩
  have hfixed : ∀ᶠZ : ℝ in atTop,fixedPresentationCost≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) fixedPresentationCost
  refine ⟨c,?_⟩
  filter_upwards [hn,htail,he,hfixed] with Z hn htail he hfixed
  obtain ⟨hZ,hn⟩ := hn
  refine ⟨hZ,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hR hH hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD hη hCcap hDcap
    E hE χ ξ F Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Dart hDart hDart0 hDartCap tleft tright Tsecond X hT hTcap
    hX hXcap hXupper hWupper hWinv hTupper n hret
    hDC3 hCD3 Lref lref hLref0 hLrefL hlref hLrefZ KL KR hKLcap hKRcap hTL hTR left right
  have hz := zero_lt_one.trans hZ
  have hKL : 0<KL := by
    dsimp only [KL,MixedFirstExceptionalWindow.childScale];exact Real.rpow_pos_of_pos hz _
  have hKR : 0<KR := hKL
  have hXpos : 0<X := zero_lt_one.trans_le hX
  have hCtail : (C.absNorm:ℝ)≤Z^Btail := hCcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hBGtail)
  have hDtail : (D.absNorm:ℝ)≤Z^Btail := hDcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hBGtail)
  have hmod : (F.left.modulus.absNorm:ℝ)≤Z^(Bη+BG+ε) ∧
      (F.right.modulus.absNorm:ℝ)≤Z^(Bη+BG+ε) := by
    have hc := fixed_pair_common_caps η C D hC hD.1 E hE χ ξ F
    have hbound : fixedPresentationCost*(η.modulus.absNorm:ℝ)*min (C.absNorm:ℝ) (D.absNorm:ℝ)
        ≤Z^(Bη+BG+ε) := by
      calc
        _≤Z^ε*Z^Bη*Z^BG :=
          mul_le_mul (mul_le_mul hfixed hη (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _))
            ((min_le_left _ _).trans hCcap)
            (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
        _=_ := by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
    exact ⟨hc.1.trans hbound,hc.2.trans hbound⟩
  have hTcapHalf : Tsecond≤Z^(Mgeom-ξsecond/2) := hTcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hradius : frequencyRadius Tsecond Z ξsecond≤Z^Mgeom := by
    unfold frequencyRadius
    calc
      _≤Z^(Mgeom-ξsecond/2)*Z^(ξsecond/2) :=
        mul_le_mul_of_nonneg_right hTcapHalf (Real.rpow_nonneg hz.le _)
      _=_ := by rw [←Real.rpow_add hz];congr 1;ring
  have hnonex := hn θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    s hcanonical hR hH hholes hHR hX₁ hX₂ hY₁ hY₂ hsource cover
  have hnl := hnonex C D Dart hC.1 hCcap hDart F.left tleft KL W Tsecond ξsecond msecond χ₀
    hmod.1 hKL hWblock hm hml hm2 (by simpa only [one_mul] using hradius)
  have hnr := hnonex D C Dart hD.1 hDcap hDart F.right tright KR W Tsecond ξsecond msecond χ₀
    hmod.2 hKR hWblock hm hml hm2 (by simpa only [one_mul] using hradius)
  have hzL := hzero ι a b s hcard ha (zero_le_one.trans hb) cover C Dart hC.1 hDart0
    F.left tleft X KL W hX hXcap hKL.le hWblock.le
  have hzR := hzero ι a b s hcard ha (zero_le_one.trans hb) cover D Dart hD.1 hDart0
    F.right tright X KR W hX hXcap hKR.le hWblock.le
  have htL := htail.2 ι a b s hcard ha (zero_le_one.trans hb) cover C Dart hC.1 hDart0
    hCtail hDartCap F.left tleft KL W X Tsecond hKL hWblock hXpos hpool hXcap hXupper
    hKLcap hWupper hWinv hTupper hTL
  have htR := htail.2 ι a b s hcard ha (zero_le_one.trans hb) cover D Dart hD.1 hDart0
    hDtail hDartCap F.right tright KR W X Tsecond hKR hWblock hXpos hpool hXcap hXupper
    hKRcap hWupper hWinv hTupper hTR
  have hex := he.2 ι s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR hF η C D hC hD hCD
    hη hCcap hDcap E χ ξ F Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst
    hξfirst hfirst χ₀ msecond hm hml hm2 Dart hDart hDart0 tleft tright Tsecond ξsecond
    hT hTcapHalf n hret hDC3 hCD3 Lref lref hLref0 hLrefL hlref hLrefZ
  have hrefL := reference_pos s F.left C D hC.1 Z hz
  have hrefR := reference_pos s F.right D C hD.1 Z hz
  have hNC : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (QRH.Record1252270103KernelMass.ideal_norm_one_le hC.1)
  have hND : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (QRH.Record1252270103KernelMass.ideal_norm_one_le hD.1)
  have heL := le_balanced hrefL hNC hND hex.1
  have heR := le_balanced hrefR hND hNC hex.2
  have hl : ∀i,components s ha (zero_le_one.trans hb) cover C Dart F.left tleft
      KL W Tsecond Z ξsecond Q msecond χ₀ i≤left i := by
    intro i
    fin_cases i
    · exact hzL
    · change allocatedPart s ha (zero_le_one.trans hb) cover C Dart F.left tleft
        KL W Tsecond Z ξsecond Q msecond χ₀ ≤
        nonexceptionalCost U c s C Dart F.left Z δ (expo w C D F.left W) t V tleft W
      simpa only [nonexceptionalCost,canonicalProfile,U,c,
        Controls.nonexceptionalDegree,Controls.nonexceptionalControl,Constants.source,
        Constants.physical,Constants.geometry,Constants.nonexceptionalCount] using hnl
    · change components s ha (zero_le_one.trans hb) cover C Dart F.left tleft
        KL W Tsecond Z ξsecond Q msecond χ₀ 2 ≤
        balancedReference s F.left C D Z *
          (numericalCost s η C Dart Q Je ce (normExponent L Pexp ε)
            ε δ (ε+(2/3-α)*lref) δ Ckernel Ae Csum CcountE Z Kfirst Cfirst ξfirst κpad W tleft*
            (s.L/Lref)^(2/3:ℝ))
      exact heL
    · exact htL
  have hr : ∀i,components s ha (zero_le_one.trans hb) cover D Dart F.right tright
      KR W Tsecond Z ξsecond Q msecond χ₀ i≤right i := by
    intro i
    fin_cases i
    · exact hzR
    · change allocatedPart s ha (zero_le_one.trans hb) cover D Dart F.right tright
        KR W Tsecond Z ξsecond Q msecond χ₀ ≤
        nonexceptionalCost U c s D Dart F.right Z δ (expo w D C F.right W) t V tright W
      simpa only [nonexceptionalCost,canonicalProfile,U,c,
        Controls.nonexceptionalDegree,Controls.nonexceptionalControl,Constants.source,
        Constants.physical,Constants.geometry,Constants.nonexceptionalCount] using hnr
    · change components s ha (zero_le_one.trans hb) cover D Dart F.right tright
        KR W Tsecond Z ξsecond Q msecond χ₀ 2 ≤
        balancedReference s F.right D C Z *
          (numericalCost s η D Dart Q Je ce (normExponent L Pexp ε)
            ε δ (ε+(2/3-α)*lref) δ Ckernel Ae Csum CcountE Z Kfirst Cfirst ξfirst κpad W tright*
            (s.L/Lref)^(2/3:ℝ))
      exact heR
    · exact htR
  refine ⟨hl,hr,?_⟩
  intro seed hseedC hseedD m A tphys rows Φ windows K₀ H₀ A₀ B₀ Mwindow hA hB hwin hblock
  -- CF (6.4): twist by `ϑ = log_Z(N C/N D)`, i.e. the balanced references
  have h := actual_reference_from_costs s ha (zero_le_one.trans hb) cover seed Dart η m A tphys
    C D hC hD hCD E χ ξ F hseedC hseedD rows Φ windows
    Kfirst K₀ H₀ A₀ B₀ Mwindow Z tleft tright KL KR W Tsecond ξsecond
    hKfirst hA hB hZ hKL hKR hWblock hwin hblock Q msecond χ₀ left right hl hr
    (Real.logb Z ((C.absNorm:ℝ)/(D.absNorm:ℝ)))
  have hϑ : Z^(Real.logb Z ((C.absNorm:ℝ)/(D.absNorm:ℝ)))=(C.absNorm:ℝ)/(D.absNorm:ℝ) :=
    Real.rpow_logb hz hZ.ne' (div_pos hNC hND)
  have hϑ' : Z^(-Real.logb Z ((C.absNorm:ℝ)/(D.absNorm:ℝ)))=(D.absNorm:ℝ)/(C.absNorm:ℝ) := by
    rw [Real.rpow_neg hz.le,hϑ,inv_div]
  rw [hϑ,hϑ'] at h
  exact h

end
end QRH.DensitySplitThird.CubeFree.FP.MixedFirstFullBudget
