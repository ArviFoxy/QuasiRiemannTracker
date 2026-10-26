/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
/- Repeated marks: fork of Record1252270103Source.High.GlobalPhysicalBalancedCofactor (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
/- Mixed step (L4/L5, F4): fork of Fork.Record1252270103Source.High.GlobalPhysicalBalancedCofactor
(PR 76 fork of Hailey Collet's module, Apache-2.0); changes: two parents and the δ-shift.
* The first layer (columns, labels, keys, the balanced first mass and its hypotheses) is read from
  `s₀ : Input α₀` with `modifier₀`; the datum, slots, `T` and `w σ v θ` live on the second-layer slot
  type `α`. Both cardinalities are bounded by `N`.
* The side is read at a free volume `Av` (the second-layer volume `logb Z (volume s)` at the call
  site), with `|Av| ≤ B`.
* The mass is the shifted mass `Z^(amp l - poolAmp l) * balancedFirstHighMass … s₀ …`, bounded by
  `QRH.MixedStep.Downstream.shifted_high_mass_mx` under
  `hshift : amp l - poolAmp l ≤ logb Z (volume s₀) - Av + shiftLoss`; the conclusion gains `+shiftLoss`. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalBalancedCofactor
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalSelectedCofactor
import Submissions.arvi_mixed_step.Downstream.Shift
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.High.ModifiedAllPositive
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion HeckeInverseAmplification
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance modifiedBalancedCofactorTauFinite_rm_mx : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_modified_balanced_cofactor_family_uniform_tau_rm_mx {α₀ α : Type} [Fintype α₀] [DecidableEq α₀] [Fintype α] [DecidableEq α]
    (ηanchor η₀ : Character)
    (sourceB sourceLam sourceCap sourceMesh : ℝ)
    (hB0 : 22/23≤sourceB) (hB1 : sourceB≤1) (hlam : 1<sourceLam) (hh0 : 0≤sourceCap) (hh1 : sourceCap<1)
    (setup : DensityCountingSetup) (W : ℝ→ℂ)
    (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ) (hδ : 0<δ)
    (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource ⟨sourceB,sourceLam,0,sourceB,0,sourceCap⟩ sourceMesh εm)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2≤bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
    (hbudget : 288*e+8*κ+2*ηw≤ε/2)
    (hεslot : 0<εslot) (hηslot : 0≤ηslot)
    (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (qlo Q mesh : ℝ) (hqlo : 0<qlo) (hQ : qlo≤Q)
    (hQroot : Q/12≤Broot) (hdlo : dmin≤qlo/2+δ)
    (hdsource : Q+Bmask+δ≤dmax)
    (hrlower : rmin≤wmin/dmax) (hmesh : 0≤mesh)
    (hmeshmax : mesh≤sourceMesh)
    (hmeshR : mesh≤Rwidth)
    (B loss : ℝ) (hB : 0≤B) (hQB : Q≤B) (hloss : 0<loss)
    (loMass εmass : ℝ) (hloMass : 0<loMass) (hεmass : 0≤εmass)
    (Smax ap bp δrestore Brestore : ℝ) (hap : 0<ap) (hδrestore : 0<δrestore)
    (hBrestore : 0≤Brestore) (N : ℕ) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧∃J : ℕ,∀τ : ℝ,0<τ→τ<dmin/2→4*τ<dmin*ηw→2*τ<dmin*ηslot→
      ∀P : HighSourceParameters,P.Wslot=W→P.τ=τ→P.e=e→
      (33/50)≤P.σmin→P.σmax≤(33/50)→2*B+P.Bmask+1≤Bmask→
      P.profileBound=bound→P.B₀=2→8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
      ∃control : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s₀ : Input α₀)(modifier₀ : CenteredMomentAddedZeroUniform.Tuple α₀→ℂ)(_hη : s₀.η=ηanchor)
        (R seed : Ideal O)(Wa : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=FirstFamily.columnCharacter reflected s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter)(punctureExtra : κ→Ideal O)(hExtra : ∀l,punctureExtra l≠0),
      let left := !reflected
      let unit := fun l=>(Record12518109Raw.fixedParentUnit left s₀.η l:O)
      let hf := fun l=>FirstFamily.first_frequency_ne_zero reflected s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left 1 unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      let core := fun l=>(Record12518109GainWholeGeometry.wholeRegularDictionary M H hH
        (secondFixedDictionary ηanchor (FirstFamily.dictionaryRay reflected s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l),ψ l)) η₀).exceptionalCore (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1
        ∀(a rootError width Bbox target reserve : ℝ) (i : ℕ),
      3/4  ≤  a → a  ≤  7/8 → 0<width →0≤rootError→
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ)
        (slots : κ→Finset α)(w σ v : α→ℝ)(t : κ→ℝ)(θ : α→RayQuotient.Characters M H),
      (∀l∈labels,∀j,-Bbox ≤ x l j ∧ x l j ≤ Bbox) →
      (∀l∈labels,0 ≤ x l 2 ∧ x l 2+width ≤ Q) →
      (∀l∈labels,0 ≤ coeff l) → (∀l∈labels,coeff l ≤ Z^(x l 0)) →
      Squarefree seed→s₀.W₁ 0=0→s₀.W₂ 0=0→sourceRadius s₀≤Z^B→
      ∀(Av:ℝ),|Av|≤B→loMass≤s₀.lower→
      (∀x,s₀.W₁ x≠0→ap≤x)→(∀x,s₀.W₂ x≠0→ap≤x)→
      ∀(amp poolAmp:κ→ℝ)(shiftLoss:ℝ),
      (∀l∈labels,amp l-poolAmp l≤Real.logb Z (volume s₀.toData)-Av+shiftLoss)→
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=((datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*punctureExtra l)
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l))  ≤  Z^(x l 2) ∧
        a  ≤  HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          ((3*i : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left 1 unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ)  ≤  Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ)  ≤  Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ)  ≤  Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^(x l 1)) →
      (i:ℝ) ≤ Z^P.τ → i ≤ I →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) →(∀j,w j≤mesh*dmin) →(∑j,w j)≤Smax →
      (∀l∈labels,∀j∈slots l,wmin≤w j) →
      (∀j,P.σmin≤σ j) →(∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      dmax*(155*ε+mesh+εm+(3/4)*ζ+η)+δ+2*binWidth*Smax≤rootError →
      binWidth≤(2*a-1)/2 →
      (∀l∈labels,retainedHighExponent (2*a-1)
        (fun q=>if selectedHighSector (core l) (x l 2) qlo=.regular then QRH.RepeatedMarks.Source.gainC (2*a-1) sourceB sourceLam sourceCap
          (∑j∈slots l,w j) q else sectorSharpGain (selectedHighSector (core l) (x l 2) qlo) (2*a-1) (∑j∈slots l,w j) qlo q) (x l)≤balancedGeometrySide reflected Av
        (CoupledFirst.geometryExponents s₀ modifier₀ R seed (Z^D) Z ξ (column l).1.val)+target-reserve) →
      ∀(ι : κ→Type)[∀l,Fintype (ι l)](schild : ∀l,Input (ι l))
        (A₁ A₂ Rchild : κ→Ideal O)(Snew Anew : Finset (Ideal O))(T : Finset α)
        (p : κ→Profiles ap bp)(b Kcontrol : ℝ),
      Fintype.card α₀≤N→Fintype.card α≤N→0≤b→bp≤b→0≤Kcontrol→GoodPair (newtonDivisorPair Snew Anew)→
      (∀l∈labels,A₁ l≠0)→(∀l∈labels,A₂ l≠0)→(∀l∈labels,A₁ l*A₂ l∣Rchild l)→
      (∀l∈labels,(st l).puncture=Rchild l*((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2))→
      (∀l∈labels,(st l).width≤P.Mcap)→
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0)→
      (∀j,w j/P.d≤P.Rwidth)→
      (∀j∈T,∀I∈CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)),
        IsCoprime I ((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2))→
      (∀l∈labels,(schild l).W₁=((p l).profile 0:ℝ→ℂ))→
      (∀l∈labels,(schild l).W₂=((p l).profile 1:ℝ→ℂ))→
      (∀l∈labels,(schild l).X₁≤Z^(P.d*P.Rplain) ∧ (schild l).X₂≤Z^(P.d*P.Rplain) ∧
        (schild l).Y₁≤Z^(P.d*P.Rplain) ∧ (schild l).Y₂≤Z^(P.d*P.Rplain))→
      (∀l∈labels,b^2*(schild l).X₁*(schild l).X₂≤Z^Brestore)→
      (∀l∈labels,((p l).control control)^2≤Kcontrol)→
      (∀l∈labels,(schild l).X₁*(schild l).X₂≤Z^(x l 3-∑j∈T,w j))→
      (∀l∈labels,slots l=largeSlots T w wmin)→
      (∑l∈labels,(Z^(amp l-poolAmp l)*CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed Wa D Z ξ εmass hK bin (column l))*
        ‖newtonCofactorPlain (schild l) (A₁ l) (A₂ l) (Rchild l) b Snew Anew (st l).character (t l) (z l)*
        (∏j:T,normalizedSlot (st l).character (fixedBadMask*idealGenerator (Rchild l)) 1 (z l)
          (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t l) (Z^(w j)))‖^2*coeff l)≤
      geometryHighFactor reflected (geometrySupportConstant N loMass ap ap) bin*
        cofactorRestorationCost δrestore Brestore Z*C*Kcontrol*
        ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
        (1+rawGeometryHeight Z τ I)^J*
        Z^(target-reserve+4*width+loss+rootError+2*P.εplain*P.d+(2*P.εslot*P.d)*N+B*εmass+shiftLoss) := by
  obtain ⟨bound,hbound,J,hsource⟩:=actual_modified_selected_cofactor_family_uniform_tau_rm_mx (α₀:=α₀) (α:=α) M H hH
    ηanchor η₀ sourceB sourceLam sourceCap sourceMesh hB0 hB1 hlam hh0 hh1
    setup W bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot I δ Bmask Broot wmin
    hδ hBmask hBroot hwmin hparentSource hWs hW hbΦ hrad hbin hη hζ hεm hdmin hdmax hrmin hRw
    hε hεsmall he he' hκ hκ' hηw hbudget hεslot hηslot hslotBudget hgap hβ
    qlo Q mesh hqlo hQ hQroot hdlo hdsource hrlower hmesh hmeshmax hmeshR
    B loss hB hQB hloss Smax ap bp δrestore Brestore hap hδrestore hBrestore N
  refine ⟨bound,hbound,J,?_⟩
  intro τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain
  obtain ⟨control,C,hC,hcount⟩:=hsource τ hτ hτzero hτheight hheight P hPW hPτ hPe hPlo hPhi hholes hpeq hB₀ hslot hplain
  refine ⟨control,C,hC,?_⟩
  filter_upwards [hcount] with Z hc
  refine ⟨hc.1,?_⟩
  intro κ DataLabel _ _ reflected second s₀ modifier₀ hηs R seed Wa D ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    left unit hf rawKey key core a rootError width Bbox target reserve i ha ha' hwidthbin hroot0
    hinj labels x coeff slots w σ v t θ hx hq hcoeff0 hcoeff hseed hz₁ hz₂ hsource Av hAbox hlower hs₁ hs₂ amp poolAmp shiftLoss hshift st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi hiI
    hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq hrootError hνbin hpoint
    ι _ schild A₁ A₂ Rchild Snew Anew T p b Kcontrol hN₀ hN hb hbp hKcontrol hd hA₁ hA₂ hAR hchildpuncture
    hwidth hradial hwr havoid hW₁ hW₂ hscales hcut hcontrol hbase hlargeSlots
  have hZ:1<Z:=by linarith [hc.1]
  have hzpos:0<Z:=zero_lt_one.trans hZ
  let side:=fun l=>balancedGeometrySide reflected Av
    (CoupledFirst.geometryExponents s₀ modifier₀ R seed (Z^D) Z ξ (column l).1.val)
  let factor:=geometryHighFactor reflected (geometrySupportConstant N loMass ap ap) bin
  let scale:=factor*Z^(B*εmass+shiftLoss)
  let mass:=fun l=>Z^(amp l-poolAmp l)*CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed Wa D Z ξ εmass hK bin (column l)
  let xc:=fun l=>compensatedHighCoordinates (x l) (side l)
  let cc:=fun l=>mass l*coeff l/scale
  have hmass0 (l:κ):0≤mass l:=mul_nonneg (Real.rpow_nonneg hzpos.le _)
    (CoupledFirst.balanced_first_high_mass_nonneg reflected s₀ modifier₀ R seed Wa D Z ξ εmass hK bin (column l))
  have hfactor:0<factor:=geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N loMass ap ap hloMass hap hap)
  have hscale:0<scale:=mul_pos hfactor (Real.rpow_pos_of_pos hzpos _)
  have hsbox (l:κ):|side l|≤5*B := by
    apply balanced_geometry_side_box reflected _ B _ hB hAbox
    intro j
    have hn:=CoupledFirst.actual_geometry_norm_caps s₀ modifier₀ R seed (Z^D) Z ξ B
      hseed hz₁ hz₂ hsource (column l).1.val j
    exact ⟨Real.logb_nonneg hZ hn.1,(Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn.1)).mpr hn.2⟩
  have hcc (l:κ)(hl:l∈labels):cc l≤Z^(xc l 0) := by
    apply (div_le_iff₀ hscale).mpr
    have hm:=QRH.MixedStep.Downstream.shifted_high_mass_mx reflected N loMass ap hloMass hap s₀ modifier₀ R seed Wa D Z ξ B εmass
      hZ hK hεmass hN₀ hlower hseed hz₁ hz₂ hsource hs₁ hs₂ bin (column l) Av (amp l) (poolAmp l) shiftLoss (hshift l hl)
    have hh:=compensated_high_coefficient Z (mass l) (coeff l) factor (B*εmass+shiftLoss) (side l) (x l)
      hzpos (hmass0 l) hm (hcoeff l hl)
    simpa only [scale,xc,mul_comm] using hh
  have hxc (l:κ)(hl:l∈labels):∀j,-(Bbox+5*B)≤xc l j ∧ xc l j≤Bbox+5*B:=
    compensated_high_coordinate_box (x l) (side l) Bbox (5*B) (hx l hl) (hsbox l)
  have hcc0 (l:κ)(hl:l∈labels):0≤cc l:=div_nonneg (mul_nonneg (hmass0 l)
    (hcoeff0 l hl)) hscale.le
  have hxe (l:κ):highExponentValue (2*a-1) (xc l)=highExponentValue (2*a-1) (x l)-side l:=
    compensated_high_exponent (2*a-1) (side l) (x l)
  have heq (l:κ)(j:Fin 4)(hj:j≠0):xc l j=x l j:=by
    simp [xc,compensatedHighCoordinates,childHighCoordinates,hj]
  have hp (l:κ)(hl:l∈labels):retainedHighExponent (2*a-1)
      (fun q=>if selectedHighSector (core l) (xc l 2) qlo=.regular then QRH.RepeatedMarks.Source.gainC (2*a-1) sourceB sourceLam sourceCap
        (∑j∈slots l,w j) q else sectorSharpGain (selectedHighSector (core l) (xc l 2) qlo) (2*a-1) (∑j∈slots l,w j) qlo q)
      (xc l)≤target-reserve := by
    have hh:=hpoint l hl
    dsimp only [retainedHighExponent] at hh ⊢
    rw [hxe,heq l 2 (by decide)]
    change highExponentValue (2*a-1) (x l)-_≤side l+target-reserve at hh
    linarith only [hh]
  have hh:=hc.2 reflected second s₀ modifier₀ hηs R seed (Z^D) ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    a rootError width (Bbox+5*B) target reserve i ha ha' hwidthbin hroot0 hinj
    labels xc cc slots w σ v t θ hxc
    (fun l hl=>by simpa only [heq l 2 (by decide)] using hq l hl)
    hcc0 hcc st hQM hQη z hz hchar hpuncture hrow
    (fun l hl=>by simpa only [heq l 2 (by decide)] using hzero l hl)
    hsupport hnorm (fun l hl=>by simpa only [heq l 1 (by decide)] using hmissing l hl)
    hi hiI hupper hw hwm hsupply hsmallSlots hσlo hσhi hfreq hplainfreq hrootError hνbin hp
    ι schild A₁ A₂ Rchild Snew Anew T p b Kcontrol hN hb hbp hKcontrol hd hA₁ hA₂ hAR hchildpuncture
    hwidth hradial hwr havoid hW₁ hW₂ hscales hcut hcontrol
    (fun l hl=>by simpa only [heq l 3 (by decide)] using hbase l hl) hlargeSlots
  have hpaid:=mul_le_mul_of_nonneg_left hh hscale.le
  calc
    _=scale*(∑l∈labels,‖newtonCofactorPlain (schild l) (A₁ l) (A₂ l) (Rchild l) b Snew Anew (st l).character (t l) (z l)*
        (∏j:T,normalizedSlot (st l).character (fixedBadMask*idealGenerator (Rchild l)) 1 (z l)
          (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t l) (Z^(w j)))‖^2*cc l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      dsimp only [cc,mass]
      field_simp [hscale.ne']
    _≤_:=hpaid
    _=_:=by dsimp only [scale,factor];simp only [Real.rpow_add hzpos];ring

end
end QRH.Record1252270103Source.High.ModifiedAllPositive
#print axioms QRH.Record1252270103Source.High.ModifiedAllPositive.actual_modified_balanced_cofactor_family_uniform_tau_rm_mx
