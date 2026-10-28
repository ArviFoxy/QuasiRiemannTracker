/- Mixed source step (L4/L5, collisions): adapted from Collet's `FirstFamilyDictionary`,
`FirstFamilyMask` and `FirstFamilyNewtonPacket` (Record1252270103Source.Admission); changes: the
first-frequency multiplier `u₀` is a parameter (Collet fixes `u₀ = 1`), and the parent character of
the second layer is not asked to equal `columnCharacter`: it carries the dictionary property
`ColumnDict` of the column at `u₀`. For the plain family `u₀ = 1` and the character is the column
character (`columnDict_one`); for a collision family `u₀ = δ³` and the character is the twist
`twistDict (columnCharacter ..) u₀` (`columnDict_twist`).

The Euler mask of the fixed dictionary is the *plain* column modulus in both cases
(`DictFlex`), so every cap on the mask, and the structure `commonMask = geometryRawFixedMask ·
firstSourceMissing`, are unchanged. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyNewtonPacket
import Submissions.arvi_mixed_step.Collision.DictFlex
import Submissions.arvi_mixed_step.Collision.TwistDict

set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 400000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths Filter CompletedGauss CenteredMomentEnergyState
open CenteredMomentFirstSourceConductorCaps
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass Record12518109Raw
open QRH.MixedStep.Collision
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

section Dict
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The dictionary property of a parent character at the multiplier `u₀`.** On the ideals coprime
to the plain column modulus `χ₁` is the fixed natural row at `u₀ ·` (the first frequency of the
column), and `0` elsewhere. -/
def ColumnDict (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ)) (u₀ : O) (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
    (χ₁ : Character) : Prop :=
  ∀ (l : JointSourceLabel), l.1=firstLabel s modifier R seed K Z ξ hK bin j →
    ∀ (G : NaturalRow (childCharacter s.η (dictionaryRay reflected s modifier R seed K Z ξ hK bin j))
      (jointFirstFrequency (!reflected) u₀ (fun l=>(fixedParentUnit (!reflected) s.η l:O)) l))
      (I : Ideal O),
      idealCoeff χ₁ I=if IsCoprime I
        (columnCharacter reflected s modifier R seed K Z ξ hK bin j).modulus
        then idealCoeff G.character I else 0

/-- The plain column character, at `u₀ = 1`. -/
theorem columnDict_one (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ)) (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin)) :
    ColumnDict reflected s modifier R seed K Z ξ hK bin 1 j
      (columnCharacter reflected s modifier R seed K Z ξ hK bin j) :=
  fun l hl G I => actual_joint_first_mask reflected s modifier R seed K Z ξ hK bin j l hl G I

/-- **The collision twist of a column character.** -/
theorem columnDict_twist (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ)) (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
    (u₀ : O) (hu₀ : u₀≠0) :
    ColumnDict reflected s modifier R seed K Z ξ hK bin u₀ j
      (twistDict (columnCharacter reflected s modifier R seed K Z ξ hK bin j) u₀) := by
  intro l hl G I
  have hF₁ : jointFirstFrequency (!reflected) 1 (fun l=>(fixedParentUnit (!reflected) s.η l:O)) l≠0 := by
    apply actual_joint_first_frequency_ne_zero _ _ _ _ one_ne_zero (Units.ne_zero _)
    change Supported l.1.1.1
    rw [hl]
    exact (source s modifier R seed K Z ξ hK bin j.1).hC
  let G₁ := naturalRow (childCharacter s.η (dictionaryRay reflected s modifier R seed K Z ξ hK bin j))
    (jointFirstFrequency (!reflected) 1 (fun l=>(fixedParentUnit (!reflected) s.η l:O)) l) hF₁
  have hz : jointFirstFrequency (!reflected) u₀ (fun l=>(fixedParentUnit (!reflected) s.η l:O)) l=
      u₀*jointFirstFrequency (!reflected) 1 (fun l=>(fixedParentUnit (!reflected) s.η l:O)) l := by
    unfold jointFirstFrequency
    ring
  exact twistDict_dict (columnCharacter reflected s modifier R seed K Z ξ hK bin j) _ G₁
    (fun J=>actual_joint_first_mask reflected s modifier R seed K Z ξ hK bin j l hl G₁ J) u₀ hu₀ G hz I

end Dict

variable {ι α Label : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype Label]
variable (u₀ : O) (hu₀ : u₀≠0)
variable (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hfirst : first r.val.1=firstLabel s modifier R seed K Z ξ hK bin j)
local notation "datum" => d r.val.1
local notation "label" => firstLabel s modifier R seed K Z ξ hK bin j
local notation "unitMap" => (fun l=>(fixedParentUnit (!reflected) s.η l:O))
local notation "baseRay" => dictionaryRay reflected s modifier R seed K Z ξ hK bin j
local notation "colMod" => (columnCharacter reflected s modifier R seed K Z ξ hK bin j).modulus

include hu₀ hfirst in
theorem first_frequency_ne_zero_u :
    jointFirstFrequency (!reflected) u₀ unitMap
      (secondEncodedRow (fun l=>(d l).block) first r)≠0 := by
  apply actual_joint_first_frequency_ne_zero _ _ _ _ hu₀ (Units.ne_zero _)
  change Supported (first r.val.1).1.1
  rw [hfirst]
  exact (source s modifier R seed K Z ξ hK bin j.1).hC

/-- The key of a row at the multiplier `u₀` (Collet's `rawKey` has `u₀ = 1`). -/
def rawKey_u (second : Bool) : NonzeroJointSourceLabel (!reflected) u₀ unitMap :=
  let hf:=first_frequency_ne_zero_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin j d first r hfirst
  let key:=secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unitMap hf
  if second then reflectedNonzeroJointLabel key else key

theorem rawKey_u_one (second : Bool) :
    rawKey_u 1 one_ne_zero reflected s modifier R seed K Z ξ hK bin j d first r hfirst second=
      rawKey reflected s modifier R seed K Z ξ hK bin j d first r hfirst second := rfl

local notation "keyOf" => rawKey_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin j d first r hfirst

include hfirst in
/-- The fixed-dictionary form of the second-layer natural row, at the multiplier `u₀` and for a parent
character with the column dictionary property. The fixed side carries the plain column mask. -/
theorem actual_natural_dictionary_u (second : Bool)
    (hdict : ColumnDict reflected s modifier R seed K Z ξ hK bin u₀ j (datum).input.η)
    (hR : (datum).R≠0)(ψ : RayCharacter) :
    let hf:=first_frequency_ne_zero_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin j d first r hfirst
    let key₀:=secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unitMap hf
    let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((d r.val.1).rows_ne _ r.val.2.2.2.property)
      · exact (d r.val.1).rows_ne _ r.val.2.2.2.property
    let puncture:=(d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let holes:=colMod*puncture
    holes≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((d r.val.1).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary s.η
        (dictionaryRay reflected s modifier R seed K Z ξ hK bin j,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro hf key₀ key z hz puncture holes
  have hp : puncture≠0 := by
    apply mul_ne_zero hR
    dsimp only [puncture]
    split <;> first | exact (d r.val.1).hC.1 | exact (d r.val.1).hD.1
  have hM : colMod≠0 := (columnCharacter reflected s modifier R seed K Z ξ hK bin j).modulus_ne_bot
  refine ⟨mul_ne_zero hM hp,?_⟩
  intro I
  let G:=naturalRow (childCharacter s.η (dictionaryRay reflected s modifier R seed K Z ξ hK bin j))
    (jointFirstFrequency (!reflected) u₀ unitMap (secondEncodedRow (fun l=>(d l).block) first r)) hf
  have hmask (J : Ideal O) : idealCoeff (d r.val.1).input.η J=
      if IsCoprime J colMod then idealCoeff G.character J else 0 :=
    hdict (secondEncodedRow (fun l=>(d l).block) first r) hfirst G J
  cases second
  · exact actual_second_input_dictionary_mask_flex d first r (!reflected) u₀ unitMap hf _ colMod hM G
      hmask ψ (naturalRow _ _ hz) hR I
  · exact actual_second_reflected_input_dictionary_mask_flex d first r (!reflected) u₀ unitMap hf _ colMod
      hM G hmask ψ (naturalRow _ _ hz) hR I

include hfirst in
/-- All moving first and second common masks reduce to the original fixed factor and the first
missing radical (Collet's `actual_common_mask`, at `u₀`). -/
theorem actual_common_mask_u
    (hdict : ColumnDict reflected s modifier R seed K Z ξ hK bin u₀ j (datum).input.η)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (ψ : RayCharacter) :
    let key:=keyOf second
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z];split
      · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
      · exact (datum).rows_ne _ r.val.2.2.2.property
    let puncture:=(datum).R*(if second then (datum).D else (datum).C)
    let commonMask:=geometryRawFixedMask s R*firstSourceMissing (!reflected) label
    commonMask≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((datum).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character commonMask) I := by
  intro key z hz puncture commonMask
  let src:=source s modifier R seed K Z ξ hK bin j.1
  have hfixed : geometryRawFixedMask s R≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))) hR
  have hmissing:=label_missing_nonzero (!reflected) s modifier R seed K Z ξ hK bin j
  have hdR : (datum).R≠0 := by
    rw [hchild]
    exact mul_ne_zero hR (column_supported reflected s modifier R seed K Z ξ hK bin j).1
  refine ⟨mul_ne_zero hfixed hmissing,?_⟩
  intro I
  have hd:=actual_natural_dictionary_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin j
    d first r hfirst second hdict hdR ψ
  apply (hd.2 I).trans
  change idealCoeff (excluded (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
    (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
      (colMod*puncture)) I=_
  have hk : key.val.1=label := by cases second <;> exact hfirst
  have hpairs : key.val.2.1=((datum).C,(datum).D) := by cases second <;> rfl
  have hc₁ : Supported key.val.1.1.1 := by rw [hk];exact src.hC
  have hd₁ : Supported key.val.1.1.2 := by rw [hk];exact src.hD
  have hs₁ : CompletedGauss.primeSupport key.val.1.1.1=CompletedGauss.primeSupport key.val.1.1.2 := by
    rw [hk];exact src.sameSupport
  have hc₂ : Supported key.val.2.1.1 := by rw [hpairs];exact (datum).hC
  have hd₂ : Supported key.val.2.1.2 := by rw [hpairs];exact (datum).hD
  have hs₂ : CompletedGauss.primeSupport key.val.2.1.1=CompletedGauss.primeSupport key.val.2.1.2 := by
    rw [hpairs];exact (datum).sameSupport
  have hm:=actual_joint_common_mask (!reflected) second u₀ unitMap key hc₁ hd₁ hs₁ hc₂ hd₂ hs₂
    (secondFixedDictionary s.η (baseRay,ψ)) (naturalRow _ _ (nonzeroJointSourceRow key).property)
    (geometryRawFixedMask s R) hfixed I
  have hp : colMod=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive*
        activeConductor src.C src.D} :=
    column_modulus reflected s modifier R seed K Z ξ hK bin j
  have hmask : colMod*puncture=
      geometryRawFixedMask s R*(Ideal.span {primeSubsetGenerator
        (fun P : CommonIndex key.val.1.1.1 key.val.1.1.2=>P.val) key.val.1.2.val*
          activeConductor key.val.1.1.1 key.val.1.1.2}*
        ((if !reflected then key.val.1.1.1 else key.val.1.1.2)*
          (if second then key.val.2.1.2 else key.val.2.1.1))) := by
    rw [hp]
    dsimp only [puncture]
    rw [hchild,hk,hpairs]
    change (s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive*
          activeConductor src.C src.D})*((R*(if reflected then src.D else src.C))*
            (if second then (datum).D else (datum).C))=
      (s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*R)*
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive*
          activeConductor src.C src.D}*((if !reflected then src.C else src.D)*
            (if second then (datum).D else (datum).C)))
    have hc : (if reflected then src.D else src.C)=(if !reflected then src.C else src.D) := by
      cases reflected <;> rfl
    rw [hc]
    ring
  rw [hmask]
  simpa only [hk,commonMask] using hm

include hfirst in
/-- Newton assignment divisors remain an explicit common puncture on both sides of the exact
physical dictionary. -/
theorem actual_common_mask_extra_u
    (hdict : ColumnDict reflected s modifier R seed K Z ξ hK bin u₀ j (datum).input.η)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (ψ : RayCharacter) (J : Ideal O) (hJ : J≠0) :
    let key:=keyOf second
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z≠0 := by
      dsimp only [z];split
      · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
      · exact (datum).rows_ne _ r.val.2.2.2.property
    let puncture:=((datum).R*(if second then (datum).D else (datum).C))*J
    let commonMask:=(geometryRawFixedMask s R*J)*firstSourceMissing (!reflected) label
    commonMask≠0 ∧ ∀I : Ideal O,
      idealCoeff (excluded (naturalRow ((datum).τ ψ) z hz).character puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character commonMask) I := by
  intro key z hz puncture commonMask
  have hm:=actual_common_mask_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin j d first r hfirst
    hdict hR hchild second ψ
  have hdR : (datum).R≠0 := by
    rw [hchild]
    exact mul_ne_zero hR (column_supported reflected s modifier R seed K Z ξ hK bin j).1
  have hp : (datum).R*(if second then (datum).D else (datum).C)≠0 := by
    apply mul_ne_zero hdR
    cases second
    · exact (datum).hC.1
    · exact (datum).hD.1
  have heq : (geometryRawFixedMask s R*firstSourceMissing (!reflected) label)*J=commonMask := by
    dsimp only [commonMask]
    ring
  refine ⟨heq ▸ mul_ne_zero hm.1 hJ,?_⟩
  intro I
  have he:=excluded_extra _ _ J hp hm.1 hJ hm.2 I
  rw [heq] at he
  exact he

include hfirst in
/-- The fixed-inducing exclusion is transported with the literal row, including reflection. -/
theorem actual_initialKeep_u
    (hdict : ColumnDict reflected s modifier R seed K Z ξ hK bin u₀ j (datum).input.η)
    (hR : R≠0) (hchild : (datum).R=R*columnIdeal reflected s modifier R seed K Z ξ hK bin j)
    (second : Bool) (ψ : RayCharacter) (Q : Ideal O) :
    initialKeep (secondFixedDictionary s.η (baseRay,ψ)) Q
      (nonzeroJointSourceRow (keyOf second)).val ↔
    (if second then -r.val.2.2.2.val else r.val.2.2.2.val)≠0 ∧
      ¬FixedInducingRow ((datum).τ ψ) Q fixedBadMask 1
        (if second then -r.val.2.2.2.val else r.val.2.2.2.val) := by
  let key:=keyOf second
  let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
  have hz : z≠0 := by
    cases second
    · exact (datum).rows_ne _ r.val.2.2.2.property
    · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
  have hm:=actual_common_mask_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin j d first r hfirst
    hdict hR hchild second ψ
  have hdR : (datum).R≠0 := by
    rw [hchild]
    exact mul_ne_zero hR (column_supported reflected s modifier R seed K Z ξ hK bin j).1
  have hp : (datum).R*(if second then (datum).D else (datum).C)≠0 := by
    apply mul_ne_zero hdR
    cases second
    · exact (datum).hC.1
    · exact (datum).hD.1
  exact natural_initialKeep_of_masked_ideal_eq
    (naturalRow (secondFixedDictionary s.η (baseRay,ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property)
    (naturalRow ((datum).τ ψ) z hz) (nonzeroJointSourceRow key).property hz
    _ _ hm.1 hp (fun I=>(hm.2 I).symm) Q

/-- The marked packet with an extra common Newton puncture (Collet's `eventually_marked_packet_extra`),
at the multiplier `u₀` and for a parent character with the column dictionary property. The mask
`holes` is the plain column modulus times the retained puncture, so its cap does not see `u₀`. -/
theorem eventually_marked_packet_extra_u
    (η₀ : Character)
    (Bfirst Bmask bΦ : ℝ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι α Label : Type}[Fintype ι][DecidableEq ι][Fintype α][DecidableEq α][Fintype Label],
      ∀(reflected second : Bool)(s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(hη : s.η=η₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))(u₀ : O)(hu₀ : u₀≠0)
        (column : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
        (dat : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
        (row : secondLiveRows (fun l=>(dat l).block))
        (hdict : ColumnDict reflected s modifier R seed K Z ξ hK bin u₀ column (dat row.val.1).input.η)
        (hfirst : first row.val.1=firstLabel s modifier R seed K Z ξ hK bin column)
        (hR : (dat row.val.1).R≠0)(ψ : RayCharacter)(J : Ideal O)(hJ : J≠0),
      ((source s modifier R seed K Z ξ hK bin column.1).C.absNorm:ℝ)≤Z^Bfirst→
      ∀(st : NaturalState Z Bmask bΦ)(z : O)(hz : st.radial.keep z),
      st.character=(dat row.val.1).τ ψ→
      st.puncture=((dat row.val.1).R*(if second then (dat row.val.1).D else (dat row.val.1).C))*J→
      z=(if second then -row.val.2.2.2.val else row.val.2.2.2.val)→
      let left:=!reflected
      let unit:=fun l=>(fixedParentUnit left s.η l:O)
      let hf:=first_frequency_ne_zero_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin
        column dat first row hfirst
      let rawKey:=secondEncodedNonzeroRow (fun l=>(dat l).block) first row left u₀ unit hf
      let key:=if second then reflectedNonzeroJointLabel rawKey else rawKey
      let index:=(dictionaryRay reflected s modifier R seed K Z ξ hK bin column,ψ)
      let holes:=(columnCharacter reflected s modifier R seed K Z ξ hK bin column).modulus*st.puncture
      holes≠0 ∧ (holes.absNorm:ℝ)≤Z^(2*Bfirst+Bmask+1) ∧
      (∀I,idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index)
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I) ∧
      (Supported key.val.1.1.1 ∧ key.val.1.1.2≠0 ∧
        Supported key.val.2.1.1 ∧ key.val.2.1.2≠0) ∧
      (primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 ∧
        primeSupport key.val.2.1.1=primeSupport key.val.2.1.2) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (fixedPresentationCost*(η₀.modulus.absNorm:ℝ))] with Z hZ hconstant
  refine ⟨hZ,?_⟩
  intro ι α Label _ _ _ _ _ reflected second s modifier hη R seed K ξ hK bin u₀ hu₀ column dat first row
    hdict hfirst hR ψ J hJ hnorm st z hz hchar hpuncture hrow left unit hf rawKey key index holes
  have hholes : holes≠0 ∧ (holes.absNorm:ℝ)≤Z^(2*Bfirst+Bmask+1) := by
    refine ⟨mul_ne_zero (columnCharacter reflected s modifier R seed K Z ξ hK bin column).modulus_ne_bot
      st.puncture_ne_zero,?_⟩
    have hcap:=column_modulus_cap reflected s modifier R seed K Z ξ hK bin column
    rw [hη] at hcap
    have hZp : 0<Z:=zero_lt_one.trans hZ
    dsimp only [holes]
    simp only [map_mul,Nat.cast_mul]
    calc
      _≤(fixedPresentationCost*(η₀.modulus.absNorm:ℝ)*
          ((source s modifier R seed K Z ξ hK bin column.1).C.absNorm:ℝ)^2)*Z^Bmask :=
        mul_le_mul hcap st.puncture_bound (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)) (sq_nonneg _))
      _≤(Z*(Z^Bfirst)^2)*Z^Bmask := by gcongr
      _=Z^(1:ℝ)*(Z^Bfirst)^2*Z^Bmask := by rw [Real.rpow_one]
      _=Z^(2*Bfirst+Bmask+1) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
        congr 1
        norm_num
        ring
  have hd:=actual_natural_dictionary_u u₀ hu₀ reflected s modifier R seed K Z ξ hK bin column
    dat first row hfirst second hdict hR ψ
  have hmask (I : Ideal O) :
      idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ index) (nonzeroJointSourceRow key).val
        (nonzeroJointSourceRow key).property).character holes) I := by
    have transfer (χ χ' : Character) (u v : O) (hu : u≠0) (hv : v≠0)
        (hc : χ=χ') (hr : u=v) :
        (naturalRow χ u hu).character=(naturalRow χ' v hv).character := by
      subst χ';subst v;rfl
    have hv : (if second then -row.val.2.2.2.val else row.val.2.2.2.val)≠0 :=
      hrow ▸ st.row_ne_zero z hz
    rw [transfer _ _ _ _ _ hv hchar hrow,hpuncture]
    rw [←hη]
    have hp : (dat row.val.1).R*(if second then (dat row.val.1).D else (dat row.val.1).C)≠0 := by
      apply mul_ne_zero hR
      cases second
      · exact (dat row.val.1).hC.1
      · exact (dat row.val.1).hD.1
    have he:=excluded_extra _ _ J hp hd.1 hJ hd.2 I
    have hholesJ : ((columnCharacter reflected s modifier R seed K Z ξ hK bin column).modulus*
        ((dat row.val.1).R*(if second then (dat row.val.1).D else (dat row.val.1).C)))*J=holes := by
      dsimp only [holes]
      rw [hpuncture]
      ring
    rw [hholesJ] at he
    exact he
  have hfirstSupport : Supported key.val.1.1.1 ∧ Supported key.val.1.1.2 ∧
      primeSupport key.val.1.1.1=primeSupport key.val.1.1.2 := by
    have heq : key.val.1=firstLabel s modifier R seed K Z ξ hK bin column := by
      cases second <;> exact hfirst
    rw [heq]
    exact ⟨(source s modifier R seed K Z ξ hK bin column.1).hC,
      (source s modifier R seed K Z ξ hK bin column.1).hD,
      (source s modifier R seed K Z ξ hK bin column.1).sameSupport⟩
  refine ⟨hholes.1,hholes.2,hmask,?_,?_⟩
  · refine ⟨hfirstSupport.1,hfirstSupport.2.1.1,?_⟩
    cases second <;> exact ⟨(dat row.val.1).hC,(dat row.val.1).hD.1⟩
  · refine ⟨hfirstSupport.2.2,?_⟩
    cases second <;> exact (dat row.val.1).sameSupport

end
end QRH.Record1252270103Source.Admission.FirstFamily

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.columnDict_one
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.columnDict_twist
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_natural_dictionary_u
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_common_mask_u
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_common_mask_extra_u
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.actual_initialKeep_u
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.eventually_marked_packet_extra_u
