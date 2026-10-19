/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Cycle63.Marked.WholeBufferedMax
import Candidate.Uneven.MixedBootstrapActualMax
import Candidate.Uneven.MixedBootstrapFamilyMaximum
import Candidate.Cycle63.Marked.WholeNaturalBatch
import Candidate.Cycle63.Marked.WholeFamilyMaximum
import Candidate.Cycle63.Marked.Route.ActualMaxWeighted

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.MixedBootstrapPlain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤  H)

theorem actual_whole_max_weighted_fixedmesh {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm binWidth ηloss : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<ηloss)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃J : ℕ,∀(dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin ≤  dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε ≤ 1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw ≤ 1) (hηw : 0 ≤  ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw ≤  ε/2),
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin ≤  d → d ≤  dmax →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀s∈slots,0<w s) → (∀s∈slots,(33/50:ℝ) ≤  σ s) → (∀s∈slots,σ s ≤  (33/50:ℝ)) →
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ) ≤  Z^d) →
      (∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤  Z^d) →
      (∀u∈rows,∀j,initialKeep (MixedBootstrapNaturalBases.base M H hH ηcoarse η₀ u₀ hu₀ R₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val) →
      (∀s∈slots,∀j,
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (MixedBootstrapNaturalBases.base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)<(Z^d)^(w s)) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow (excluded F₀.character R₀) u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i ≤  I →
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      0 ≤  mesh → mesh ≤  markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈slots,w s ≤  mesh) →
      0 ≤  height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ ≤  height →
      (∀s∈slots,|v s| ≤  height) → (∀u∈rows,|t u| ≤  height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : rows,a ≤  zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈rows,∀j,(naturalRow (MixedBootstrapNaturalBases.base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u.val u.property.1).character.modulus.absNorm ≤  Z^d) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH (excluded F₀.character R₀) η₀ W (Z^d) w σ v t θ u s‖
         ≤ ((Z^d)^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH (excluded F₀.character R₀) η₀ W (Z^d) w σ v t θ u s‖)^2) ≤ 
        C*(1+height)^J*
        (Z^d)^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,w s)+(2*a-1)*(∑s∈slots,w s)+
          402*ε+mesh+εm+2*binWidth*(∑s∈slots,w s)+ηloss) := by
  obtain ⟨J,hcount⟩ :=
    MixedBootstrapActualWeighted.actual_max_weighted_from_buffered_maxima_fixedmesh (Slot:=Slot) M H hH
      (wholeSourceBase M H hH η₀ ηcoarse) (wholeSourceAnchor M H hH η₀)
      u₀ (fun j=>naturalRow (wholeSourceBase M H hH η₀ ηcoarse j) u₀ hu₀)
      (R₀*wholeAnchorMask M H hH η₀) hu₀ bad
      hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm binWidth ηloss
      hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hβhi
  refine ⟨J,?_⟩
  intro dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκw hκw' hηw hbudget
  obtain ⟨C,hC,hcount⟩ := hcount dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight
    hε hεsmall he he' hκw hκw' hηw hbudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hcount
  refine ⟨hcount.1,?_⟩
  intro d hd hd' rows slots w σ v t θ hw hlo hhi hrow hnorm hkeep hlarge
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hmeshaux hbin' hwm hh hf hv ht
    hχ hnext hcurrent hmod hQ
  let B := MixedBootstrapNaturalBases.wholeNaturalBatch M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ bad W (33/50) (33/50) (Z^d) hWs rows slots w σ v t θ
    hw hlo hhi hrow hnorm hkeep hlarge
  have he (u : FreeRow) (hu : u∈rows) :=
    MixedBootstrapNaturalBases.whole_family_maximum M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ (χ u) u.val u.property.1 (holes u)
      (hholes u hu) (hcoeff u hu) (hχ u hu)
  let hc : ∀u∈B.rows,∀j,(B.family u j).residue≠1 := fun u hu=>(he u hu).choose
  have hmax (u : FreeRow) (hu : u∈rows) (T : ℝ) :
      zeroMaximum (B.family u) (hc u hu) T=
      zeroMaximum (wholeSourceFamily M H hH η₀ (χ u)) (hχ u hu) T :=
    (he u hu).choose_spec T
  exact hcount.2 d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax hmeshaux hbin' hwm hh hf hv ht hc
    (fun u=>by rw [hmax u.val u.property];exact hnext u)
    (fun u=>by rw [hmax u.val u.property];exact hcurrent u) hmod hQ

end
end OAI.SevenEighths.MixedBootstrapPlain
#print axioms OAI.SevenEighths.MixedBootstrapPlain.actual_whole_max_weighted_fixedmesh
