/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedBootstrapWholeRaw
import Candidate.Uneven.BootstrapTrivialSeed
import Candidate.Uneven.WeightedRootLift
import Candidate.Uneven.MixedBootstrapWholePadded
import Candidate.Cycle63.Marked.AmplitudeCap

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.BootstrapPlain
open OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily ProbePhysical LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentDetectorEnergyInitialState
open Deletion26
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤  H)

/-- Actual whole-family max-product count on raw frequencies. Every small
sixth-root fiber is counted by the marked source; large roots use the
verified ordinary density. Only literal source, buffer, and slot gates remain. -/
theorem actual_whole_raw_max_weighted_arbitrary {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j ≤  M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j) ≤  Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (bΦ Δ εm binWidth ηloss ordloss tailε : ℝ)
    (hordloss : 0<ordloss) (htail : 0<tailε) (htailmax : tailε ≤ 1/2)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2  ≤  bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0< binWidth) (hη : 0<ηloss)
    (hΔ0 : 0 ≤  Δ) (hΔ : Δ=0) (hεm : 0<εm)
    (hβ : (51/100:ℝ) ≤  HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta  ≤  7/8) :
    ∃J : ℕ,∀(Dmin Dmax dmin dmax τ ε e κw ηw pad wmin κroot Bmask Ccap slotloss : ℝ) (I : ℕ)
    (hDmin : 0< Dmin) (hDmax : Dmin ≤  Dmax) (hκroot : 0 ≤  κroot) (hκrootmax : κroot<1/6)
    (hdsmall : dmin ≤  Dmin*(1-6*κroot)) (hdlarge : Dmax+pad ≤  dmax)
    (hBmask : 0 ≤  Bmask) (hCcap : 0 ≤  Ccap) (hslotloss : slotloss ≤  binWidth*wmin)
    (hpad : 0< pad) (hwmin : 0< wmin) (hdmin : 0< dmin) (hdmax : dmin ≤  dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*ηw)
    (hε : 0<ε) (hεsmall : ε ≤ 1/1000) (he : 0< e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw ≤ 1) (hηw : 0 ≤  ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw ≤  ε/2),
      ∃C : ℝ,0<C ∧
      ∀ᶠU : ℝ in atTop,1< U ∧ ∀D : ℝ,Dmin ≤  D → D ≤  Dmax →
      ∀(rows : Finset NonzeroFrequency)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : NonzeroFrequency→ℝ)(θ : Slot→RayQuotient.Characters M H)
        (χ : NonzeroFrequency→Character)(holes : NonzeroFrequency→Ideal O),
      (∀u∈rows,rawFrequencyNorm u ≤  U^D) →
      (∀s∈slots,wmin ≤  w s) → (∀s∈slots,(33/50:ℝ) ≤  σ s) → (∀s∈slots,σ s ≤  (33/50:ℝ)) →
      (∀u∈rows,holes u≠0) → (∀u∈rows,((holes u).absNorm:ℝ) ≤  U^Bmask) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i ≤  I →
      31/50 ≤ 2*a-1 → 2*a-1 ≤ 33/50 →
      0 ≤  mesh → mesh ≤  markedPlainMesh (3/4+2*Δ) εm → mesh  ≤  AuxiliaryAssembly.sourceMesh εm → binWidth ≤ (2*a-1)/2 →
      (∀s∈slots,w s ≤  mesh*dmin) →
      0 ≤  height → 2*Real.pi*U^(τ/2)+(3*i:ℕ)*U^τ ≤  height →
      (∀s∈slots,|v s| ≤  height) → (∀u∈rows,|t u| ≤  height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*U^τ)< a+2*e) →
      (∀u : rows,a ≤  zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*U^τ)) →
      (∀u∈rows,∀s∈slots,(max 1 ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2
         ≤  Ccap*U^((2*a-1)*w s+slotloss)) →
      let S:=∑s∈slots,w s
      let ρ:=unmarkedDensity (2*a-1)
      let A:=(2*a-1+2*binWidth)*S+dmax*(402*ε+mesh+εm+ηloss)+pad*ρ
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeRawSlot M H hH η₀ W U w σ v t θ χ u s‖)^2) ≤ 
        C*(1+height)^J*U^(D*(ρ+ordloss)+A-
          min (Sil.Uneven.Bootstrap.physicalGain (2*a-1) S D) (D*κroot*(6*(ρ+ordloss-3/200)-1-tailε))) := by
  simpa only [BootstrapNaturalBases.trivial_seed_masked_coefficients] using
    MixedBootstrapPlain.actual_whole_raw_max_weighted_fixedmesh (Slot:=Slot) M H hH
      η η₀ 1 (naturalRow η 1 one_ne_zero) one_ne_zero 1 one_ne_zero
      bad hbadM hbad0 hbadTop hbad72 Sbad hbad setup W bΦ Δ εm binWidth ηloss ordloss tailε
      hordloss htail htailmax hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hβhi

end
end OAI.SevenEighths.BootstrapPlain
#print axioms OAI.SevenEighths.BootstrapPlain.actual_whole_raw_max_weighted_arbitrary
