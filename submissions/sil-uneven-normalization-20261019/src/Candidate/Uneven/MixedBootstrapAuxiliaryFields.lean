/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedAuxiliaryPlainRowwise
import Candidate.Cycle63.Marked.Route.ActualWeightedFixedMesh
import Candidate.Uneven.BootstrapAssembly

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.MixedBootstrapActualWeighted
open Cycle63ActualWeighted HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open LocalMoment CenteredMomentDetectorPlainFiberSource
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Uniform auxiliary moment for the same literal batch used in PR63.
The bases are fixed natural seeds over their corresponding relative anchors.
No bound on the moving rows is assumed beyond the fields of NaturalBatch. -/
theorem actual_auxiliary_source_fields
    (coarse anchor : Label→Character) (u₀ : O) (F₀ : ∀j,NaturalRow (coarse j) u₀)
    (R₀ : Ideal O) (hu₀ : u₀≠0) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j ≤ M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j) ≤ Ideal.span {(72:O)})
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (bΦ εm mesh : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 2 ≤ bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀B : NaturalBatch (Slot:=Slot) M H hH (fun j=>excluded (F₀ j).character R₀)
        anchor bad W (33/50) (33/50) U,
      (∀s∈B.slots,B.widths s ≤ mesh) →
      ∀height : ℝ,0 ≤ height → (∀s∈B.slots,|B.relativeHeight s| ≤ height) →
      (∀u∈B.rows,|B.commonHeight u| ≤ height) →
      ∀rows : Finset FreeRow,rows⊆B.rows → ∀label : Label,
      ∀selected : Finset Slot,selected⊆B.slots →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s∈selected,B.widths s) →
      (∑s∈selected,B.widths s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s∈selected,B.widths s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σ freq*
        polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σ freq*
          (∏s∈selected,B.Q u s)‖^2) ≤ (C*(1+height)^J)*U^(1+εm) := by
  have hP (j : Label) := AuxiliaryPlainTransport.actual_rowwise_marked_plain_energy_mixed_anchor (α:=Slot)
    M H hH Sbad hbad W hWs hW bΦ εm mesh hbΦ hrad hεm hmesh0 hmesh hβlo hβhi
    (coarse j) (anchor j) u₀ (F₀ j) R₀ hu₀ (bad j) (hbadM j) (hbad0 j) (hbadTop j) (hbad72 j)
  choose Jp Cp hCp hP using hP
  let J := ∑j,Jp j
  let C := 1+∑j,Cp j
  have hCps : 0 ≤ ∑j,Cp j := Finset.sum_nonneg (fun j _=>(hCp j).le)
  have hC : 0<C := by dsimp [C]; linarith
  have hCpj (j : Label) : Cp j ≤ C := by
    have hh := Finset.single_le_sum (fun k _=>(hCp k).le) (Finset.mem_univ j)
    dsimp [C]; linarith
  have hJp (j : Label) : Jp j ≤ J :=
    Finset.single_le_sum (fun k _=>Nat.zero_le (Jp k)) (Finset.mem_univ j)
  have hPall : ∀ᶠU : ℝ in atTop,∀j,_ := eventually_all.mpr hP
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hPall,eventually_gt_atTop (1:ℝ)] with U hPall hU
  refine ⟨hU,?_⟩
  intro B hwm height hh hv hchoice rows hrows label selected hselected hwl hwu m hm hm1 hcap
    j k hjk σ hσ freq hfreq
  have hPC : Cp label*(1+height)^(Jp label) ≤ C*(1+height)^J :=
    mul_le_mul (hCpj label) (pow_le_pow_right₀ (by linarith) (hJp label)) (by positivity) hC.le
  have hinj : Function.Injective (fun u:FreeRow=>u.val) := Subtype.val_injective
  have he := (hPall label).2 rows (fun u:FreeRow=>u.val) hinj (fun u=>B.family u label)
    (fun u hu=>B.elementCoefficients u (hrows hu) label)
    (fun u hu=>B.retained u (hrows hu) label) (fun u hu=>B.embeddingNorm u (hrows hu))
    m hm hm1 selected (fun s=>B.rays label s.val) (fun s=>B.widths s.val)
    (fun s=>B.sigma s.val) (fun s=>B.relativeHeight s.val) height B.commonHeight
    (fun s=>(B.widthsPositive s.val (hselected s.property)).le)
    (fun s=>hwm s.val (hselected s.property))
    (fun s=>B.sigmaLower s.val (hselected s.property))
    (fun s=>B.sigmaUpper s.val (hselected s.property)) hh
    (fun s=>hv s.val (hselected s.property)) (fun u hu=>hchoice u (hrows hu))
    (by simpa only [Finset.sum_coe_sort] using hwl)
    (by simpa only [Finset.sum_coe_sort] using hwu)
    (by simpa only [Finset.sum_coe_sort] using hcap) j k hjk σ hσ freq (abs_le.mpr hfreq)
  have heq : (∑u∈rows,‖polynomial (B.family u label) false ((logProfile^[j]) positiveAnnular)
      (U^m) σ freq*polynomial (B.family u label) false ((logProfile^[k]) positiveAnnular)
      (U^m) σ freq*(∏s∈selected,B.Q u s)‖^2) ≤ (Cp label*(1+height)^(Jp label))*U^(1+εm) := by
    convert he using 1
    apply Finset.sum_congr rfl
    intro u hu
    congr 3
    rw [←Finset.prod_coe_sort selected (B.Q u)]
    exact Finset.prod_congr rfl (fun s _=>B.plainIdentity u (hrows hu) label s.val (hselected s.property))
  exact heq.trans (mul_le_mul_of_nonneg_right hPC (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end OAI.SevenEighths.MixedBootstrapActualWeighted
#print axioms OAI.SevenEighths.MixedBootstrapActualWeighted.actual_auxiliary_source_fields
