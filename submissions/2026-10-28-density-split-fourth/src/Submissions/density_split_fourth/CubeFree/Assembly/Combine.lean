/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L, step assembly (design L7): the restricted cube-free source from the parent rows and the
root chain's rows, and the child source by restoration.

Every restored row `(T, w, r, A)` is classified by its OWN marked width `rowWidth`:
* rows narrower than `s₀` are bounded by the parent source through the forward K₃ transfer
  (`restricted_rows_of_parent`, CF §8);
* the other rows are the root chain's top output (`HighRestrictedUnitSource`).
The two sets of constants are merged after both are fixed (max degree, union of controls,
max constant, min mesh), and WP-R's restoration (`global_source_of_restricted`) gives the
child `GlobalSource`. -/
import Submissions.density_split_fourth.CubeFree.Assembly.ParentRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Assembly
noncomputable section
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentRetainedEnergy CenteredMomentLattice
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentRayMaskedFloor QuadraticInitialBound CenteredMomentEnergyBandMonotonicity
open CenteredMomentOriginalRadialComparison CenteredMomentEnergyReferenceChild
open QRH.DensitySplitThird.CubeFree.FP
open RestorationFamily KernelCollisionEnergy KernelRowPools KernelRowProfiles
open ReferencePrimeEnclosure RestoredInitialSource NativeFiniteHoles
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The root chain's top output: the restricted cube-free source on every restored row whose
own marked width is at least `s₀` (mesh before the slot type, η before the constants). -/
def HighRestrictedUnitSource (face : SourceFace) (s₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Id) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H),
  ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Id),
    Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
    internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, ∀ (T : Finset α) (w : T → ℝ) (r : Setoid T)
        (A : Finset {q // singletonBlock r q}), s₀ ≤ rowWidth T w r A →
        RestrictedRowAt rayM H hH face W bΦ mesh ε Z η η₀ Q degree controls C T w r A

set_option maxHeartbeats 800000 in
/-- **Per-row assembly** (design L7): the parent rows (width `< s₀`) and the root chain's rows
give the child source. `hinherit` is `StepGates.inherit` (CF crossing). -/
theorem global_source_of_parent_and_high (B L c B₀ L₀ c₀ s₀ : ℝ) (hB : B ≤ 1) (hL : 0 ≤ L)
    (hL₀ : 0 ≤ L₀)
    (hinherit : ∀ P S : ℝ, 0 ≤ S → S < s₀ → P + L*S ≤ B → P + L₀*S ≤ B₀ ∧ S ≤ c₀)
    (hparent : GlobalSource B₀ L₀ c₀)
    (hhigh : HighRestrictedUnitSource (globalFace B L c) s₀) :
    GlobalSource B L c := by
  apply global_source_of_restricted B L c hB
  intro ε hε
  obtain ⟨meshL, hmL, hlow⟩ :=
    restricted_rows_of_parent B L c B₀ L₀ c₀ s₀ hB hL hL₀ hinherit hparent ε hε
  obtain ⟨meshH, hmH, hhi⟩ := hhigh ε hε
  refine ⟨min meshL meshH, lt_min hmL hmH, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨dL, SL, CL, hCL, hLev⟩ := hlow α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨dH, SH, CH, hCH, hHev⟩ := hhi α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨max dL dH, SL ∪ SH, max CL CH, lt_max_of_lt_left hCL, ?_⟩
  filter_upwards [hLev, hHev, eventually_gt_atTop (0:ℝ)] with Z hLZ hHZ hZ0
  intro T θ w
  refine restrictedInitialAtT_of_rows rayM H hH (globalFace B L c) W bΦ _ ε Z η η₀ Q _ _ _ T w
    (fun r A => ?_) θ
  by_cases hrw : rowWidth T w r A < s₀
  · exact RestrictedRowAt.mono rayM H hH (hLZ T w r A hrw) (min_le_left _ _) hCL.le
      (le_max_left _ _) Finset.subset_union_left (le_max_left _ _) hZ0
  · exact RestrictedRowAt.mono rayM H hH (hHZ T w r A (le_of_not_gt hrw)) (min_le_right _ _)
      hCH.le (le_max_right _ _) Finset.subset_union_right (le_max_right _ _) hZ0

end
end QRH.DensitySplitThird.CubeFree.Assembly
