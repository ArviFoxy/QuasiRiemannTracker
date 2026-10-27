/- Copyright (c) 2026 Sil. Apache-2.0.
WP-J: `diag_hbud`, the diagonal part of `hbudL/hbudR` with WP-M's counting bounds
(`ConcreteAssemblyAvgBounds2`) plugged into `ConcreteDiagAssembly.diag_budget`: `W_B = slotWidth`,
`Hv = 2304·log X`, `Selmax = pcMass·Mall²·1024^N·Mc·Wmax^{2/3}`,
`S0 = pcMass·Mall²·256^N·(Wmax+Yr)·(2^N·Mc)·(Wmax⁴·profileCap(s)²·Yup^ε)`,
`St = pcMass·Mall²·256^N·Wmax·(2^N·Mc)·(128·X·Wmax·profileCap(s)²)`.
The only remaining hypotheses are the three root-level inequalities `hroot0`, `hrootf`, `hroott`.

Exponent check of `hroot0` (CF §7): with `K = childScale ≲ firstNominalScale =
N E·N act·V²/(Kfirst·N C·N D)` and `N τ = N η·fixed·N E·N act`,
`K/(N τ·V²/(N C·N D)) ≍ Z^{-m}` (`m = inputWidth = log(Kfirst·Nη·fixed)`), so the main term
`K·Wmax⁴·Yr` against `balancedBudget` is `Z^{Λ - c - m + 4u}` (`Yr ≍ V/N C`, the live cap;
`Wmax ≍ Z^u`): CF's `A-1-c+4u`, i.e. `4u`. The additive `Wmax` gives `Z^{5u-m}`, covered by
the main term whenever `u ≤ Λ - c` (the residual of a selection has nonnegative log-volume). -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteAssemblyAvgBounds2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstMixedAllowance
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional
open CenteredMomentCanonicalFirst EisensteinSchwartzPoisson CenteredMomentCompleteCommon
open QRH.Record1252270103KernelMass
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedPrincipalCentered MixedCommonCoefficient MixedFirstLiveSource MixedOriginalTail
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedFirstExceptionalNormalization
open MixedFirstExceptionalWindow MixedFirstAllocatedRemainders MixedOriginalNormCap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAnnularMajorant CenteredMomentFirstAnnularEnergy
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentFirstMixedAllowance CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open RayFourExpansion CenteredMomentSecondEnergySplit CenteredMomentLattice
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalBudget
open MixedPrincipalCentered MixedCommonCoefficient MixedCommonRestriction
open MixedPrincipalWindow MixedOriginalTail
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstLiveSource MixedFirstExceptionalNormalization MixedSourceAssembly
open QRH.DensitySplitThird.CubeFree.FP
open QRH.DensitySplitThird.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) instDecEqSubtypeDiagHbud {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-- **The diagonal part of `hbud`**, with every counting input discharged by WP-M's bounds. -/
theorem diag_hbud (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (η τ : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D))
    (JB : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val))
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (Lref : ℝ) (M Y : actualAllocations (tuplePools s) C → ℝ) (J : ℕ)
    (control controlT : Finset (ℕ×ℕ)) (Q : Id)
    (Z ε α Bnorm δ εsum saving C0 Ckernel A Csum Ct : ℝ)
    (Kfirst Tsec Csec ξ κ : ℝ) (n : ℤ) (N : ℕ) (Mc Wmax Yr Yup X Abud loss θ0 θf θt : ℝ)
    (hZ : 1 < Z) (hKf : 0 < Kfirst) (hCsec : 1 ≤ Csec) (hξ : 0 ≤ ξ) (hLref : 0 ≤ Lref)
    (hε : 0 ≤ ε)
    (hC0 : 0 ≤ C0) (hCk : 0 ≤ Ckernel) (hA : 0 ≤ A) (hCsum : 0 ≤ Csum) (hCt : 0 ≤ Ct)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hsec : Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s))
    (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hDC : (D.absNorm:ℝ)≤(C.absNorm:ℝ)^3)
    (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc)
    (hWB : ∀ B, slotWidth (allocatedLiveSource s hb cover C B) (JB B) ≤ Wmax)
    (hYr : ∀ B, sourceNormCap (allocatedLiveSource s hb cover C B).P b
      (allocatedLiveSource s hb cover C B).T (allocatedLiveSource s hb cover C B).d ≤ Yr)
    (hY : ∀ B, 1 ≤ Y B ∧ Y B ≤ Yup ∧
      Y B ≤ 1 + sourceNormCap (restOf s hb cover C B (JB B)).P b
        (restOf s hb cover C B (JB B)).T (restOf s hb cover C B (JB B)).d)
    (hX : 3 ≤ X) (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ X) (hPX : poolCap s ≤ X)
    (hroot0 : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      ((∏ i, s.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (16*childScale Z κ n*‖paperRadialFourier ballProfile 0‖*C0)*(2304*Real.log X)*
        (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * (Wmax + Yr) * ((2:ℝ)^N * Mc) *
          (Wmax^4 * (profileCap s)^2 * Yup^ε))) ≤
        θ0*balancedBudget s τ C D Abud Z loss)
    (hrootf : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      ((pcMass * (∏ i, s.M i)^2 * (1024:ℝ)^N * Mc * Wmax^(2/3:ℝ))*
        ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*
          Z^(2*Bnorm*δ)*(Csum*Z^εsum))*(2304*Real.log X)*
        (fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*
        (slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))) ≤ θf*Abud*Z^loss)
    (hroott : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      ((∏ i, s.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*
        (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax * ((2:ℝ)^N * Mc) *
          (128 * X * Wmax * (profileCap s)^2))) ≤
        θt*balancedBudget s τ C D Abud Z loss) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
        (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            xiB s hb cover C JB Us (childScale Z κ n) Lref
              (fun B => slotWidth (allocatedLiveSource s hb cover C B) (JB B)) Y J control controlT
              Q Z ε α Bnorm δ εsum saving C0 Ckernel A Csum Ct B)) ≤
      (θ0+θf+θt)*balancedBudget s τ C D Abud Z loss := by
  have hWpos : ∀ B, 0 < slotWidth (allocatedLiveSource s hb cover C B) (JB B) :=
    fun B => slotWidth_pos _ _
  have hlogX : 0 ≤ 2304*Real.log X := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ X); positivity
  by_cases hne : Nonempty (actualAllocations (tuplePools s) C)
  · obtain ⟨B₀⟩ := hne
    have hWmax : 0 < Wmax := (hWpos B₀).trans_le (hWB B₀)
    exact diag_budget s ha hb cover η τ C D hC hD hCD E JB Us Lref
      (fun B => slotWidth (allocatedLiveSource s hb cover C B) (JB B)) M Y J control controlT Q
      Z ε α Bnorm δ εsum saving C0 Ckernel A Csum Ct Kfirst Tsec Csec ξ κ n Wmax
      (pcMass * (∏ i, s.M i)^2 * (1024:ℝ)^N * Mc * Wmax^(2/3:ℝ)) (2304*Real.log X)
      (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * (Wmax + Yr) * ((2:ℝ)^N * Mc) *
        (Wmax^4 * (profileCap s)^2 * Yup^ε))
      (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax * ((2:ℝ)^N * Mc) *
        (128 * X * Wmax * (profileCap s)^2)) Abud loss θ0 θf θt
      hZ hKf hCsec hξ hLref hC0 hCk hA hCsum hCt hlogX hmod hsec hn hDC hWmax
      (fun B => ⟨hWpos B, hWB B⟩) (fun B => (hM B).1)
      (fun B => zero_le_one.trans (hY B).1)
      (hV_bound s hb cover C JB Us hUs X hX hUX hPX)
      (hsel0_bound_rest s hb cover C JB M Y N Mc Wmax Yr Yup ε hε hJ hM hWB hYr hY)
      (hself_bound s hb cover C JB M N Mc Wmax hJ hM hWB)
      (hselT_bound s hb cover C JB Us hUs X (by linarith) hUX hPX M N Mc Wmax hJ hM hWB)
      hroot0 hrootf hroott
  · have hE : (Finset.univ : Finset (actualAllocations (tuplePools s) C)) = ∅ :=
      Finset.univ_eq_empty_iff.mpr (not_nonempty_iff.mp hne)
    rw [hE, Finset.sum_empty, mul_zero]
    have h0 := hroot0
    have ht := hroott
    rw [hE, Finset.card_empty] at h0 ht
    have hf := hrootf
    rw [hE, Finset.card_empty] at hf
    have hbud := balancedBudget_eq s τ C D hC.1 hD.1 Abud Z loss
    have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
    have hd : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hD.1)
    have href : 0 ≤ reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ)) := by
      have := (zero_lt_one.trans hZ).le
      unfold reference; positivity
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul] at h0 ht hf
    have hf' : 0 ≤ θf*balancedBudget s τ C D Abud Z loss := by
      rw [hbud]
      have hZl : 0 < Z^loss := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
      have : 0 ≤ θf*Abud := by
        by_contra hneg
        push_neg at hneg
        have := mul_neg_of_neg_of_pos hneg hZl
        linarith
      calc (0:ℝ) ≤ θf*Abud*Z^loss*(reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) :=
            mul_nonneg (mul_nonneg this hZl.le) href
        _ = _ := by ring
    rw [add_mul, add_mul]
    linarith
