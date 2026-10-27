/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L: restored rows narrower than the crossing width come from the parent (CF §8).

`restricted_rows_of_parent`: the parent `GlobalSource B₀ L₀ c₀` bounds every restricted
(collision- and inverse-restored, cube-free, with marked holes) row of the child face whose
own marked width is `< s₀`. This is the cube-free analogue of PR69's
`projected_subsets_of_ordinary_parent`:
* the restricted row is WP-G's forward-K₃ row (`Packet.Reduce.forward_dom`): it is dominated,
  at mass `C·Z^{ε/2}`, by canonical native leaves on all subsets of its slots, at shortened
  lengths and with the restoration holes;
* each leaf is a full initial energy (`nativeLeaf_energy`) of a slot subset `B` of width
  `≤ rowWidth < s₀`, at lengths below the root's, hence in the parent face
  (`StepGates.inherit`), so the parent's bound applies;
* the phase-shifted profiles cost `(1+|t|)^{4n}` (`normPowerProfile_source_control`).
Constants: the forward masses are bounded uniformly over the finitely many row types
`(T, r, A)` of the ambient slot type, after the parent constants; all before `Z`. -/
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Rows
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.NativeForwardDom
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.Label
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedPrincipalHeights
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Reindex
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.SilDensitySplit.CubeFree.Assembly
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
open QRH.SilDensitySplit.CubeFree.FP
open RestorationFamily KernelCollisionEnergy KernelRowPools KernelRowProfiles
open ReferencePrimeEnclosure RestoredInitialSource NativeFiniteHoles
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Setoids on a finite type form a finite type. -/
instance setoidFinite (T : Type*) [Finite T] : Finite (Setoid T) :=
  Finite.of_injective (fun r : Setoid T => r.r) (by
    intro r s h
    cases r; cases s
    simp only at h
    subst h
    rfl)

/-- The restored-row types of an ambient slot type. -/
abbrev RowType (α : Type) : Type :=
  Σ T : Finset α, Σ r : Setoid T, Finset {q // singletonBlock r q}

/-- The row depends on its character only through the ideal coefficients. -/
theorem row_idealCoeff_congr {β : Type*} [Fintype β] (inv : Bool) (S : Finset PrimeIdeal)
    (χ χ' : Character) (h : ∀ I, idealCoeff χ I = idealCoeff χ' I)
    (pool : β → Finset Id) (b' : β → Id → ℂ) (P : β → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    row inv S χ pool b' P W₁ W₂ b X₁ X₂ = row inv S χ' pool b' P W₁ W₂ b X₁ X₂ := by
  unfold RestorationFamily.row KernelMarkedRows.naturalCoefficients KernelNaturalSlots.slotTerm
    normalizedRow KernelRowExpansion.pairCharacter
  simp only [h]

theorem excludePrimes_empty_coeff (χ : Character) (h : ∀ P ∈ (∅ : Finset Id), Prime P) :
    ∀ I, idealCoeff (χ.excludePrimes ∅ h) I = idealCoeff χ I := by
  intro I
  rw [idealCoeff_excludePrimes]
  simp

/-- The finite initial-weight sum is below the kept radial energy. -/
theorem finite_le_radialEnergy (F : O → ℂ) (η η₀ : Character) (Q : Id) (Φ : 𝓢(ℝ,ℂ))
    (K bΦ : ℝ) (hK : 0 < K) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (rows : Finset O) :
    (∑ z ∈ rows, initialWeight η η₀ Q Φ K z*‖F z‖^2) ≤
      radialEnergy F (initialKeep η (internalQ Q η₀)) Φ K := by
  let g := fun z : O => if initialKeep η (internalQ Q η₀) z then
    ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hg : ∀ z, 0 ≤ g z := by
    intro z
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  have hsum := CenteredMomentEnergyCapacityRemoval.compact_radial_summable F
    (initialKeep η (internalQ Q η₀)) Φ K bΦ hK hs
  have he : (∑ z ∈ rows, initialWeight η η₀ Q Φ K z*‖F z‖^2) = ∑ z ∈ rows, g z := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hk : initialKeep η (internalQ Q η₀) z
    · simp only [initialWeight, hk, ite_true, g]; ring
    · simp only [initialWeight, hk, ite_false, g, zero_mul]
  rw [he]
  exact hsum.sum_le_tsum rows (fun z _ => hg z)

section
variable (rayM : Id) [NeZero rayM]
local instance finiteRayQuotientP : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- A native leaf on a slot type embedded in another is the leaf of the image subset. -/
theorem nativeLeaf_map {β γ : Type*} (e : β ↪ γ) (W : ℝ → ℂ) (η₀ : Character)
    (θ : γ → RayQuotient.Characters rayM H) (Z : ℝ) (w σ freq : γ → ℝ) (t : ℝ) (η : Character)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (W₁ W₂ : ℝ → ℂ) (t₁ t₂ : ℝ) (A : Finset β)
    (X₁ X₂ : ℝ) :
    Packet.Reduce.nativeLeaf rayM H hH W η₀ (θ ∘ e) Z (w ∘ e) (σ ∘ e) (freq ∘ e) t η keep Φ K
        W₁ W₂ t₁ t₂ A X₁ X₂ =
      Packet.Reduce.nativeLeaf rayM H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂
        (A.map e) X₁ X₂ := by
  unfold Packet.Reduce.nativeLeaf Packet.Reduce.leafEnergy Packet.Reduce.leafRow
  simp only [Finset.prod_map]
  rfl

end

set_option maxHeartbeats 4000000 in
/-- **Narrow restored rows from the parent** (CF §8 at the level of restricted rows): the
parent source bounds every restored row of the child face of marked width `< s₀`.
`hinherit` is `StepGates.inherit`. Constants: η before constants, mesh before slot type. -/
theorem restricted_rows_of_parent (B L c B₀ L₀ c₀ s₀ : ℝ) (hB : B ≤ 1) (hL : 0 ≤ L)
    (hL₀ : 0 ≤ L₀)
    (hinherit : ∀ P S : ℝ, 0 ≤ S → S < s₀ → P + L*S ≤ B → P + L₀*S ≤ B₀ ∧ S ≤ c₀)
    (hparent : GlobalSource B₀ L₀ c₀) :
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
          (A : Finset {q // singletonBlock r q}), rowWidth T w r A < s₀ →
          RestrictedRowAt rayM H hH (globalFace B L c) W bΦ mesh ε Z η η₀ Q degree controls C
            T w r A := by
  intro ε hε
  obtain ⟨meshP, hmP, hP⟩ := hparent (ε/2) (half_pos hε)
  refine ⟨min meshP 1, lt_min hmP one_pos, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨dP, SP, CP, hCP, hPev⟩ := hP α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨n, Tc, Cc, hCc, hctl⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) SP
  choose Cf hCf hfwd using fun x : RowType α =>
    Packet.Reduce.forward_dom rayM H hH (α := {q : {q // singletonBlock x.2.1 q} // q ∉ x.2.2})
      (2*Fintype.card α) W (1/4) (9/4) 1 1 2 4 0 (ε/2) (33/50) (33/50) hWs hW
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
      (by norm_num) (by norm_num) (half_pos hε)
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, ∀ x, Cf x ≤ Cm := by
    obtain ⟨M, hM⟩ := (Set.finite_range Cf).bddAbove
    exact ⟨M, fun x => hM ⟨x, rfl⟩⟩
  refine ⟨dP + 4*n, Tc, max Cm 1*CP*Cc^4, by positivity, ?_⟩
  filter_upwards [hPev, eventually_gt_atTop (1:ℝ)] with Z hPZ hZ1
  intro T w r A hnarrow θ σ v t height hw hwm hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm
    rows tc ti hti Y₁ Y₂ hY₁ hYX₁ hY₂ hYX₂
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  let emb : {q : {q // singletonBlock r q} // q ∉ A} ↪ α :=
    (RestoredRootDictionary.remainingEmbedding r A).trans (Function.Embedding.subtype (· ∈ T))
  let θα := extend T θ 1
  let wα := extend T w 0
  let σα := extend T σ (33/50)
  let vα := extend T v 0
  have hθf : θα ∘ emb = fun q => θ (singletonRepresentative r q.val) :=
    funext fun q => extend_coe T θ 1 (singletonRepresentative r q.val)
  have hwf : wα ∘ emb = fun q => w (singletonRepresentative r q.val) :=
    funext fun q => extend_coe T w 0 (singletonRepresentative r q.val)
  have hσf : σα ∘ emb = fun q => σ (singletonRepresentative r q.val) :=
    funext fun q => extend_coe T σ (33/50) (singletonRepresentative r q.val)
  have hvf : vα ∘ emb = fun q => v (singletonRepresentative r q.val) :=
    funext fun q => extend_coe T v 0 (singletonRepresentative r q.val)
  have hwe : ∀ q, wα (emb q) = w (singletonRepresentative r q.val) :=
    fun q => congrFun hwf q
  let R₀ := fun _ : {q : {q // singletonBlock r q} // q ∉ A} =>
    NativeMaskedEnergy.restorationHoles r (primeEnclosure Z) tc A ti
  let keep := initialKeep η (internalQ Q η₀)
  -- the face data of the root
  have hsT : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  obtain ⟨hcapT, hbudT⟩ := (globalFace_admissible_iff (length_nonneg Z X₁ hZ1)
    (length_nonneg Z X₂ hZ1) hsT hL).mp hadm
  simp only [mul_one] at hcapT hbudT
  have hLs := mul_nonneg hL hsT
  have hl₁ : length Z X₁ ≤ 1 := by nlinarith [length_nonneg Z X₂ hZ1]
  have hl₂ : length Z X₂ ≤ 1 := by nlinarith [length_nonneg Z X₁ hZ1]
  have hXZ : ∀ X : ℝ, length Z X ≤ 1 → X ≤ Z^(1:ℝ) := by
    intro X hX
    have h1 : max 1 X ≤ Z^(1:ℝ) :=
      (Real.logb_le_iff_le_rpow hZ1 (lt_of_lt_of_le one_pos (le_max_left _ _))).mp hX
    exact (le_max_right _ _).trans h1
  have hRe : ∀ P ∈ (∅ : Finset Id), Prime P := by simp
  -- the forward K₃ domination of the restored row
  have hfd := hfwd ⟨T, r, A⟩ Z hZ1.le η₀ (θα ∘ emb) (wα ∘ emb) (σα ∘ emb) (vα ∘ emb) t R₀
    (fun q => by rw [hwf]; exact hw _)
    (fun q => by rw [hwf]; exact (hwm _).trans (min_le_right _ _))
    (fun q => by rw [hσf]; exact hσlo _) (fun q => by rw [hσf]; exact hσhi _)
    (fun q => (NativeMaskedEnergy.restoration_holes_card r _ tc A ti).trans
      (Nat.mul_le_mul_left 2 (by simpa only [Fintype.card_coe] using Finset.card_le_univ T)))
    η keep Φ Z bΦ hZ0 hΦ (fun z => hΦp _) (fun z hz => hz.1) ∅ hRe (by simp)
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) (t/(2*Real.pi)) (t/(2*Real.pi))
    Y₁ Y₂ hY₁ hY₂ (hYX₁.trans (hXZ X₁ hl₁)) (hYX₂.trans (hXZ X₂ hl₂))
  -- the restricted row is the forward row
  have hc : crossBeta A (primeEnclosure Z) ti
      (RestorationCollisionEnergy.collisionBeta r (primeEnclosure Z) tc
        (initialCoefficient rayM H hH η₀ θ W w σ v Z t)) =
      fun q => heightCoefficient (holeCoefficient
        (fun j : {q : {q // singletonBlock r q} // q ∉ A} =>
          rawCoefficient rayM H hH η₀ θ W w σ v Z (singletonRepresentative r j.val))
        R₀ q) t :=
    RestoredRootDictionary.restoration_height_coefficients r (primeEnclosure Z) tc A ti
      (fun i => rawCoefficient rayM H hH η₀ θ W w σ v Z i) t
  have hr0 : (raisedProfile p t 0 : ℝ → ℂ) = phaseProfile (p.profile 0) (t/(2*Real.pi)) :=
    MixedPrincipalHeights.norm_power_profile_phase _ _ _ _ _ _ t
  have hr1 : (raisedProfile p t 1 : ℝ → ℂ) = phaseProfile (p.profile 1) (t/(2*Real.pi)) :=
    MixedPrincipalHeights.norm_power_profile_phase _ _ _ _ _ _ t
  let Frow := fun z : O => row false (enclosure (4*Z^(2:ℝ)))
    ((naturalCharacter η z).excludePrimes ∅ hRe)
    (fun i => supportedPool (primePool rayM H 2 (Z^((wα ∘ emb) i))))
    (fun i => heightCoefficient (holeCoefficient
      (Packet.Reduce.slotBeta rayM H hH W η₀ (θα ∘ emb) Z (wα ∘ emb) (σα ∘ emb) (vα ∘ emb))
      R₀ i) t)
    (fun i => Z^((wα ∘ emb) i))
    (phaseProfile (p.profile 0) (t/(2*Real.pi))) (phaseProfile (p.profile 1) (t/(2*Real.pi)))
    (9/4) Y₁ Y₂
  have hrow : ∀ z, row false (primeEnclosure Z) (naturalCharacter η z)
      (fun q : {q : {q // singletonBlock r q} // q ∉ A} =>
        initialPool rayM H w Z (singletonRepresentative r q.val))
      (crossBeta A (primeEnclosure Z) ti
        (RestorationCollisionEnergy.collisionBeta r (primeEnclosure Z) tc
          (initialCoefficient rayM H hH η₀ θ W w σ v Z t)))
      (fun q => Z^(w (singletonRepresentative r q.val)))
      (raisedProfile p t 0) (raisedProfile p t 1) (9/4) Y₁ Y₂ = Frow z := by
    intro z
    dsimp only [Frow]
    rw [row_idealCoeff_congr false _ _ (naturalCharacter η z) (excludePrimes_empty_coeff _ hRe),
      hc, hr0, hr1, hθf, hwf, hσf, hvf]
    rfl
  -- every leaf is a parent energy
  let tt := 2*Real.pi*(t/(2*Real.pi))
  have htt : tt = t := by dsimp only [tt]; field_simp
  let p' := independentProfiles (by norm_num : (0:ℝ) < 1/4) (p.profile 0) (p.profile 1)
    (p.support 0) (p.support 1) tt tt
  let E := CP*diagonalControl Φ*(p'.control SP)^2*(1+|(0:ℝ)|+(|t|+height))^dP*
    Z^((1:ℝ)+ε/2)
  have hE : 0 ≤ E := by
    have := diagonalControl_nonneg Φ
    dsimp only [E]
    positivity
  have hleaves : ∀ (A'' : Finset {q : {q // singletonBlock r q} // q ∉ A}),
      ∀ pr ∈ Packet.Reduce.forwardLengths (enclosure (4*Z^(2:ℝ))) (9/4) Y₁ Y₂ ∅,
      Packet.Reduce.nativeLeaf rayM H hH W η₀ (θα ∘ emb) Z (wα ∘ emb) (σα ∘ emb) (vα ∘ emb) t
        η keep Φ Z (p.profile 0) (p.profile 1) (2*Real.pi*(t/(2*Real.pi)))
        (2*Real.pi*(t/(2*Real.pi))) A'' pr.1 pr.2 ≤ E := by
    intro A'' pr hpr
    obtain ⟨hp1, hp1Y, hp2, hp2Y⟩ := Packet.Reduce.forwardLengths_below hRe hY₁ hY₂ pr hpr
    rw [nativeLeaf_map rayM H hH emb, Packet.Reduce.nativeLeaf_energy rayM H hH W η₀ θα Z hZ0
      wα σα vα t η keep (fun z hz => hz.1) Φ Z hZ0 hΦp (by norm_num : (0:ℝ) < 1/4)
      (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) tt tt (A''.map emb)
      pr.1 pr.2 hp1 hp2]
    have hsB : ∑ i : (A''.map emb), wα i = ∑ q ∈ A'', w (singletonRepresentative r q.val) := by
      rw [Finset.sum_coe_sort (A''.map emb) wα, Finset.sum_map]
      exact Finset.sum_congr rfl (fun q _ => hwe q)
    have hsBrow : ∑ q ∈ A'', w (singletonRepresentative r q.val) ≤ rowWidth T w r A :=
      Finset.sum_le_univ_sum_of_nonneg (fun q => hw _)
    have hrowT : rowWidth T w r A ≤ ∑ i, w i := RestoredRootDictionary.remaining_sum_le r A w hw
    have hsB0 : 0 ≤ ∑ i : (A''.map emb), wα i := by
      rw [hsB]; exact Finset.sum_nonneg (fun q _ => hw _)
    have hlen₁ : length Z pr.1 ≤ length Z X₁ :=
      Real.logb_le_logb_of_le hZ1 (lt_of_lt_of_le one_pos (le_max_left _ _))
        (max_le_max le_rfl (hp1Y.trans hYX₁))
    have hlen₂ : length Z pr.2 ≤ length Z X₂ :=
      Real.logb_le_logb_of_le hZ1 (lt_of_lt_of_le one_pos (le_max_left _ _))
        (max_le_max le_rfl (hp2Y.trans hYX₂))
    have hLB : L*(∑ i : (A''.map emb), wα i) ≤ L*(∑ i, w i) := by
      rw [hsB]; exact mul_le_mul_of_nonneg_left (hsBrow.trans hrowT) hL
    have hchild : length Z pr.1 + length Z pr.2 + L*(∑ i : (A''.map emb), wα i) ≤ B := by
      linarith
    obtain ⟨hbud₀, hcap₀⟩ := hinherit _ _ hsB0 (by rw [hsB]; exact hsBrow.trans_lt hnarrow)
      hchild
    have hadmP := (globalFace_admissible_iff (B := B₀) (lam := L₀) (cap := c₀) (M := 1)
      (length_nonneg Z pr.1 hZ1) (length_nonneg Z pr.2 hZ1) hsB0 hL₀).mpr
      ⟨by simpa only [mul_one] using hcap₀, by simpa only [mul_one] using hbud₀⟩
    have hb := hPZ (A''.map emb) (fun i => θα i) (fun i => wα i) (fun i => σα i)
      (fun i => t + vα i) 0 (|t|+height)
      (fun i => extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl i)
      (fun i => extend_forall T w 0 (fun x => x ≤ meshP)
        (fun j => (hwm j).trans (min_le_left _ _)) hmP.le i)
      (fun i => extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσlo le_rfl i)
      (fun i => extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσhi le_rfl i)
      (by positivity)
      (fun i => (abs_add_le _ _).trans (add_le_add (le_refl |t|)
        (extend_forall T v 0 (fun x => |x| ≤ height) hv (by simpa using hh) i)))
      1 le_rfl le_rfl Φ hΦ hΦp p' pr.1 pr.2 hp1 hp2 hadmP
    rw [Real.rpow_one] at hb
    exact hb
  have hrad := hfd E hE hleaves
  -- the profile cost of the phase-shifted profiles
  have hh1 : 1 ≤ 1+|t|+height := by have := abs_nonneg t; linarith
  have hctl' : p'.control SP ≤ Cc^2*(p.control Tc)*(1+|t|+height)^(2*n) := by
    have h0 := hctl (p.profile 0) (p.support 0) tt
    have h1 := hctl (p.profile 1) (p.support 1) tt
    have hpow : (1+‖tt‖)^n ≤ (1+|t|+height)^n :=
      pow_le_pow_left₀ (by positivity) (by rw [htt, Real.norm_eq_abs]; linarith) n
    have hq : 0 ≤ (1+‖tt‖)^n := by positivity
    have ha0 : 0 ≤ Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 0) := apply_nonneg _ _
    have ha1 : 0 ≤ Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 1) := apply_nonneg _ _
    have e : p'.control SP =
        SP.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile (p.profile 0) (1/4) (9/4)
          (by norm_num) (p.support 0) ((p.profile 0).smooth ⊤) tt) *
        SP.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile (p.profile 1) (1/4) (9/4)
          (by norm_num) (p.support 1) ((p.profile 1).smooth ⊤) tt) := by
      simp only [p', Profiles.control, sourceControl, independentProfiles, ite_true,
        show (1:Fin 2) ≠ 0 by decide, ite_false]
    have epc : p.control Tc = Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 0) *
        Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 1) := rfl
    rw [e, epc]
    calc _ ≤ (Cc*Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 0)*(1+‖tt‖)^n)*
          (Cc*Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 1)*(1+‖tt‖)^n) :=
          mul_le_mul h0 h1 (apply_nonneg _ _) (by positivity)
      _ ≤ (Cc*Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 0)*(1+|t|+height)^n)*
          (Cc*Tc.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile 1)*(1+|t|+height)^n) := by
          gcongr
      _ = _ := by ring
  have h0 : (1+|(0:ℝ)|+(|t|+height)) = 1+|t|+height := by rw [abs_zero]; ring
  have hcf : Cf ⟨T, r, A⟩ ≤ max Cm 1 := (hCm _).trans (le_max_left _ _)
  have hdg := diagonalControl_nonneg Φ
  have hpc := Profiles.control_nonneg p Tc
  have hpc' := Profiles.control_nonneg p' SP
  calc _ = ∑ z ∈ rows, initialWeight η η₀ Q Φ Z z*‖Frow z‖^2 :=
        Finset.sum_congr rfl (fun z _ => by rw [hrow z])
    _ ≤ radialEnergy Frow keep Φ Z := finite_le_radialEnergy Frow η η₀ Q Φ Z bΦ hZ0 hΦ hΦp rows
    _ ≤ (Cf ⟨T, r, A⟩*Z^(ε/2))*E := hrad
    _ ≤ (max Cm 1*Z^(ε/2))*(CP*diagonalControl Φ*
          (Cc^2*(p.control Tc)*(1+|t|+height)^(2*n))^2*(1+|t|+height)^dP*Z^((1:ℝ)+ε/2)) := by
        dsimp only [E]
        rw [h0]
        gcongr
    _ = _ := by
        have hz : Z^((1:ℝ)+ε) = Z^(ε/2)*Z^((1:ℝ)+ε/2) := by
          rw [← Real.rpow_add hZ0]; ring_nf
        rw [hz, pow_add]
        ring

end
end QRH.SilDensitySplit.CubeFree.Assembly
