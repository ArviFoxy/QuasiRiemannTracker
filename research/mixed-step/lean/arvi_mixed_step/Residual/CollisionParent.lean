/- Mixed source step, L3: new in this submission; uses Collet's and the baseline's definitions by
import.

The residual of a collision family is the child of the shortened parent.

For an allocation `B` of `s`, a block `J ⊆ live(B)` and side products `D₀, D₁`, the parent of a
collision family is `collParent s J D₀ D₁ = (s.restrict J).shortenPlains D₀ D₁`.

* `collAlloc_mem`: `B` read on the remaining slots (`restPart J B`) is an allocation of
  `collParent` as soon as one tuple of the family residual has its ordinary pair coprime to `C`.
* `collChild_match`: the residual input of the family (pattern `Q ⊆ J`) of the child of `B` and the
  child of `collParent` at that allocation have the same source data along `collChildEquiv`. -/
import Submissions.arvi_mixed_step.Residual.CollisionTransfer

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion CenteredMomentFirstSectors
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
open RayFourExpansion CanonicalQuadraticSieve
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.MixedStep.Transfer QRH.MixedStep.Collision
local notation "O" => ActualEisensteinCubic.O

theorem residualPool_comm (a b : Ideal O) (ha : a ≠ 0) (hb : b ≠ 0) (S : Finset (Ideal O)) :
    residualPool a ha (residualPool b hb S) = residualPool b hb (residualPool a ha S) := by
  ext I
  simp only [mem_residualPool]
  rw [mul_left_comm]

theorem supportExtract_idem (I : Ideal O) (S : Finset (Ideal O)) :
    supportExtract (supportExtract I S) S = supportExtract I S := by
  show ((normalizedFactors (supportExtract I S)).filter (fun P => P ∈ S)).prod = supportExtract I S
  rw [supportExtract_factors, Multiset.filter_filter]
  simp only [and_self]
  rfl

theorem supportExtract_coprime (I C : Ideal O) (h : IsCoprime I C) :
    supportExtract I (primeSupport C) = 1 := by
  unfold supportExtract
  have he : (normalizedFactors I).filter (fun P => P ∈ primeSupport C) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP hPC
    have hpr : Prime P := prime_of_normalized_factor P hP
    have h1 : P ∣ I := dvd_of_mem_normalizedFactors hP
    have h2 : P ∣ C := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPC)
    exact hpr.not_isUnit (h.isUnit_of_dvd' h1 h2)
  rw [he, Multiset.prod_zero]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The parent of a collision family. -/
abbrev collParent (s : Input α) (J : Finset α) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0) :
    Input {i // i ∉ J} :=
  (s.restrict J).shortenPlains D₀ D₁ h₀ h₁

theorem restPart_prod_alloc (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) : ∏ i, restPart J B.val i = C := by
  obtain ⟨_, hprod⟩ := Finset.mem_filter.mp B.property
  refine Eq.trans ?_ hprod
  simp only [Fintype.prod_sum_type, restPart, Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [prod_split J (fun i => B.val (Sum.inl i))]
  have h1 : ∏ j : J, B.val (Sum.inl j.val) = 1 :=
    Finset.prod_eq_one (fun j _ => live_one B hJ j.val j.property)
  rw [h1, one_mul]

/-- **The allocation of the shortened parent.** -/
theorem collAlloc_mem (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (τ : HeckeFamily.Character) (t : ℝ)
    (Q : Finset (liveIndices B.val)) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0)
    (a : Tuple {i : {i : liveIndices B.val // i ∉ Q} // i ∉ restBlock (liveBlock B J) Q})
    (ha : a ∈ Fintype.piFinset
      (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
        (restBlock (liveBlock B J) Q)).pools)
    (hcop : IsCoprime (a (Sum.inr 0) * a (Sum.inr 1)) C) :
    restPart J B.val ∈ actualAllocations (collParent s J D₀ D₁ h₀ h₁).pools C := by
  obtain ⟨hlab, _⟩ := Finset.mem_filter.mp B.property
  obtain ⟨v, hv, hvB⟩ := Finset.mem_image.mp hlab
  have hv' := (mem_pools_iff s v).mp ((mem_piFinset_any _ _ _).mp hv)
  have ha' := (mem_pools_iff _ a).mp (Fintype.mem_piFinset.mp ha)
  have hB0 : B.val (Sum.inr 0) ≠ 0 := alloc_ne s C B _
  have hB1 : B.val (Sum.inr 1) ≠ 0 := alloc_ne s C B _
  have ha0 : a (Sum.inr 0) ≠ 0 := (residualInput _ _).plain₁_ne _ ha'.2.1
  have ha1 : a (Sum.inr 1) ≠ 0 := (residualInput _ _).plain₂_ne _ ha'.2.2
  let w : Tuple {i // i ∉ J} :=
    Sum.elim (fun i => v (Sum.inl i.val)) (fun k => B.val (Sum.inr k) * a (Sum.inr k))
  have hw : ∀ x, w x ∈ (collParent s J D₀ D₁ h₀ h₁).pools x := by
    apply (mem_pools_iff _ w).mpr
    refine ⟨fun i => hv'.1 i.val, ?_, ?_⟩
    · apply (mem_shortenPlains_plain₁ (s.restrict J) _ _ _ _ _).mpr
      have h := ha'.2.1
      change a (Sum.inr 0) ∈ residualPool D₀ h₀ (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁) at h
      rw [mem_residualPool, mem_residualPool] at h
      change D₀ * (B.val (Sum.inr 0) * a (Sum.inr 0)) ∈ s.plain₁
      rwa [mul_left_comm]
    · apply (mem_shortenPlains_plain₂ (s.restrict J) _ _ _ _ _).mpr
      have h := ha'.2.2
      change a (Sum.inr 1) ∈ residualPool D₁ h₁ (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂) at h
      rw [mem_residualPool, mem_residualPool] at h
      change D₁ * (B.val (Sum.inr 1) * a (Sum.inr 1)) ∈ s.plain₂
      rwa [mul_left_comm]
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w, (mem_piFinset_any _ _ _).mpr hw, ?_⟩, ?_⟩
  · funext x
    cases x with
    | inl i => exact congrFun hvB (Sum.inl i.val)
    | inr k =>
      have hk : supportExtract (B.val (Sum.inr k)) (primeSupport C) = B.val (Sum.inr k) := by
        rw [← congrFun hvB (Sum.inr k), supportExtract_idem]
      have hak : IsCoprime (a (Sum.inr k)) C := by
        fin_cases k
        · exact hcop.of_mul_left_left
        · exact hcop.of_mul_left_right
      have hk0 : a (Sum.inr k) ≠ 0 := by
        fin_cases k
        · exact ha0
        · exact ha1
      change supportExtract (B.val (Sum.inr k) * a (Sum.inr k)) (primeSupport C) =
        B.val (Sum.inr k)
      rw [supportExtract_mul _ _ (alloc_ne s C B _) hk0, hk, supportExtract_coprime _ C hak,
        mul_one]
  · exact restPart_prod_alloc s C B J hJ

/-- The slot equivalence between a family residual and the child of the shortened parent. -/
def collChildEquiv (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) (J : Finset α)
    (Q : Finset (liveIndices B.val)) (hQ : Q ⊆ liveBlock B J) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0)
    (h₁ : D₁ ≠ 0) (hmem : restPart J B.val ∈ actualAllocations (collParent s J D₀ D₁ h₀ h₁).pools C) :
    {i : {i : liveIndices B.val // i ∉ Q} // i ∉ restBlock (liveBlock B J) Q} ≃
      liveIndices (⟨restPart J B.val, hmem⟩ :
        actualAllocations (collParent s J D₀ D₁ h₀ h₁).pools C).val where
  toFun i := ⟨⟨i.val.val.val, fun h =>
      i.property (Finset.mem_subtype.mpr ((mem_liveBlock B J _).mpr h))⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp i.val.val.property).2⟩⟩
  invFun k := ⟨⟨⟨k.val.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp k.property).2⟩⟩,
      fun h => k.val.property ((mem_liveBlock B J _).mp (hQ h))⟩,
    fun h => k.val.property ((mem_liveBlock B J _).mp (Finset.mem_subtype.mp h))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The family residual and the child of the shortened parent have the same source data.** -/
theorem collChild_match (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (Q : Finset (liveIndices B.val)) (hQ : Q ⊆ liveBlock B J) (D₀ D₁ : Ideal O)
    (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0)
    (hmem : restPart J B.val ∈ actualAllocations (collParent s J D₀ D₁ h₀ h₁).pools C)
    (τ τ' : HeckeFamily.Character) (t t' : ℝ) :
    SlotMatch (collChildEquiv s C B J Q hQ D₀ D₁ h₀ h₁ hmem)
      (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
        (restBlock (liveBlock B J) Q))
      (child (collParent s J D₀ D₁ h₀ h₁) C R ⟨restPart J B.val, hmem⟩ τ' t') where
  slots _ := rfl
  ν _ := rfl
  W _ := rfl
  P _ := rfl
  plain₁ := residualPool_comm (B.val (Sum.inr 0)) D₀ (alloc_ne s C B _) h₀ s.plain₁
  plain₂ := residualPool_comm (B.val (Sum.inr 1)) D₁ (alloc_ne s C B _) h₁ s.plain₂
  W₁ := rfl
  W₂ := rfl
  X₁ := div_right_comm _ _ _
  X₂ := div_right_comm _ _ _
  Y₁ := div_right_comm _ _ _
  Y₂ := div_right_comm _ _ _

/-! ### The family residual energy -/

/-- The energy of a collision family at its shortened parent (zero when `restPart J B` is not an
allocation of the parent; then the family residual vanishes, `collResidual_eq`). -/
def collEnergy (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (J : Finset α) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0)
    (τ : HeckeFamily.Character) (t T H : ℝ) : ℝ :=
  if hmem : restPart J B.val ∈ actualAllocations (collParent s J D₀ D₁ h₀ h₁).pools C then
    correctedChildGaussEnergy (collParent s J D₀ D₁ h₀ h₁) 1 1 1 1 C R L' (fun _ => 1) P
      ⟨restPart J B.val, hmem⟩ τ t T H
  else 0

theorem collEnergy_nonneg (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (J : Finset α) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0)
    (τ : HeckeFamily.Character) (t T H : ℝ) (hH : 0 < H) :
    0 ≤ collEnergy s C R L' P B J D₀ D₁ h₀ h₁ τ t T H := by
  unfold collEnergy
  split_ifs
  · exact corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH
  · exact le_refl 0

/-- **The family residual is the energy at the shortened parent.** -/
theorem collResidual_eq (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val)
    (τ : HeckeFamily.Character) (t : ℝ) (Q : Finset (liveIndices B.val)) (hQ : Q ⊆ liveBlock B J)
    (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0) (τ' : HeckeFamily.Character) (T' H' : ℝ) :
    (gaussEnergy Finset.univ
      (sourceGenerator (finiteColumns (Fintype.piFinset
        (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
          (restBlock (liveBlock B J) Q)).pools)))
      (sourceGenerator_supported (finiteColumns (Fintype.piFinset
        (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
          (restBlock (liveBlock B J) Q)).pools)))
      (fun I : supportedColumns (finiteColumns (Fintype.piFinset
          (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
            (restBlock (liveBlock B J) Q)).pools)) =>
        CoupledFirst.coefficient
            (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
              (restBlock (liveBlock B J) Q))
            (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L' I *
          ((Real.sqrt T' : ℂ)⁻¹ * rowWeight τ' fixedBadMask 1 1 t I)) ballProfile H').re =
      collEnergy s C R L' P B J D₀ D₁ h₀ h₁ τ' t T' H' := by
  unfold collEnergy
  split_ifs with hmem
  · rw [congrArg Complex.re (energy_transport (collChildEquiv s C B J Q hQ D₀ D₁ h₀ h₁ hmem)
      (collChild_match s C R B J Q hQ D₀ D₁ h₀ h₁ hmem τ τ' t t)
      (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val)
      (poolCorr P C) (R * C) L'
      (fun I => (Real.sqrt T' : ℂ)⁻¹ * rowWeight τ' fixedBadMask 1 1 t I) ballProfile H')]
    unfold correctedChildGaussEnergy
    dsimp only
    have hmk : markedProduct (restPart J B.val) = markedProduct B.val :=
      allocRestrict_marked s C B J hJ
    rw [hmk]
    generalize child (collParent s J D₀ D₁ h₀ h₁) C R ⟨restPart J B.val, hmem⟩ τ' t = s''
    apply congrArg Complex.re
    exact source_gauss_energy_pool_decEq
      (ι := liveIndices (⟨restPart J B.val, hmem⟩ :
        actualAllocations (collParent s J D₀ D₁ h₀ h₁).pools C).val) _ _ s''.pools
      (fun I => CoupledFirst.coefficient s''
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L' I *
        ((Real.sqrt T' : ℂ)⁻¹ * rowWeight τ' fixedBadMask 1 1 t I)) ballProfile H'
  · -- no surviving tuple: the family residual vanishes
    have htc : ∀ a ∈ Fintype.piFinset
        (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
          (restBlock (liveBlock B J) Q)).pools,
        CoupledFirst.tupleCoefficient
          (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
            (restBlock (liveBlock B J) Q))
          (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
            (1 * markedProduct B.val) (poolCorr P C)) (R * C) L' a = 0 := by
      intro a ha
      by_contra hne
      apply hmem
      have hc := profile_coprime _ _ _ _ a hne
      have hdvd : a (Sum.inr 0) * a (Sum.inr 1) ∣ finiteTupleProduct a := by
        rw [finiteTupleProduct_split]
        exact dvd_mul_left _ _
      exact collAlloc_mem s C R B J hJ τ t Q D₀ D₁ h₀ h₁ a ha
        ((hc.of_isCoprime_of_dvd_left hdvd).of_isCoprime_of_dvd_right (dvd_mul_left C R))
    have hcoef : ∀ I : Ideal O, CoupledFirst.coefficient
        (residualInput (((child s C R B τ t).restrict Q).shortenPlains D₀ D₁ h₀ h₁)
          (restBlock (liveBlock B J) Q))
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L' I = 0 := by
      intro I
      rw [coefficient_eq_piFinset]
      unfold finiteColumnCoefficient
      exact Finset.sum_eq_zero (fun a ha => htc a (Finset.mem_filter.mp ha).1)
    simp only [hcoef, zero_mul]
    rw [gaussEnergy_zero_coeff, Complex.zero_re]

/-- Rescaling the normalization of a source energy. -/
theorem energy_rescale {β : Type*} (S : Finset β) (a : β → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c w : β → ℂ) (Φ : 𝓢(ℝ, ℂ)) (H T₁ T₂ : ℝ)
    (h₁ : 0 < T₁) (h₂ : 0 < T₂) :
    (gaussEnergy S a ha (fun i => c i * ((Real.sqrt T₁ : ℂ)⁻¹ * w i)) Φ H).re =
      (gaussEnergy S a ha (fun i => c i * ((Real.sqrt T₂ : ℂ)⁻¹ * w i)) Φ H).re * (T₂ / T₁) := by
  have e : ∀ T : ℝ, (fun i => c i * ((Real.sqrt T : ℂ)⁻¹ * w i)) =
      fun i => (Real.sqrt T : ℂ)⁻¹ * (c i * w i) := fun T => funext fun i => by ring
  rw [e T₁, e T₂, CenteredMomentGaussNormalization.gaussEnergy_central _ _ _ _ T₁ h₁,
    CenteredMomentGaussNormalization.gaussEnergy_central _ _ _ _ T₂ h₂]
  field_simp

theorem corrected_energy_rescale {β : Type*} [Fintype β] [DecidableEq β] (s : Input β)
    (A₁ A₂ D K C R L : Ideal O) (F : Ideal O → ℂ) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t T₁ T₂ H : ℝ)
    (h₁ : 0 < T₁) (h₂ : 0 < T₂) :
    correctedChildGaussEnergy s A₁ A₂ D K C R L F P B τ t T₁ H =
      correctedChildGaussEnergy s A₁ A₂ D K C R L F P B τ t T₂ H * (T₂ / T₁) := by
  unfold correctedChildGaussEnergy
  dsimp only
  exact energy_rescale _ _ _ _ _ _ H T₁ T₂ h₁ h₂

theorem collEnergy_rescale (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (J : Finset α) (D₀ D₁ : Ideal O) (h₀ : D₀ ≠ 0) (h₁ : D₁ ≠ 0)
    (τ : HeckeFamily.Character) (t T₁ T₂ H : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) :
    collEnergy s C R L' P B J D₀ D₁ h₀ h₁ τ t T₁ H =
      collEnergy s C R L' P B J D₀ D₁ h₀ h₁ τ t T₂ H * (T₂ / T₁) := by
  unfold collEnergy
  split_ifs
  · exact corrected_energy_rescale _ _ _ _ _ _ _ _ _ _ _ _ t T₁ T₂ H hT₁ hT₂
  · rw [zero_mul]

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.collResidual_eq
#print axioms QRH.MixedStep.Residual.collEnergy_rescale
#print axioms QRH.MixedStep.Residual.collAlloc_mem
#print axioms QRH.MixedStep.Residual.collChild_match
