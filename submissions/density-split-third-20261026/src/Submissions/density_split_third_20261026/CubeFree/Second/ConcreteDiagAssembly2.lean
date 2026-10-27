/- Copyright (c) 2026 Sil. Apache-2.0.
WP-J: the diagonal part of `hbudL/hbudR` (`ConcreteAssemblyAvg`): the explicit `Ed` of
`ConcreteDiagAssembly.diag_avg_uniform` is at most `(θ₀+θ_f+θ_t)·balancedBudget`.

* `balancedBudget_eq`: `balancedBudget s τ C D A Z loss = A·(reference τ C D V Z·N C/N D)·Z^loss`.
* Fixed-inducing rows (`exc_budget`): per allocation, `‖w_B‖²·V(r_B)·W_B·savedBudget(r_B)` is
  `W_B·(∏_{J_B}P)^{-4/3}·F_s·allocationShape s C B K W_B` (`exc_allocation_term`: residual volume
  `V/∏_J P` and `shape` homogeneity); with the selection size `SelF` (`AtotP·2^{|J|}·M·W/(∏_J P)^{4/3}
  ≤ Selmax`, CF: `Z^u·Z^u/Z^{4u/3} = Z^{2u/3}`), `W_B ≤ Wmax`, the first child scale
  `K = childScale Z κ n` and Window's `balanced_allocation_reference`, the total is
  `#B²·Selmax·#Ray²·Cexc·Hv·F_s·slotCost s·Z^{referenceExponent … Wmax}·reference·N C/N D`.
  The root supplies `hroot_f : that factor ≤ θ_f·A·Z^loss` (K1's `AlphaReferenceMargin` at the
  extra `(2/3)·log Wmax`, i.e. CF (7.1) with `+3u`).
* Zero frequency (`zero_budget`) and tails (`tail_budget`): `‖w_B‖ ≤ ∏M` and the selection sizes
  `Sel0`, `SelT`; root inputs `hroot_0` (CF: `A-1-c+4u ≤ -Δ-(λ₁-1-4a)S`) and `hroot_t`
  (arbitrary decay). -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteDiagAssembly
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstAllocatedRemainders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstMixedAllowance
open QRH.Record1252270103KernelMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentSourceProfileMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentFiniteProfileExceptional
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedPrincipalCentered MixedCommonCoefficient MixedFirstLiveSource MixedOriginalTail
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedFirstExceptionalNormalization
open MixedFirstExceptionalWindow MixedFirstAllocatedRemainders
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
open EisensteinSchwartzPoisson CenteredMomentCompleteCommon
open QRH.DensitySplitThird.CubeFree.FP
open QRH.DensitySplitThird.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) instDecEqSubtypeDiagBud {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### Scalar identities -/

theorem balancedBudget_eq (s : Source ι a b) (τ : Character) (C D : Id) (hC : C ≠ 0)
    (hD : D ≠ 0) (A Z loss : ℝ) :
    balancedBudget s τ C D A Z loss =
      A*(reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ)))*Z^loss := by
  have hc : (C.absNorm:ℝ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hd : (D.absNorm:ℝ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  unfold balancedBudget reference
  field_simp

theorem shape_div (V X p H L K W : ℝ) (hV : 0 ≤ V) (hX : 0 < X) (hp : 0 < p) :
    shape (V/X) p H L K W = (X^(4/3:ℝ))⁻¹*shape V p H L K W := by
  unfold shape
  rw [show V/X/p = (V/p)/X by ring, Real.div_rpow (div_nonneg hV hp.le) hX.le]
  field_simp

theorem shape_mono_W (V p H L K W W' : ℝ) (hV : 0 ≤ V) (hp : 0 < p) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hWW : W ≤ W') : shape V p H L K W ≤ shape V p H L K W' := by
  unfold shape
  have h1 : W^(7/3:ℝ) ≤ W'^(7/3:ℝ) := Real.rpow_le_rpow hW hWW (by norm_num)
  have h0 : 0 ≤ (V/p)^(4/3:ℝ)*K^(5/6:ℝ) := by positivity
  have h2 : 0 ≤ (L/H)^(-2/3:ℝ) := Real.rpow_nonneg (div_nonneg hL hH) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) h2

theorem allocationShape_mono_W (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G)
    (K W W' : ℝ) (hK : 0 ≤ K) (hW : 0 ≤ W) (hWW : W ≤ W') :
    allocationShape s G B K W ≤ allocationShape s G B K W' := by
  unfold allocationShape
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hpair := pairNorm_pos
    (d := (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
    (mul_ne_zero s.hd.1 (hB (Sum.inr 0))) (mul_ne_zero s.hd.2 (hB (Sum.inr 1)))
  have hprefix := prefixNormMax_pos
    (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))
    ⟨mul_ne_zero s.hd.1 (hB _),mul_ne_zero s.hd.2 (hB _)⟩
  have hT : 0 ≤ s.T*∏i : liveIndices B.val,s.P i.val := by
    have := (s.total_pos).le
    exact mul_nonneg this (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i.val)))
  exact mul_le_mul_of_nonneg_left (shape_mono_W _ _ _ _ K W W' hT hpair hK s.hL.le hprefix.le hW hWW)
    (sq_nonneg _)

/-! ### Profiles of the residual -/

theorem rest_fullMarkedCost_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) :
    fullMarkedCost (restSource s hB1 J) ≤ fullMarkedCost s := by
  rw [fullMarkedCost_eq, fullMarkedCost_eq]
  have hcard : Fintype.card (Rest J) ≤ Fintype.card ι := Fintype.card_subtype_le _
  have h1 : (1024:ℝ)^Fintype.card (Rest J) ≤ (1024:ℝ)^Fintype.card ι :=
    pow_le_pow_right₀ (by norm_num) hcard
  have hM : (∏ i, (restSource s hB1 J).M i) ≤ ∏ i, s.M i := by
    change (∏ j : Rest J, s.M j.val) ≤ _
    rw [(Finset.prod_subtype (Jᶜ) (fun i => by simp) s.M).symm]
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    · intro i _
      exact zero_le_one.trans (s.hM i)
    · intro i _ _
      exact s.hM i
  have hM0 : 0 ≤ ∏ i, (restSource s hB1 J).M i :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans ((restSource s hB1 J).hM i))
  have h2 := pow_le_pow_left₀ hM0 hM 3
  exact mul_le_mul h1 h2 (pow_nonneg hM0 3) (by positivity)

theorem rest_sourceProfile_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι)
    (Jd : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ) (hZ : 0 ≤ Z) :
    0 ≤ sourceProfile (restSource s hB1 J) Jd control Z ε ∧
      sourceProfile (restSource s hB1 J) Jd control Z ε ≤ sourceProfile s Jd control Z ε := by
  have hfactor : 0 ≤ (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
      (1+‖s.t₁‖+‖s.t₂‖)^Jd := by
    have := sourceControl_nonneg control s.W₁
    have := sourceControl_nonneg control s.W₂
    positivity
  exact ⟨mul_nonneg hfactor (fullMarkedCost_nonneg _),
    mul_le_mul_of_nonneg_left (rest_fullMarkedCost_le s hB1 J) hfactor⟩

/-- The residual of an allocation has at most the original source profile. -/
theorem restOf_sourceProfile_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (Jd : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ) (hZ : 0 ≤ Z) :
    (sourceProfile (restOf s hb cover G B J) Jd control Z ε)^2 ≤ (sourceProfile s Jd control Z ε)^2 := by
  have h1 := rest_sourceProfile_le (allocatedLiveSource s hb cover G B) (fun _ => rfl) J Jd control Z ε hZ
  have h2 := live_sourceProfile (allocationSource s hb cover G B) Jd control Z ε hZ
  exact pow_le_pow_left₀ h1.1 (h1.2.trans h2.2) 2

/-! ### Fixed-inducing rows -/

/-- One allocation's fixed-inducing term in the allocation shape of the ORIGINAL source. -/
theorem exc_allocation_term (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : Finset (liveIndices B.val)) (Jd : ℕ) (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε K W : ℝ)
    (hZ : 0 ≤ Z) (hW : 0 ≤ W) (hK : 0 ≤ K) :
    ‖allocWeight s G B‖^2*(sourceVolume (restOf s hb cover G B J)*W*
        savedBudget (restOf s hb cover G B J) Jd control Q Z ε K W) ≤
      W*((∏ j ∈ J, s.P j.val)^(4/3:ℝ))⁻¹*
        (fixedQCost Q*(sourceProfile s Jd control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*
        allocationShape s G B K W := by
  have hraw := ConcreteDiag.rest_saved_raw (allocatedLiveSource s hb cover G B) (fun _ => rfl) J ha Jd control Q Z ε K W
  have hX : 0 < ∏ j ∈ J, s.P j.val := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (s.hP j.val))
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hpair := pairNorm_pos
    (d := (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
    (mul_ne_zero s.hd.1 (hB (Sum.inr 0))) (mul_ne_zero s.hd.2 (hB (Sum.inr 1)))
  have hvol : sourceVolume (allocatedLiveSource s hb cover G B) = s.T*∏i : liveIndices B.val,s.P i.val := by
    dsimp only [allocatedLiveSource,liveSource,allocationSource,sourceVolume]
    rw [s.hpX]
  have hV0 : 0 ≤ s.T*∏i : liveIndices B.val,s.P i.val := by
    have := (s.total_pos).le
    exact mul_nonneg this (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i.val)))
  have hsh : shape (sourceVolume (allocatedLiveSource s hb cover G B) /
        ∏ j ∈ J, (allocatedLiveSource s hb cover G B).P j)
      (pairNorm (allocatedLiveSource s hb cover G B).d)
      (prefixNormMax (allocatedLiveSource s hb cover G B).d) (allocatedLiveSource s hb cover G B).L K W =
      ((∏ j ∈ J, s.P j.val)^(4/3:ℝ))⁻¹*
        shape (s.T*∏i : liveIndices B.val,s.P i.val)
          (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
          (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W := by
    rw [hvol]
    exact shape_div _ _ _ _ _ _ _ hV0 hX hpair
  have hprof := restOf_sourceProfile_le s hb cover G B J Jd control Z ε hZ
  have hF0 : 0 ≤ fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ) := by
    have := fixedQCost_nonneg Q; positivity
  have hshape0 : 0 ≤ shape (s.T*∏i : liveIndices B.val,s.P i.val)
          (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
          (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W := by
    have hprefix := prefixNormMax_pos
      (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) ⟨mul_ne_zero s.hd.1 (hB _),mul_ne_zero s.hd.2 (hB _)⟩
    unfold shape
    have := s.hL.le
    positivity
  have hrest : sourceVolume (restOf s hb cover G B J) * savedBudget (restOf s hb cover G B J) Jd control
      Q Z ε K W = fixedQCost Q*(sourceProfile (restOf s hb cover G B J) Jd control Z ε)^2*
        (16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ)*(((∏ j ∈ J, s.P j.val)^(4/3:ℝ))⁻¹*
        shape (s.T*∏i : liveIndices B.val,s.P i.val)
          (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
          (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W) := by
    rw [← hsh]; exact hraw
  have hXi : 0 ≤ ((∏ j ∈ J, s.P j.val)^(4/3:ℝ))⁻¹ := by positivity
  calc ‖allocWeight s G B‖^2*(sourceVolume (restOf s hb cover G B J)*W*
        savedBudget (restOf s hb cover G B J) Jd control Q Z ε K W)
      = W*((∏ j ∈ J, s.P j.val)^(4/3:ℝ))⁻¹*
          ((fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*(sourceProfile (restOf s hb cover G B J) Jd
            control Z ε)^2)*(‖allocWeight s G B‖^2*
          shape (s.T*∏i : liveIndices B.val,s.P i.val)
            (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
            (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W) := by
        rw [show sourceVolume (restOf s hb cover G B J)*W*
          savedBudget (restOf s hb cover G B J) Jd control Q Z ε K W = W*(sourceVolume
            (restOf s hb cover G B J) * savedBudget (restOf s hb cover G B J) Jd control Q Z ε K W)
          by ring, hrest]
        ring
    _ ≤ W*((∏ j ∈ J, s.P j.val)^(4/3:ℝ))⁻¹*
          ((fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*(sourceProfile s Jd control Z ε)^2)*
          (‖allocWeight s G B‖^2*
          shape (s.T*∏i : liveIndices B.val,s.P i.val)
            (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
            (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W) := by
        gcongr
    _ = _ := by unfold allocationShape allocWeight; ring


/-! ### Splitting `Ξ_B` and the three budgets -/

/-- Zero-frequency part of `Ξ_B` (factored). -/
def z0B (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (K : ℝ) (W Y : actualAllocations (tuplePools s) G → ℝ) (ε C0 : ℝ)
    (B : actualAllocations (tuplePools s) G) : ℝ :=
  (16*K*W B^4*‖paperRadialFourier ballProfile 0‖*
    (C0*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)))*
  ∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us, 1/(w.absNorm:ℝ)

/-- Fixed-inducing part of `Ξ_B` (factored). -/
def excB (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (K Lref : ℝ) (W : actualAllocations (tuplePools s) G → ℝ) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε α Bnorm δ εsum Ckernel A Csum : ℝ)
    (B : actualAllocations (tuplePools s) G) : ℝ :=
  (sourceVolume (restOf s hb cover G B (JB B))*W B*
      savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B))*
    ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*Z^(2*Bnorm*δ)*
      (Csum*Z^εsum))*
  ∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us, 1/(w.absNorm:ℝ)

/-- Tail part of `Ξ_B` (factored). -/
def tlB (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (W : actualAllocations (tuplePools s) G → ℝ) (controlT : Finset (ℕ×ℕ)) (Z saving Ct : ℝ)
    (B : actualAllocations (tuplePools s) G) : ℝ :=
  ((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card:ℝ)*
    (W B*(Ct*(profileCap (restOf s hb cover G B (JB B)))^2*
      controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)))

theorem xiB_eq (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (K Lref : ℝ) (W Y : actualAllocations (tuplePools s) G → ℝ) (J : ℕ)
    (control controlT : Finset (ℕ×ℕ)) (Q : Id)
    (Z ε α Bnorm δ εsum saving C0 Ckernel A Csum Ct : ℝ)
    (B : actualAllocations (tuplePools s) G) :
    xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
      C0 Ckernel A Csum Ct B =
    z0B s hb cover G JB Us K W Y ε C0 B +
      excB s hb cover G JB Us K Lref W J control Q Z ε α Bnorm δ εsum Ckernel A Csum B +
      tlB s hb cover G JB Us W controlT Z saving Ct B := by
  unfold xiB z0B excB tlB
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  have hrl : refLoss (restOf s hb cover G B (JB B)) Lref α = refLoss s Lref α := rfl
  refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ ?_) rfl
  · apply Finset.sum_congr rfl; intro w _; ring
  · apply Finset.sum_congr rfl; intro w _; rw [hrl]; ring

/-- **Fixed-inducing budget.** -/
theorem exc_budget (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (η τ : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D))
    (JB : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val)) (Us : Finset Id)
    (Lref : ℝ) (W M : actualAllocations (tuplePools s) C → ℝ) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε α Bnorm δ εsum Ckernel A Csum : ℝ)
    (Kfirst Tsec Csec ξ κ : ℝ) (n : ℤ) (Wmax Selmax Hv : ℝ)
    (hZ : 1 < Z) (hKf : 0 < Kfirst) (hCsec : 1 ≤ Csec) (hξ : 0 ≤ ξ) (hLref : 0 ≤ Lref)
    (hCk : 0 ≤ Ckernel) (hA : 0 ≤ A) (hCsum : 0 ≤ Csum) (hHv : 0 ≤ Hv)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hsec : Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s))
    (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hDC : (D.absNorm:ℝ)≤(C.absNorm:ℝ)^3)
    (hWmax : 0 < Wmax) (hW : ∀ B, 0 < W B ∧ W B ≤ Wmax) (hM : ∀ B, 0 ≤ M B)
    (hsel : ∀ B, AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
      W B * ((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹ ≤ Selmax)
    (hV : ∀ B, ∑ w ∈ Vset (allocatedLiveSource s hb cover C B) (fun _ => rfl) (JB B) Us,
      1/(w.absNorm:ℝ) ≤ Hv) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
        (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            excB s hb cover C JB Us (childScale Z κ n) Lref W J control Q Z ε α Bnorm δ εsum
              Ckernel A Csum B)) ≤
    ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      (Selmax*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*
          Z^(2*Bnorm*δ)*(Csum*Z^εsum))*Hv*
        (fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*
        (slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))*
        (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ)))) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hK0 : 0 ≤ childScale Z κ n := Real.rpow_nonneg hZ0.le _
  have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hd : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hD.1)
  have href : 0 < reference τ C D (sourceVolume s) Z := by
    have hτ := zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
    have hv := sourceVolume_pos s
    unfold reference; positivity
  set Cx := (Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*
    Z^(2*Bnorm*δ)*(Csum*Z^εsum) with hCx
  set Fs := fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ) with hFs
  set R2 := (Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ) with hR2
  have hCx0 : 0 ≤ Cx := by
    have := refLoss_nonneg s Lref α hLref
    rw [hCx]; positivity
  have hFs0 : 0 ≤ Fs := by have := fixedQCost_nonneg Q; rw [hFs]; positivity
  have hR20 : 0 ≤ R2 := by rw [hR2]; positivity
  have hper : ∀ B : actualAllocations (tuplePools s) C,
      ‖allocWeight s C B‖^2 *
        (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          (R2 * excB s hb cover C JB Us (childScale Z κ n) Lref W J control Q Z ε α Bnorm δ εsum
              Ckernel A Csum B)) ≤
      Selmax*R2*Cx*Hv*Fs*(slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))*
        (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) := by
    intro B
    obtain ⟨hW0, hWB⟩ := hW B
    have hX : 0 < ∏ j ∈ JB B, s.P j.val :=
      Finset.prod_pos (fun j _ => zero_lt_one.trans_le (s.hP j.val))
    have h1 := exc_allocation_term s ha hb cover C B (JB B) J control Q Z ε (childScale Z κ n) (W B)
      hZ0.le hW0.le hK0
    have h2 := allocationShape_mono_W s C B (childScale Z κ n) (W B) Wmax hK0 hW0.le hWB
    have h3 := balanced_allocation_reference s η τ C D hC hD hCD E B Kfirst Z Tsec Csec ξ κ Wmax
      hKf hZ hWmax hCsec hξ hmod hsec n hn hDC
    have h3' : allocationShape s C B (childScale Z κ n) Wmax ≤
        slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax)*
          (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) := by
      have e : allocationShape s C B (childScale Z κ n) Wmax =
          (allocationShape s C B (childScale Z κ n) Wmax/reference τ C D (sourceVolume s) Z*
            ((D.absNorm:ℝ)/(C.absNorm:ℝ)))*
          (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have hsum0 : 0 ≤ ∑ w ∈ Vset (allocatedLiveSource s hb cover C B) (fun _ => rfl) (JB B) Us,
        1/(w.absNorm:ℝ) := Finset.sum_nonneg (fun w _ => by positivity)
    have hP0 : 0 ≤ ‖allocWeight s C B‖^2*(sourceVolume (restOf s hb cover C B (JB B))*W B*
        savedBudget (restOf s hb cover C B (JB B)) J control Q Z ε (childScale Z κ n) (W B)) := by
      have := (sourceVolume_pos (restOf s hb cover C B (JB B))).le
      have := savedBudget_nonneg (restOf s hb cover C B (JB B)) J control Q Z ε (childScale Z κ n)
        (W B) (Real.rpow_pos_of_pos hZ0 _) hW0
      have := hW0.le
      positivity
    have hAX : 0 ≤ AtotP (allocatedLiveSource s hb cover C B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) :=
      mul_nonneg (AtotP_nonneg _ _) (by have := hM B; positivity)
    have haS0 : 0 ≤ allocationShape s C B (childScale Z κ n) (W B) := by
      have := (allocationShape_mono_W s C B (childScale Z κ n) 0 (W B) hK0 le_rfl hW0.le)
      refine le_trans ?_ this
      unfold allocationShape shape
      rw [Real.zero_rpow (by norm_num)]
      simp
    have hXi : 0 ≤ ((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹ := by positivity
    have hSel0 : 0 ≤ Selmax := le_trans (by
      have := hW0.le; positivity) (hsel B)
    calc ‖allocWeight s C B‖^2 *
        (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          (R2 * excB s hb cover C JB Us (childScale Z κ n) Lref W J control Q Z ε α Bnorm δ εsum
              Ckernel A Csum B))
        = (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B))*
            R2*Cx*(∑ w ∈ Vset (allocatedLiveSource s hb cover C B) (fun _ => rfl) (JB B) Us,
              1/(w.absNorm:ℝ))*
            (‖allocWeight s C B‖^2*(sourceVolume (restOf s hb cover C B (JB B))*W B*
              savedBudget (restOf s hb cover C B (JB B)) J control Q Z ε (childScale Z κ n) (W B))) := by
          unfold excB; rw [hCx]; ring
      _ ≤ (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B))*
            R2*Cx*Hv*(W B*((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹*Fs*
              allocationShape s C B (childScale Z κ n) (W B)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hV B) (by positivity)) h1 hP0 (by positivity)
      _ ≤ (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B))*
            R2*Cx*Hv*(W B*((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹*Fs*
              allocationShape s C B (childScale Z κ n) Wmax) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left h2 (by have := hW0.le; positivity)
      _ = (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B)*
            W B*((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹)*
            (R2*Cx*Hv*Fs*allocationShape s C B (childScale Z κ n) Wmax) := by ring
      _ ≤ Selmax*(R2*Cx*Hv*Fs*allocationShape s C B (childScale Z κ n) Wmax) := by
          apply mul_le_mul_of_nonneg_right (hsel B)
          have := haS0.trans h2
          positivity
      _ ≤ Selmax*(R2*Cx*Hv*Fs*(slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax)*
            (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ hSel0
          apply mul_le_mul_of_nonneg_left h3' (by positivity)
      _ = _ := by ring
  calc _ ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
        ∑ _B : actualAllocations (tuplePools s) C,
          Selmax*R2*Cx*Hv*Fs*(slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))*
            (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => hper B) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring


theorem allocWeight_sq_le (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G) :
    ‖allocWeight s G B‖^2 ≤ (∏ i, s.M i)^2 :=
  pow_le_pow_left₀ (norm_nonneg _) (frozen_scalar_bound s G B) 2

/-- **Zero-frequency budget.** -/
theorem zero_budget (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (K : ℝ) (W M Y : actualAllocations (tuplePools s) G → ℝ) (ε C0 Hv S0 : ℝ)
    (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hW : ∀ B, 0 ≤ W B) (hM : ∀ B, 0 ≤ M B) (hY : ∀ B, 0 ≤ Y B)
    (hV : ∀ B, ∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
      1/(w.absNorm:ℝ) ≤ Hv)
    (hsel0 : ∀ B, AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
      (W B^4*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)) ≤ S0) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
        (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            z0B s hb cover G JB Us K W Y ε C0 B)) ≤
    ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ)^2 *
      ((∏ i, s.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (16*K*‖paperRadialFourier ballProfile 0‖*C0)*Hv*S0) := by
  set R2 := (Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ) with hR2
  have hR20 : 0 ≤ R2 := by rw [hR2]; positivity
  have hper : ∀ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
        (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          (R2 * z0B s hb cover G JB Us K W Y ε C0 B)) ≤
      (∏ i, s.M i)^2*R2*(16*K*‖paperRadialFourier ballProfile 0‖*C0)*Hv*S0 := by
    intro B
    have hAX : 0 ≤ AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) :=
      mul_nonneg (AtotP_nonneg _ _) (by have := hM B; positivity)
    have hsum0 : 0 ≤ ∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
        1/(w.absNorm:ℝ) := Finset.sum_nonneg (fun w _ => by positivity)
    have hS : 0 ≤ AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (W B^4*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)) := by
      have := hY B; have := hW B; positivity
    have hS0 : 0 ≤ S0 := hS.trans (hsel0 B)
    have hc : 0 ≤ 16*K*‖paperRadialFourier ballProfile 0‖*C0 := by positivity
    calc _ = ‖allocWeight s G B‖^2*R2*(16*K*‖paperRadialFourier ballProfile 0‖*C0)*
          (∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us, 1/(w.absNorm:ℝ))*
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            (W B^4*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε))) := by
          unfold z0B; ring
      _ ≤ (∏ i, s.M i)^2*R2*(16*K*‖paperRadialFourier ballProfile 0‖*C0)*Hv*S0 := by
          have hw := allocWeight_sq_le s G B
          have hHv : 0 ≤ Hv := hsum0.trans (hV B)
          apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hw hR20) hc) (hV B) hsum0 (by positivity))
            (hsel0 B) hS (by positivity)
  calc _ ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ _B : actualAllocations (tuplePools s) G,
          (∏ i, s.M i)^2*R2*(16*K*‖paperRadialFourier ballProfile 0‖*C0)*Hv*S0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => hper B) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Tail budget.** -/
theorem tail_budget (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (W M : actualAllocations (tuplePools s) G → ℝ) (controlT : Finset (ℕ×ℕ)) (Z saving Ct St : ℝ)
    (hZ : 0 < Z) (hCt : 0 ≤ Ct) (hW : ∀ B, 0 ≤ W B) (hM : ∀ B, 0 ≤ M B)
    (hselT : ∀ B, AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
      (((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card:ℝ)*W B*
        (profileCap (restOf s hb cover G B (JB B)))^2) ≤ St) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
        (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            tlB s hb cover G JB Us W controlT Z saving Ct B)) ≤
    ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ)^2 *
      ((∏ i, s.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*St) := by
  set R2 := (Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ) with hR2
  have hR20 : 0 ≤ R2 := by rw [hR2]; positivity
  have hcT : 0 ≤ controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
  have hper : ∀ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
        (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          (R2 * tlB s hb cover G JB Us W controlT Z saving Ct B)) ≤
      (∏ i, s.M i)^2*R2*(Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*St := by
    intro B
    have hS : 0 ≤ AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card:ℝ)*W B*
          (profileCap (restOf s hb cover G B (JB B)))^2) := by
      have := AtotP_nonneg (allocatedLiveSource s hb cover G B) (JB B)
      have := hW B; have := hM B; positivity
    have hc : 0 ≤ Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving) := by
      positivity
    calc _ = ‖allocWeight s G B‖^2*R2*(Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
            Z^(-saving))*
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            (((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card:ℝ)*W B*
              (profileCap (restOf s hb cover G B (JB B)))^2)) := by
          unfold tlB; ring
      _ ≤ _ := by
          have hw := allocWeight_sq_le s G B
          apply mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hw hR20) hc) (hselT B) hS (by positivity)
  calc _ ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ _B : actualAllocations (tuplePools s) G,
          (∏ i, s.M i)^2*R2*(Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*St :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => hper B) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The diagonal part of `hbud`.** The explicit `Ed` of `diag_avg_uniform` (at the first child
scale `K = childScale Z κ n`) is at most `(θ₀+θ_f+θ_t)·balancedBudget`, given the selection sizes
`Sel0`/`Selmax`/`SelT`, the seed mass `Hv` and the three root-level inputs `hroot0`, `hrootf`,
`hroott`. -/
theorem diag_budget (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (η τ : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D))
    (JB : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val)) (Us : Finset Id)
    (Lref : ℝ) (W M Y : actualAllocations (tuplePools s) C → ℝ) (J : ℕ)
    (control controlT : Finset (ℕ×ℕ)) (Q : Id)
    (Z ε α Bnorm δ εsum saving C0 Ckernel A Csum Ct : ℝ)
    (Kfirst Tsec Csec ξ κ : ℝ) (n : ℤ) (Wmax Selmax Hv S0 St Abud loss θ0 θf θt : ℝ)
    (hZ : 1 < Z) (hKf : 0 < Kfirst) (hCsec : 1 ≤ Csec) (hξ : 0 ≤ ξ) (hLref : 0 ≤ Lref)
    (hC0 : 0 ≤ C0) (hCk : 0 ≤ Ckernel) (hA : 0 ≤ A) (hCsum : 0 ≤ Csum) (hCt : 0 ≤ Ct)
    (hHv : 0 ≤ Hv)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hsec : Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s))
    (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hDC : (D.absNorm:ℝ)≤(C.absNorm:ℝ)^3)
    (hWmax : 0 < Wmax) (hW : ∀ B, 0 < W B ∧ W B ≤ Wmax) (hM : ∀ B, 0 ≤ M B) (hY : ∀ B, 0 ≤ Y B)
    (hV : ∀ B, ∑ w ∈ Vset (allocatedLiveSource s hb cover C B) (fun _ => rfl) (JB B) Us,
      1/(w.absNorm:ℝ) ≤ Hv)
    (hsel0 : ∀ B, AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
      (W B^4*(profileCap (restOf s hb cover C B (JB B)))^2*(Y B)^(1+ε)) ≤ S0)
    (hself : ∀ B, AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
      W B * ((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹ ≤ Selmax)
    (hselT : ∀ B, AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
      (((Vset (allocatedLiveSource s hb cover C B) (fun _ => rfl) (JB B) Us).card:ℝ)*W B*
        (profileCap (restOf s hb cover C B (JB B)))^2) ≤ St)
    (hroot0 : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      ((∏ i, s.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (16*childScale Z κ n*‖paperRadialFourier ballProfile 0‖*C0)*Hv*S0) ≤
        θ0*balancedBudget s τ C D Abud Z loss)
    (hrootf : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      (Selmax*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*
          Z^(2*Bnorm*δ)*(Csum*Z^εsum))*Hv*
        (fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*
        (slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))) ≤ θf*Abud*Z^loss)
    (hroott : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      ((∏ i, s.M i)^2*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        (Ct*controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving))*St) ≤
        θt*balancedBudget s τ C D Abud Z loss) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
        (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            xiB s hb cover C JB Us (childScale Z κ n) Lref W Y J control controlT Q Z ε α Bnorm δ
              εsum saving C0 Ckernel A Csum Ct B)) ≤
      (θ0+θf+θt)*balancedBudget s τ C D Abud Z loss := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hK0 : 0 ≤ childScale Z κ n := Real.rpow_nonneg hZ0.le _
  have hsplit : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
        (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
            xiB s hb cover C JB Us (childScale Z κ n) Lref W Y J control controlT Q Z ε α Bnorm δ
              εsum saving C0 Ckernel A Csum Ct B)) =
      ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
          (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
              z0B s hb cover C JB Us (childScale Z κ n) W Y ε C0 B)) +
      ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
          (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
              excB s hb cover C JB Us (childScale Z κ n) Lref W J control Q Z ε α Bnorm δ εsum
                Ckernel A Csum B)) +
      ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) C, ‖allocWeight s C B‖^2 *
          (AtotP (allocatedLiveSource s hb cover C B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
              tlB s hb cover C JB Us W controlT Z saving Ct B)) := by
    rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro B _
    rw [xiB_eq]; ring
  rw [hsplit]
  have h0 := zero_budget s hb cover C JB Us (childScale Z κ n) W M Y ε C0 Hv S0 hK0 hC0
    (fun B => (hW B).1.le) hM hY hV hsel0
  have hf := exc_budget s ha hb cover η τ C D hC hD hCD E JB Us Lref W M J control Q Z ε α Bnorm δ εsum
    Ckernel A Csum Kfirst Tsec Csec ξ κ n Wmax Selmax Hv hZ hKf hCsec hξ hLref hCk hA hCsum hHv
    hmod hsec hn hDC hWmax hW hM hself hV
  have ht := tail_budget s hb cover C JB Us W M controlT Z saving Ct St hZ0 hCt
    (fun B => (hW B).1.le) hM hselT
  have hbud := balancedBudget_eq s τ C D hC.1 hD.1 Abud Z loss
  have hf' : ((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
      (Selmax*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
        ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*
          Z^(2*Bnorm*δ)*(Csum*Z^εsum))*Hv*
        (fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*
        (slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))*
        (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ)))) ≤
      θf*balancedBudget s τ C D Abud Z loss := by
    have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
    have hd : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hD.1)
    have href : 0 ≤ reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ)) := by
      unfold reference; positivity
    rw [hbud]
    calc _ = (((Finset.univ : Finset (actualAllocations (tuplePools s) C)).card : ℝ)^2 *
          (Selmax*((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*
            ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*refLoss s Lref α*
              Z^(2*Bnorm*δ)*(Csum*Z^εsum))*Hv*
            (fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*
            (slotCost s*Z^(referenceExponent s η Kfirst Z Csec ξ κ Wmax))))*
          (reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) := by ring
      _ ≤ (θf*Abud*Z^loss)*(reference τ C D (sourceVolume s) Z*((C.absNorm:ℝ)/(D.absNorm:ℝ))) :=
          mul_le_mul_of_nonneg_right hrootf href
      _ = _ := by ring
  linarith [h0.trans hroot0, hf.trans hf', ht.trans hroott]

end
end QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
