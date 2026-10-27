/- Copyright (c) 2026 Sil. Apache-2.0.
WP-J: `diag_avg_uniformT`, the diagonal bound of `ConcreteDiagAssembly.diag_avg_uniform` at an
allocation-dependent second-step frequency `T B` (`diagAvgT`). -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteAssemblyAvgT
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteDiagAssembly
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteDiag
import Submissions.density_split_third_20261026.CubeFree.FP.MixedLocalizedDictionary
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstExceptionalWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentChildRows CenteredMomentFirstColumns
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open QRH.Record1252270103KernelMass
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource
open MixedOriginalTail MixedOriginalNormCap MixedOriginalTailPower MixedPoissonLocalization
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedLocalizedDictionary
open QRH.DensitySplitThird.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeDiagAsmT {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-- **`diag_avg_uniform` with an allocation-dependent second-step frequency `T B`.** All constants (degree, seminorm set, kernel,
exceptional, summation, zero and tail constants) are fixed before `Z` and before the source,
the allocations, the selected blocks, the widths and the multiplicities; the remaining
hypotheses are the structural caps of each residual `r_B` (as in FP's applications). -/
theorem diag_avg_uniformT (N : ℕ)
    (α Bcap a b ε δ Bnorm Lrad Cr εsum Btl ξr saving : ℝ)
    (hα0 : 0≤α) (hα23 : α<2/3) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum)
    (hBtl : 0≤Btl) (hξr : 0<ξr) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃A Csum C0 Ct : ℝ,∃controlT : Finset (ℕ×ℕ),0<A ∧ 0<Csum ∧ 0<C0 ∧ 0<Ct ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,∀G : Id,
      ∀JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val),
      ∀(Us : Finset Id)(τ : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(K Lref : ℝ)(T W M Y : actualAllocations (tuplePools s) G → ℝ),
      0<K → 0<Lref → Lref≤s.L → K≤Z^Btl →
      (∀B, 0≤T B ∧ frequencyRadius (T B) Z ξr≤Cr*Z^Lrad ∧ T B≤Z^Btl) →
      (∀B, 0<W B ∧ W B≤Z^Btl ∧ (W B)⁻¹≤Z^Btl ∧ 0≤M B ∧ 1≤Y B ∧ Y B≤Z^Btl) →
      (∀B, Fintype.card (Rest (JB B))≤N ∧
        ((restOf s hb cover G B (JB B)).Fhole.absNorm:ℝ)≤Z^Bcap ∧
        (∏i,2*(restOf s hb cover G B (JB B)).P i)≤Z^Bcap ∧
        poolCap (restOf s hb cover G B (JB B))≤Z^Bnorm ∧
        poolCap (restOf s hb cover G B (JB B))≤Z^Btl ∧
        sourceNormCap (restOf s hb cover G B (JB B)).P b (restOf s hb cover G B (JB B)).T
          (restOf s hb cover G B (JB B)).d≤Z^Bnorm ∧
        sourceNormCap (restOf s hb cover G B (JB B)).P b (restOf s hb cover G B (JB B)).T
          (restOf s hb cover G B (JB B)).d≤Y B ∧
        (Y B)^2/(16*K*W B^4)≤T B ∧
        ∀ξ : RayCharacter, familyConductorBudget (restOf s hb cover G B (JB B))
          (childCharacter τ ξ) (frequencyRadius (T B) Z ξr)≤Z^Bcap) →
      ∀v : ℝ,
      outerAvg s hb cover G JB τ v M (diagAvgT s ha hb cover G JB Us τ χ₀ Q m v K T Z ξr W)≤
        (((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
              ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
                xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
                  C0 Ckernel A Csum Ct B)))*
          (1+‖v‖)^(2*J) := by
  obtain ⟨J,control,h00,hk⟩ := uniform_actual_exceptional_part.{u} N α Bcap a b ε δ Bnorm Lrad Cr
    εsum hα0 hα23 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum
  obtain ⟨Ckernel,hCk,hQ⟩ := hk ballProfile
  refine ⟨J,control,Ckernel,hCk,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,hA,hCsum,hZe⟩ := hQ Q hQ0 hQt hQ72
  obtain ⟨C0,hC0,hzero⟩ := seed_second_zero.{u} N ε hε
  obtain ⟨controlT,Ct,hCt,hZt⟩ := seed_tail.{u} Btl ξr saving hBtl hξr
  refine ⟨A,Csum,C0,Ct,controlT,hA,hCsum,hC0,hCt,?_⟩
  filter_upwards [hZe,hZt] with Z hZe hZt
  refine ⟨hZe.1,?_⟩
  intro ι instι s cover G JB Us τ χ₀ m hm hml hm2 K Lref T W M Y hK hLref0 hLref hKc hTB
    hWMY hcaps v
  have hpoint : ∀ B ξ, diagAvgT s ha hb cover G JB Us τ χ₀ Q m v K T Z ξr W B ξ ≤
      (1+‖v‖)^(2*J) *
        xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
          C0 Ckernel A Csum Ct B := by
    intro B ξ
    obtain ⟨hW0, hWc, hWic, _, hY1, hYc⟩ := hWMY B
    obtain ⟨hcard, hF, hP, hpool, hpoolT, hH, hYcap, hscale, hcond⟩ := hcaps B
    obtain ⟨hT, hrad, hTc⟩ := hTB B
    have hsq : ∀ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
        Squarefree w := Vset_squarefree _ _ _ Us
    have hne : ∀ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
        w ≠ 0 := fun w hw h => not_squarefree_zero (h ▸ hsq w hw)
    rw [diagAvgT, diagAvg_eq]
    have hKc0 : 0 ≤ 16*K*W B^4 := by positivity
    refine (diagR_le (restOf s hb cover G B (JB B)) ha
      (Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us)
      (childCharacter τ ξ) χ₀ Q m v (16*K*W B^4) (T B) Z ξr _ hKc0
      (fun w => C0*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)/(w.absNorm:ℝ))
      (fun w => (1+‖v‖)^(2*J)*(sourceVolume (restOf s hb cover G B (JB B))*W B*
              ((Ckernel*A*((1+2*Real.pi)^2)^(2*J)*(windowMoment J)^2)*
                savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
                refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
                (Csum*Z^εsum/(w.absNorm:ℝ)))))
      (fun _ => W B*(Ct*(profileCap (restOf s hb cover G B (JB B)))^2*
              controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)))
      ?_ ?_ ?_).trans ?_
    · intro w hw
      exact hzero (Rest (JB B)) a b (restOf s hb cover G B (JB B)) hcard ha w (hne w hw)
        (childCharacter τ ξ) v (Y B) hY1 hYcap
    · intro w hw
      have h := hZe.2 (Rest (JB B)) (restOf s hb cover G B (JB B))
        (ConcreteDiag.rest_enclosure _ _ _ (MixedFirstExceptionalWindow.live_enclosure _)) hcard hF hP hpool
        (childCharacter τ ξ) χ₀ m hm hml hm2 w (hsq w hw) (hne w hw)
        v K (W B) (T B) ξr _ hK hW0 hT hH hrad (hcond ξ) Lref hLref0 hLref
      have hV := sourceVolume_pos (restOf s hb cover G B (JB B))
      have hb2 := heightBase_pow_le J v
      have hrest : 0 ≤ savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
          refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
          (Csum*Z^εsum/(w.absNorm:ℝ)) := by
        have := savedBudget_nonneg (restOf s hb cover G B (JB B)) J control Q Z ε K (W B) hK hW0
        have := refLoss_nonneg (restOf s hb cover G B (JB B)) Lref α hLref0.le
        have := (zero_lt_one.trans hZe.1).le
        positivity
      have hwm : 0 ≤ Ckernel*A*(windowMoment J)^2 := by positivity
      rw [div_div, div_le_iff₀ (mul_pos hV hW0)] at h
      calc _ ≤ (Ckernel*A*heightBase v^(2*J)*(windowMoment J)^2)*
              savedBudget (restOf s hb cover G B (JB B)) J control Q Z ε K (W B)*
              refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
              (Csum*Z^εsum/(w.absNorm:ℝ))*
              (sourceVolume (restOf s hb cover G B (JB B))*W B) := h
        _ = ((Ckernel*A*(windowMoment J)^2)*(savedBudget (restOf s hb cover G B (JB B)) J control
              Q Z ε K (W B)*refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
              (Csum*Z^εsum/(w.absNorm:ℝ)))*
              (sourceVolume (restOf s hb cover G B (JB B))*W B))*heightBase v^(2*J) := by ring
        _ ≤ ((Ckernel*A*(windowMoment J)^2)*(savedBudget (restOf s hb cover G B (JB B)) J control
              Q Z ε K (W B)*refLoss (restOf s hb cover G B (JB B)) Lref α*Z^(2*Bnorm*δ)*
              (Csum*Z^εsum/(w.absNorm:ℝ)))*
              (sourceVolume (restOf s hb cover G B (JB B))*W B))*
              (((1+2*Real.pi)^2)^(2*J)*(1+‖v‖)^(2*J)) := by
            apply mul_le_mul_of_nonneg_left hb2
            have := hV.le; have := hW0.le; positivity
        _ = _ := by ring
    · intro w _
      exact hZt.2 (Rest (JB B)) a b (restOf s hb cover G B (JB B)) ha hb w (childCharacter τ ξ) v K
        (W B) (Y B) (T B) hK hW0 (zero_lt_one.trans_le hY1) hpoolT hYcap hYc hKc hWc hWic hTc hscale
    · unfold xiB
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro w _
      have hp1 : 1≤(1+‖v‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg v])
      have hzt : 0 ≤ W B*(Ct*(profileCap (restOf s hb cover G B (JB B)))^2*
          controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)) := by
        have := hW0.le
        have := (zero_lt_one.trans hZe.1).le
        have : 0 ≤ controlT.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
        positivity
      have hzz : 0 ≤ 16*K*W B^4*‖paperRadialFourier ballProfile 0‖*
          (C0*(profileCap (restOf s hb cover G B (JB B)))^2*(Y B)^(1+ε)/(w.absNorm:ℝ)) := by
        have := (zero_lt_one.trans_le hY1).le
        have := profileCap_nonneg (restOf s hb cover G B (JB B))
        positivity
      nlinarith
  have hsum : ∀ B, (∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
      diagAvgT s ha hb cover G JB Us τ χ₀ Q m v K T Z ξr W B ξ) ≤
      (Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
        ((1+‖v‖)^(2*J) * xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ
          εsum saving C0 Ckernel A Csum Ct B) := by
    intro B
    calc _ ≤ ∑ _χ : RayCharacter, ∑ _ξ : RayCharacter, (1+‖v‖)^(2*J) *
          xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
            C0 Ckernel A Csum Ct B :=
        Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ξ _ => hpoint B ξ
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hnn : ∀ B, 0 ≤ ∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
      diagAvgT s ha hb cover G JB Us τ χ₀ Q m v K T Z ξr W B ξ := by
    intro B
    apply Finset.sum_nonneg; intro χ _
    apply Finset.sum_nonneg; intro ξ _
    rw [diagAvgT, diagAvg_eq]; exact diagR_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _
  unfold outerAvg
  calc _ ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
              ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
                ((1+‖v‖)^(2*J) * xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α
                  Bnorm δ εsum saving C0 Ckernel A Csum Ct B))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum; intro B _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hM0 := (hWMY B).2.2.2.1
        have h2M : 0 ≤ (2:ℝ)^(Fintype.card (JB B)) * M B := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_right (Atot_le _ _ _ _) h2M) (hsum B) (hnn B)
          (mul_nonneg (AtotP_nonneg _ _) h2M)
    _ = _ := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl; intro B _
        ring

end
end QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
