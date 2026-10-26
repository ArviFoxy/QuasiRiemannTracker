/- Mixed source step, L3 interface: new in this submission; uses Collet's definitions
by import (the instance transports follow the proof of Collet's
`actual_marked_allocation_main`, as in Contract.lean).

The transfer contract with (Col) discharged by splitting the child tuples into
the no-collision part (selected product coprime to the ordinary pair) and the
collision part:

  correctedChildGaussEnergy s … C R L 1 P B τ t T H
    ≤ K · ∏_{j∈J} hi_j M_j² · (max 1 H')^ε ·
        Σ_ξ correctedChildGaussEnergy (s.restrict J) … (allocRestrict B hJ) (childCharacter τ ξ) t (T/∏_J P) H'
      + 2 · collisionEnergy s C R L P B J τ t T H,

with no collision hypothesis. `collisionEnergy` is the ball energy of the child
source restricted to the tuples with a collision (some selected prime divides the
ordinary pair); bounding it is the job of L3 (Collision/). -/
import Submissions.arvi_mixed_step.Residual.Waist
import Submissions.arvi_mixed_step.Transfer.NoCollisionBall

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open RayFourExpansion
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O

/-- The collision part of the child energy: tuples whose selected product (the
block `J` read in the live slots) shares a prime with the ordinary pair. -/
def collisionEnergy {α : Type*} [Fintype α] [DecidableEq α] (s : Input α) (C R L : Ideal O)
    (P : Finset (Ideal O)) (B : actualAllocations s.pools C) (J : Finset α)
    (τ : HeckeFamily.Character) (t T H : ℝ) : ℝ :=
  (gaussEnergy Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
    (sourceGenerator_supported (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
    (fun I : supportedColumns (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)) =>
      finiteColumnCoefficient (Fintype.piFinset (child s C R B τ t).pools)
        (colPart (liveBlock B J) (CoupledFirst.tupleCoefficient (child s C R B τ t)
          (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
            (1 * markedProduct B.val) (poolCorr P C)) (R * C) L)) I *
        ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re

/-- **Transfer contract, (Col) discharged by the collision split.** -/
theorem transfer_waist_split (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      SeedFree s J L → (∀ j ∈ J, 0 ≤ s.hi j) →
    ∀ (τ : HeckeFamily.Character) (t T H H' : ℝ), 0 < H → 0 < H' →
      2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H ≤
        K * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
            (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' +
        2 * collisionEnergy s C R L P B J τ t T H := by
  obtain ⟨Cb, hCb, hball⟩ := collet_main_selected_transfer_ball_nocol.{u} ε hε N
  refine ⟨2 * Cb, by positivity, ?_⟩
  intro α _ _ hcard s C R L P hp hPA B J hJ hSF hhi τ t T H H' hH hH' hrad
  have hcard' : Fintype.card (liveIndices B.val) ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans hcard
  have hrad' : 2 * H * (∏ j ∈ liveBlock B J,
      (child s C R B τ t).hi j * (child s C R B τ t).P j) ^ 4 ≤ H' := by
    have h := prod_liveBlock B J hJ (fun j => s.hi j * s.P j)
    exact h ▸ hrad
  have hhi' : ∀ j ∈ liveBlock B J, 0 ≤ (child s C R B τ t).hi j :=
    fun j hj => hhi j.val ((mem_liveBlock B J j).mp hj)
  have hS' : ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
      CoupledFirst.tupleCoefficient (child s C R B τ t)
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L v ≠ 0 →
        IsCoprime L (∏ j ∈ liveBlock B J, v (Sum.inl j)) :=
    fun v hv _ => seed_free_of_slots (child s C R B τ t) (liveBlock B J) L
      (fun j hj p hpj => hSF j.val ((mem_liveBlock B J j).mp hj) p hpj) v hv
  have hF' : ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
      poolCorr P C (1 * finiteTupleProduct v) =
        poolCorr P C (1 * finiteTupleProduct (restPart (liveBlock B J) v)) := by
    intro v hv
    have hv' := (mem_pools_iff _ v).mp (Fintype.mem_piFinset.mp hv)
    have hsel : selPart (liveBlock B J) v ∈ selBox (child s C R B τ t) (liveBlock B J) :=
      Fintype.mem_piFinset.mpr (fun j => hv'.1 j.val)
    have hprod : finiteTupleProduct v = selProduct (liveBlock B J) (selPart (liveBlock B J) v) *
        finiteTupleProduct (restPart (liveBlock B J) v) := by
      conv_lhs => rw [← join_parts (liveBlock B J) v]
      exact finiteTupleProduct_join _ _ _
    rw [hprod]
    exact poolCorr_invariant (child s C R B τ t) P hp
      (fun Q hQ i I hI => hPA Q hQ i.val I hI) C (liveBlock B J) _ hsel _
  -- the no-collision part, transferred and transported to the child of the restriction
  have hb := hball hcard' (child s C R B τ t) (liveBlock B J)
    (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val) (R * C) L
    (poolCorr P C) τ t T H H' hH hH' hrad' hhi' hS' hF'
  have hPJ : ∏ j ∈ liveBlock B J, (child s C R B τ t).P j = ∏ j ∈ J, s.P j :=
    prod_liveBlock B J hJ s.P
  have hR : ∀ ξ : RayCharacter,
      (gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset
          (residualInput (child s C R B τ t) (liveBlock B J)).pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset
          (residualInput (child s C R B τ t) (liveBlock B J)).pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset
            (residualInput (child s C R B τ t) (liveBlock B J)).pools)) =>
          CoupledFirst.coefficient (residualInput (child s C R B τ t) (liveBlock B J))
            (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
            ((Real.sqrt (T / ∏ j ∈ liveBlock B J, (child s C R B τ t).P j) : ℂ)⁻¹ *
              rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re =
      correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' := by
    intro ξ
    rw [congrArg Complex.re (energy_transport (childRestrictEquiv s C B J hJ)
      (childRestrict_match s C R B J hJ τ (childCharacter τ ξ) t t)
      (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val)
      (poolCorr P C) (R * C) L
      (fun I => (Real.sqrt (T / ∏ j ∈ liveBlock B J, (child s C R B τ t).P j) : ℂ)⁻¹ *
        rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I) ballProfile H'), hPJ]
    unfold correctedChildGaussEnergy
    dsimp only
    rw [allocRestrict_marked s C B J hJ]
    generalize child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t = s''
    apply congrArg Complex.re
    exact source_gauss_energy_pool_decEq
      (ι := liveIndices (allocRestrict s C B J hJ).val) _ _ s''.pools
      (fun I => CoupledFirst.coefficient s''
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
        ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
          rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H'
  have hHM : ∏ j ∈ liveBlock B J, (child s C R B τ t).hi j * (child s C R B τ t).M j ^ 2 =
      ∏ j ∈ J, s.hi j * s.M j ^ 2 :=
    prod_liveBlock B J hJ (fun j => s.hi j * s.M j ^ 2)
  rw [hHM, Finset.sum_congr rfl (fun ξ _ => hR ξ)] at hb
  -- the child energy splits into the two parts
  have hL : correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H =
      (gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)) =>
          CoupledFirst.coefficient (child s C R B τ t)
            (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re := by
    unfold correctedChildGaussEnergy
    dsimp only
    generalize child s C R B τ t = s'
    apply congrArg Complex.re
    exact source_gauss_energy_pool_decEq (ι := liveIndices B.val) _ _ s'.pools
      (fun I => CoupledFirst.coefficient s'
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
        ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H
  have hsplit : (gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)) =>
          CoupledFirst.coefficient (child s C R B τ t)
            (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H) =
      gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset (child s C R B τ t).pools)) =>
          finiteColumnCoefficient (Fintype.piFinset (child s C R B τ t).pools)
              (noColPart (liveBlock B J) (CoupledFirst.tupleCoefficient (child s C R B τ t)
                (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
                  (1 * markedProduct B.val) (poolCorr P C)) (R * C) L)) I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I) +
            finiteColumnCoefficient (Fintype.piFinset (child s C R B τ t).pools)
              (colPart (liveBlock B J) (CoupledFirst.tupleCoefficient (child s C R B τ t)
                (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
                  (1 * markedProduct B.val) (poolCorr P C)) (R * C) L)) I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H := by
    congr 1
    funext I
    rw [coefficient_eq_box, column_split _ (liveBlock B J)]
    ring
  rw [hL, hsplit]
  refine (ball_energy_add_le _ _ _ _ _ H hH).trans ?_
  have hb2 := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2)
  unfold collisionEnergy
  linarith

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.transfer_waist_split
