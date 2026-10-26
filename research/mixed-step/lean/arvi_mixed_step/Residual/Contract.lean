/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The decidable-instance transports `hL` and `hR` follow the proof of Collet's
`actual_marked_allocation_main` (Record1252270103Source/High/GlobalPhysicalAllocationMain.lean:
`generalize` the child, then `source_gauss_energy_pool_decEq`). The rest is new in
this submission.

Mixed source step: the transfer in the waist form consumed by L4/L5
(`TransferContract`, design §4).

For an actual allocation `B` and a block `J` of its live slots,

  correctedChildGaussEnergy s 1 1 1 1 C R L 1 P B τ t T H
    ≤ K · ∏_{j∈J} hi_j M_j² · (max 1 H')^ε ·
        Σ_ξ correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L 1 P
              (allocRestrict B hJ) (childCharacter τ ξ) t (T/∏_J P) H',

with `K` depending only on `(ε, N)`, under `PoolAvoids P s` (pool primes avoid
the slots), `SeedFree s J L` (no selected prime divides the seed), no collision
in the child, `0 ≤ hi` on `J`, and the radius condition
`2·H·(∏_J hi_j P_j)⁴ ≤ H'`. The residual carries `T/∏_J P` and the only
slot factor is the bounded `∏ hi·M²`: no `∏ P` appears twice. -/
import Submissions.arvi_mixed_step.Residual.BallMatch
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalAllocationMain

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

/-- Pool primes avoid every marked slot (Collet's `hmarked`). -/
def PoolAvoids {α : Type*} [Fintype α] (P : Finset (Ideal O)) (s : Input α) : Prop :=
  ∀ Q ∈ P, ∀ i, ∀ I ∈ s.pools (Sum.inl i), ¬Q ∣ I

/-- (S): no prime of a selected slot divides the seed. -/
def SeedFree {α : Type*} [Fintype α] (s : Input α) (J : Finset α) (L : Ideal O) : Prop :=
  ∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L

/-- The pool correction of `correctedChildGaussEnergy` at `F = 1`. -/
def poolCorr (P : Finset (Ideal O)) (C : Ideal O) : Ideal O → ℂ :=
  fun J => (((P.card : ℝ) / ((P.card : ℝ) - (idealDividingPool P J).card)) : ℂ) *
    (fun _ : Ideal O => (1 : ℂ)) ((1 * C) * J)

theorem modifier_ne_one {κ : Type*} [Fintype κ] (A₁ A₂ D K : Ideal O) (F : Ideal O → ℂ)
    (v : Tuple κ) (h : markedSourceModifier A₁ A₂ D K F v ≠ 0) :
    markedSourceModifier A₁ A₂ D K (fun _ => 1) v ≠ 0 := by
  unfold markedSourceModifier sourceModifier coupledFactor at h ⊢
  intro hz
  apply h
  simp only [mul_one] at hz
  rcases mul_eq_zero.mp hz with h1 | h2
  · rw [h1, zero_mul]
  · rcases mul_eq_zero.mp h2 with h3 | h4
    · rw [h3, zero_mul, mul_zero]
    · rw [h4, zero_mul, mul_zero, mul_zero]

/-- The pool correction is invariant under multiplying by a product of slot
primes, when the pool avoids the slots. -/
theorem poolCorr_invariant {α : Type*} [Fintype α] [DecidableEq α] (s : Input α) (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hPA : PoolAvoids P s) (C : Ideal O) (J : Finset α)
    (u : J → Ideal O) (hu : u ∈ selBox s J) (n : Ideal O) :
    poolCorr P C (1 * (selProduct J u * n)) = poolCorr P C (1 * n) := by
  have hdiv : idealDividingPool P (selProduct J u * n) = idealDividingPool P n := by
    unfold idealDividingPool
    apply Finset.filter_congr
    intro Q hQ
    constructor
    · intro hd
      rcases (hp Q hQ).dvd_or_dvd hd with h1 | h2
      · exfalso
        obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff (hp Q hQ) u).mp h1
        exact hPA Q hQ j.val (u j) (Fintype.mem_piFinset.mp hu j) hj
      · exact h2
    · intro hd
      exact hd.trans (dvd_mul_left _ _)
  unfold poolCorr
  simp only [one_mul, hdiv]

/-- **Transfer contract in the waist form** (seed-free selected block, no collision). -/
theorem transfer_waist (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      SeedFree s J L → (∀ j ∈ J, 0 ≤ s.hi j) →
    ∀ (τ : HeckeFamily.Character) (t T H H' : ℝ), 0 < H → 0 < H' →
      2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
        CoupledFirst.tupleCoefficient (child s C R B τ t)
          (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
            (1 * markedProduct B.val) (fun _ => 1)) (R * C) L v ≠ 0 →
          IsCoprime (∏ j ∈ liveBlock B J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H ≤
        K * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
            (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' := by
  obtain ⟨Cb, hCb, hball⟩ := collet_main_selected_transfer_ball_match.{u} ε hε N
  refine ⟨Cb, hCb, ?_⟩
  intro α _ _ hcard s C R L P hp hPA B J hJ hSF hhi τ t T H H' hH hH' hrad hCol
  have hcard' : Fintype.card (liveIndices B.val) ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans hcard
  -- the child and its selected block
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
  have hCol' : ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
      CoupledFirst.tupleCoefficient (child s C R B τ t)
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L v ≠ 0 →
        IsCoprime (∏ j ∈ liveBlock B J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) := by
    intro v hv hne
    apply hCol v hv
    unfold CoupledFirst.tupleCoefficient at hne ⊢
    exact mul_ne_zero (modifier_ne_one _ _ _ _ _ v (left_ne_zero_of_mul hne))
      (right_ne_zero_of_mul hne)
  have hb := hball hcard' (child s C R B τ t) (liveBlock B J) (childRestrictEquiv s C B J hJ)
    (fun ξ => child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t)
    (fun ξ => childRestrict_match s C R B J hJ τ (childCharacter τ ξ) t t)
    (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val) (R * C) L
    (poolCorr P C) τ t T H H' hH hH' hrad' hhi' hS' hF' hCol'
  -- left side: Collet's decidable-equality instance
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
  -- right side: the child of the restricted parent, with Collet's instance
  have hPJ : ∏ j ∈ liveBlock B J, (child s C R B τ t).P j = ∏ j ∈ J, s.P j :=
    prod_liveBlock B J hJ s.P
  have hR : ∀ ξ : RayCharacter,
      (gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset
          (child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t).pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset
          (child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t).pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset
            (child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t).pools)) =>
          CoupledFirst.coefficient
            (child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t)
            (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
            ((Real.sqrt (T / ∏ j ∈ liveBlock B J, (child s C R B τ t).P j) : ℂ)⁻¹ *
              rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re =
      correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' := by
    intro ξ
    rw [hPJ]
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
  rw [hL]
  refine hb.trans (le_of_eq ?_)
  rw [hHM]
  exact congrArg (fun x => Cb * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε * x)
    (Finset.sum_congr rfl (fun ξ _ => hR ξ))

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.transfer_waist
