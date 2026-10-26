/- Mixed source step: new in this submission; uses Collet's definitions by import
(the instance transports follow the proof of Collet's `actual_marked_allocation_main`,
as in Contract.lean).

The transfer contract without (S) (design §8, risk 1). For a squarefree seed `L`
nothing is frozen: the selected primes that divide `L` are transferred with the
others, and the residual of a selected assignment `u` carries the residual seed
`L / gcd(L, D_u)`. The output is a sum over residual seeds `L' ∣ L` of waist-form
energies of `child (s.restrict J)` with seed `L'`, with the same common ideal `C`,
the same restricted allocation and the same constant as with (S); the labels go
through the pushforward, so no divisor count of `L` is paid. -/
import Submissions.arvi_mixed_step.Residual.Waist
import Submissions.arvi_mixed_step.Transfer.SupplierBall

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u v

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open RayFourExpansion CanonicalQuadraticSieve Cycle61InitialMass
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- Ball transfer without (S), residual given by matched inputs. -/
theorem collet_main_selected_transfer_supplier_ball_match (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) {κ' : Type u} [Fintype κ'] [DecidableEq κ']
      (e : {i // i ∉ J} ≃ κ') (s₂ : RayCharacter → Input κ'),
      (∀ ξ, SlotMatch e (residualInput s J) (s₂ ξ)) →
    ∀ (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H H' : ℝ),
      0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ j ∈ J, 0 ≤ s.hi j) → Squarefree L →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
      (gaussEnergy Finset.univ
          (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            (gaussEnergy Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (s₂ ξ).pools)))
              (sourceGenerator_supported (finiteColumns (Fintype.piFinset (s₂ ξ).pools)))
              (fun I : supportedColumns (finiteColumns (Fintype.piFinset (s₂ ξ).pools)) =>
                CoupledFirst.coefficient (s₂ ξ) (markedSourceModifier A₁ A₂ Dc K F) R L' I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re := by
  obtain ⟨C, hC, hball⟩ := collet_main_selected_transfer_supplier_ball.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J κ' _ _ e s₂ hm A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hLsq hF hCol
  obtain ⟨seeds, hseeds, hb⟩ :=
    hball hcard s J A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hLsq hF hCol
  refine ⟨seeds, hseeds, hb.trans (le_of_eq
    (congrArg (fun x => C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε * x)
      (Finset.sum_congr rfl (fun ξ _ => Finset.sum_congr rfl (fun L' _ => congrArg Complex.re
        (energy_transport e (hm ξ) A₁ A₂ Dc K F R L'
          (fun I => (Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
            rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I) ballProfile H'))))))⟩

/-- **Transfer contract without (S)**, waist form: a sum over residual seeds. -/
theorem transfer_waist_supplier (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s → Squarefree L →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      (∀ j ∈ J, 0 ≤ s.hi j) →
    ∀ (τ : HeckeFamily.Character) (t T H H' : ℝ), 0 < H → 0 < H' →
      2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      NoCollision s C R L B J τ t →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H ≤
        K * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
              (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' := by
  obtain ⟨Cb, hCb, hball⟩ := collet_main_selected_transfer_supplier_ball_match.{u} ε hε N
  refine ⟨Cb, hCb, ?_⟩
  intro α _ _ hcard s C R L P hp hPA hLsq B J hJ hhi τ t T H H' hH hH' hrad hCol
  have hcard' : Fintype.card (liveIndices B.val) ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans hcard
  have hrad' : 2 * H * (∏ j ∈ liveBlock B J,
      (child s C R B τ t).hi j * (child s C R B τ t).P j) ^ 4 ≤ H' := by
    have h := prod_liveBlock B J hJ (fun j => s.hi j * s.P j)
    exact h ▸ hrad
  have hhi' : ∀ j ∈ liveBlock B J, 0 ≤ (child s C R B τ t).hi j :=
    fun j hj => hhi j.val ((mem_liveBlock B J j).mp hj)
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
  obtain ⟨seeds, hseeds, hb⟩ := hball hcard' (child s C R B τ t) (liveBlock B J)
    (childRestrictEquiv s C B J hJ)
    (fun ξ => child (s.restrict J) C R (allocRestrict s C B J hJ) (childCharacter τ ξ) t)
    (fun ξ => childRestrict_match s C R B J hJ τ (childCharacter τ ξ) t t)
    (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val) (R * C) L
    (poolCorr P C) τ t T H H' hH hH' hrad' hhi' hLsq hF' hCol'
  refine ⟨seeds, hseeds, ?_⟩
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
  have hPJ : ∏ j ∈ liveBlock B J, (child s C R B τ t).P j = ∏ j ∈ J, s.P j :=
    prod_liveBlock B J hJ s.P
  have hR : ∀ (ξ : RayCharacter) (L' : Ideal O),
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
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L' I *
            ((Real.sqrt (T / ∏ j ∈ liveBlock B J, (child s C R B τ t).P j) : ℂ)⁻¹ *
              rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re =
      correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
        (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' := by
    intro ξ L'
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
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L' I *
        ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
          rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H'
  have hHM : ∏ j ∈ liveBlock B J, (child s C R B τ t).hi j * (child s C R B τ t).M j ^ 2 =
      ∏ j ∈ J, s.hi j * s.M j ^ 2 :=
    prod_liveBlock B J hJ (fun j => s.hi j * s.M j ^ 2)
  rw [hL]
  refine hb.trans (le_of_eq ?_)
  rw [hHM]
  exact congrArg (fun x => Cb * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε * x)
    (Finset.sum_congr rfl (fun ξ _ => Finset.sum_congr rfl (fun L' _ => hR ξ L')))

/-- **Transfer contract without (S) for a first-layer column**: design radius,
shifted columns `rayShift c ξ`, and `H' ≤ Z^A`. -/
theorem transfer_waist_supplier_column (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s → Squarefree L →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ {ι₀ : Type v} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (t T H H' Z A : ℝ), 0 < H → 2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 ≤ H' →
      1 ≤ Z → 0 ≤ A → H' ≤ Z ^ A →
      NoCollision s C R L B J (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t T H ≤
        K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
              (allocRestrict s C B J hJ)
              (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
              t (T / ∏ j ∈ J, s.P j) H' := by
  obtain ⟨Kw, hKw, hw⟩ := transfer_waist_supplier.{u} ε hε N
  refine ⟨Kw * 2 ^ N, by positivity, ?_⟩
  intro α _ _ hcard s C R L P hp hPA hLsq B J hJ hhi ι₀ _ _ reflected s₀ modifier R₀ seed K₀ Z₀
    ξ₀ hK key c t T H H' Z A hH hrad hZ hA hHZ hNC
  have hPpos : 0 < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hH' : 0 < H' := lt_of_lt_of_le (by positivity) hrad
  have hrad' : 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' := by
    calc
      _ ≤ 2 * H * (16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4) :=
        mul_le_mul_of_nonneg_left (window_le s J hhi) (by positivity)
      _ = 2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 := by ring
      _ ≤ H' := hrad
  obtain ⟨seeds, hseeds, h⟩ := hw hcard s C R L P hp hPA hLsq B J hJ (fun j hj => (hhi j hj).1)
    (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t T H H' hH hH' hrad' hNC
  refine ⟨seeds, hseeds, h.trans ?_⟩
  have hE : ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
        correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
          (allocRestrict s C B J hJ)
          (childCharacter (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ξ) t
          (T / ∏ j ∈ J, s.P j) H' =
      ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
        correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
          (allocRestrict s C B J hJ)
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
          t (T / ∏ j ∈ J, s.P j) H' :=
    Finset.sum_congr rfl (fun ξ _ => Finset.sum_congr rfl (fun L' _ =>
      rayShift_energy reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c ξ (s.restrict J) 1 1 1 1 C R
        L' (fun _ => 1) P (allocRestrict s C B J hJ) t (T / ∏ j ∈ J, s.P j) H'))
  have hsum : 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
        correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
          (allocRestrict s C B J hJ)
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
          t (T / ∏ j ∈ J, s.P j) H' :=
    Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
      corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH'))
  have hJN : J.card ≤ N := (Finset.card_le_univ J).trans hcard
  have hX : 0 ≤ (max 1 H') ^ ε := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) ε
  rw [hE]
  calc
    _ ≤ Kw * (2 ^ N * ∏ j ∈ J, s.M j ^ 2) * (max 1 H') ^ ε *
        ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
          correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (T / ∏ j ∈ J, s.P j) H' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (slot_factor_le s J N hJN hhi) hKw.le) hX) hsum
    _ ≤ Kw * (2 ^ N * ∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
        ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
          correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (T / ∏ j ∈ J, s.P j) H' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (max_rpow_le H' Z A ε hZ hA hε.le hHZ)
        (mul_nonneg hKw.le (mul_nonneg (by positivity)
          (Finset.prod_nonneg (fun j _ => sq_nonneg _))))) hsum
    _ = _ := by ring

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.transfer_waist_supplier
#print axioms QRH.MixedStep.Residual.transfer_waist_supplier_column
