/- Mixed source step, N3 (pieces): new in this submission. Uses Collet's, the baseline's and the
transfer's (`Residual/`, `Transfer/`) definitions by import. The decidable-instance transports in
`restrict_empty_energy` follow the proof of the transfer's `transfer_waist` (Residual/Contract.lean),
itself after Collet's `actual_marked_allocation_main`
(Record1252270103Source/High/GlobalPhysicalAllocationMain.lean).

Pieces of the first MAIN sum `Σ_l amplitude_l·E_l` (the output of Collet's `eventual_selected_main`),
`L45_DESIGN.md` §2.1–2.2:

* `pieceKey alloc trans l = (live slots of l, transferable slots of l)`. The sum splits by key
  (`sum_pieces`) into at most `4^N` pieces (`card_pieces_le`). All labels of a piece have the same
  live slots (frozen set `F_l = {i | alloc l (inl i) ≠ 1}`) and the same transferable slots, so one
  block `J ⊆ trans` serves them all. With `trans = live` this is the design's split by frozen class
  (at most `2^N` classes); with `trans = live ∩ allowedSlots s seed` it is the refinement needed by
  the seed condition (S) of `transfer_waist`.
* `residual_frozen_width`: the frozen width of the restricted allocation, read on the residual
  slots, is the original frozen width. This is the form of the forked LOW spine's hypothesis
  `φ ≤ Σ_i w i - Σ_{i ∈ liveIndices B₁} w i` (HANDOFF.md, F3).
* `restrict_logb_volume`: `logb Z (volume (s.restrict J)) = logb Z (volume s) − Σ_J w` when
  `s.P = Z^w`; so the δ-shift `hshift : a_v − a ≤ A − A_v + κ` reads `δ − Σ_J w ≤ κ`.
* `residual_width`: the residual width is `Σ w − Σ_J w`.
* `firstMainRadius_restrict`, `piece_radius`: the transfer radius condition
  `2·16^{|J|}·H·(∏_J P)⁴ ≤ H'` for `H = firstMainRadius(V, 3a)` and
  `H' = firstMainRadius(V/∏_J P, 3(a+δ))`, once `Σ_J w ≤ δ − mesh` and `log_Z(2·16^N) ≤ 6·mesh`.
* `restrict_empty_energy`: the corrected child energy of `s` equals that of `s.restrict ∅`
  (the pieces at node 0, which transfer nothing); `rayShift_one`. -/
import Submissions.arvi_mixed_step.Downstream.Grid
import Submissions.arvi_mixed_step.Residual.Waist
import Submissions.arvi_mixed_step.Transfer.Select

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale
open RayFourExpansion CanonicalQuadraticSieve Cycle61InitialMass Cycle61Moment ActualEisensteinCubic
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer QRH.MixedStep.Residual
local notation "O" => ActualEisensteinCubic.O

/-! ### Keys and the split of the sum -/

section Keys
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The piece key of a label: its live slots and its transferable slots. -/
def pieceKey {Label : Type*} {s : Input α} {C : Label → Ideal O}
    (alloc : ∀ l, actualAllocations s.pools (C l)) (trans : Label → Finset α) (l : Label) :
    Finset α × Finset α :=
  (liveIndices (alloc l).val, trans l)

/-- **The split by pieces.** -/
theorem sum_pieces {Label K : Type*} [Fintype Label] [DecidableEq K] (key : Label → K)
    (f : Label → ℝ) :
    ∑ l, f l = ∑ k ∈ Finset.univ.image key, ∑ l : {l // key l = k}, f l.val := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image key)
    (g := key) (fun l _ => Finset.mem_image_of_mem key (Finset.mem_univ l)) f]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_subtype _ (fun l => by simp) f

/-- At most `4^N` pieces. -/
theorem card_pieces_le {Label : Type*} [Fintype Label] (key : Label → Finset α × Finset α) :
    (Finset.univ.image key).card ≤ 4 ^ Fintype.card α := by
  calc (Finset.univ.image key).card ≤ Fintype.card (Finset α × Finset α) := Finset.card_le_univ _
    _ = 4 ^ Fintype.card α := by
      rw [Fintype.card_prod, Fintype.card_finset, ← mul_pow]
      norm_num

/-- The live slots of a label are the complement of its frozen set. -/
theorem mem_liveIndices {s : Input α} {C : Ideal O} (B : actualAllocations s.pools C) (i : α) :
    i ∈ liveIndices B.val ↔ B.val (Sum.inl i) = 1 := by
  simp [liveIndices]

end Keys

/-! ### The residual: frozen width, volume, width -/

section Residual
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The residual frozen width** (form of the F3 hypothesis): the residual slots minus the live
slots of the restricted allocation are exactly the original frozen slots. -/
theorem residual_frozen_width (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (w : α → ℝ) :
    (∑ i : {i // i ∉ J}, w i.val) - ∑ i ∈ liveIndices (allocRestrict s C B J hJ).val, w i.val =
      ∑ i ∈ Finset.univ.filter (fun i => B.val (Sum.inl i) ≠ 1), w i := by
  have hlive : liveIndices (allocRestrict s C B J hJ).val =
      Finset.univ.filter (fun i : {i // i ∉ J} => B.val (Sum.inl i.val) = 1) := by
    ext i
    simp [liveIndices, allocRestrict_val, restPart]
  rw [hlive, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : {i // i ∉ J} => B.val (Sum.inl i.val) = 1), add_sub_cancel_left]
  refine Finset.sum_bij' (fun i _ => i.val)
    (fun i hi => ⟨i, fun hiJ => (Finset.mem_filter.mp hi).2 ((mem_liveIndices B i).mp (hJ hiJ))⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _
    rfl
  · intro i _
    rfl
  · intro i _
    rfl

/-- The block's product of scales, when `s.P = Z^w`. -/
theorem prod_P_eq (s : Input α) (w : α → ℝ) {Z : ℝ} (hZ : 0 < Z) (hP : ∀ i, s.P i = Z ^ w i)
    (J : Finset α) : ∏ j ∈ J, s.P j = Z ^ ∑ j ∈ J, w j := by
  rw [Real.rpow_sum_of_pos hZ]
  exact Finset.prod_congr rfl (fun j _ => hP j)

/-- **The volume drop**: `logb Z (volume (s.restrict J)) = logb Z (volume s) − Σ_J w`. -/
theorem restrict_logb_volume (s : Input α) (w : α → ℝ) {Z : ℝ} (hZ : 1 < Z)
    (hP : ∀ i, s.P i = Z ^ w i) (J : Finset α) :
    Real.logb Z (volume (s.restrict J)) = Real.logb Z (volume s) - ∑ j ∈ J, w j := by
  have hZ0 : 0 < Z := by linarith
  rw [volume_restrict, prod_P_eq s w hZ0 hP J,
    Real.logb_div (volume_pos s).ne' (Real.rpow_pos_of_pos hZ0 _).ne',
    Real.logb_rpow hZ0 hZ.ne']

/-- The residual width. -/
theorem residual_width (J : Finset α) (w : α → ℝ) :
    ∑ i : {i // i ∉ J}, w i.val = ∑ i, w i - ∑ j ∈ J, w j := by
  have h1 : ∑ i ∈ Jᶜ, w i = ∑ i : {i // i ∉ J}, w i.val :=
    Finset.sum_subtype Jᶜ (fun i => by simp) w
  have h2 := Finset.sum_add_sum_compl J w
  linarith

end Residual

/-! ### The radius of the residual -/

section Radius
variable {α : Type*}

theorem firstNominalScale_div (I J E : Ideal O) (K X W : ℝ) :
    firstNominalScale I J E K (X / W) = firstNominalScale I J E K X / W ^ 2 := by
  unfold firstNominalScale
  ring

theorem nominalLog_div (I J E : Ideal O) (K X Z W : ℝ) (hZ : 1 < Z) (hW : 1 ≤ W) :
    nominalLog I J E K X Z ≤ nominalLog I J E K (X / W) Z + 2 * Real.logb Z W := by
  unfold nominalLog
  rw [firstNominalScale_div]
  have hW0 : W ≠ 0 := by linarith
  have hlog : 0 ≤ Real.logb Z W := Real.logb_nonneg hZ hW
  by_cases hx : firstNominalScale I J E K X = 0
  · rw [hx, zero_div, Real.logb_zero]
    linarith
  · rw [Real.logb_div hx (pow_ne_zero 2 hW0), Real.logb_pow]
    push_cast
    linarith

/-- **The residual radius**: dividing the volume by `W ≥ 1` and adding `δ` to the amplitude
multiplies the MAIN radius by at least `Z^{6δ}/W²`. -/
theorem firstMainRadius_restrict (reflected : Bool) (K V Z ξ a δ reserve W : ℝ)
    (l : FirstSourceLabel) (hZ : 1 < Z) (hW : 1 ≤ W) :
    firstMainRadius reflected K V Z ξ (3 * a) reserve l * Z ^ (6 * δ) ≤
      firstMainRadius reflected K (V / W) Z ξ (3 * (a + δ)) reserve l * W ^ 2 := by
  have hZ0 : 0 < Z := by linarith
  have hW2 : W ^ 2 = Z ^ (Real.logb Z W * 2) := by
    rw [Real.rpow_mul hZ0.le, Real.rpow_logb hZ0 hZ.ne' (by linarith)]
    norm_cast
  unfold firstMainRadius mainCommonRadius
  rw [hW2, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have h := nominalLog_div l.1.1 l.1.2
    (Ideal.span {primeSubsetGenerator (fun p : CenteredMomentCanonicalFirst.CommonIndex l.1.1 l.1.2 =>
      p.val) l.2.val}) K V Z W hZ hW
  linarith

/-- **The transfer radius condition of a piece** (`transfer_waist_design`'s
`2·16^|J|·H·(∏_J P)⁴ ≤ H'`), from the window `Σ_J w ≤ δ − mesh` and `log_Z(2·16^N) ≤ 6·mesh`. -/
theorem piece_radius (reflected : Bool) (K V Z ξ a δ reserve mesh : ℝ) (l : FirstSourceLabel)
    (hZ : 1 < Z) (N : ℕ) (J : Finset α) (hJ : J.card ≤ N) (w P : α → ℝ)
    (hP : ∀ j, P j = Z ^ w j) (hw : ∀ j, 0 ≤ w j)
    (hmesh : Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh) (hact : ∑ j ∈ J, w j ≤ δ - mesh) :
    2 * 16 ^ J.card * firstMainRadius reflected K V Z ξ (3 * a) reserve l * (∏ j ∈ J, P j) ^ 4 ≤
      firstMainRadius reflected K (V / ∏ j ∈ J, P j) Z ξ (3 * (a + δ)) reserve l := by
  have hZ0 : 0 < Z := by linarith
  have hW : ∏ j ∈ J, P j = Z ^ (∑ j ∈ J, w j) := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_congr rfl (fun j _ => hP j)
  have hW1 : 1 ≤ ∏ j ∈ J, P j := by
    rw [hW]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun j _ => hw j))
  have hH := firstMainRadius_restrict reflected K V Z ξ a δ reserve (∏ j ∈ J, P j) l hZ hW1
  have hHpos := first_main_radius_pos reflected K V Z ξ (3 * a) reserve hZ0 l
  have h16 : (2 : ℝ) * 16 ^ J.card ≤ Z ^ (6 * mesh) := by
    calc (2 : ℝ) * 16 ^ J.card ≤ 2 * 16 ^ N := by
          gcongr
          norm_num
      _ = Z ^ (Real.logb Z (2 * 16 ^ N)) := (Real.rpow_logb hZ0 hZ.ne' (by positivity)).symm
      _ ≤ Z ^ (6 * mesh) := Real.rpow_le_rpow_of_exponent_le hZ.le hmesh
  have hW6 : (∏ j ∈ J, P j) ^ 6 ≤ Z ^ (6 * (δ - mesh)) := by
    rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    push_cast
    linarith
  have hW2pos : 0 < (∏ j ∈ J, P j) ^ 2 := by positivity
  have key : 2 * 16 ^ J.card * firstMainRadius reflected K V Z ξ (3 * a) reserve l *
      (∏ j ∈ J, P j) ^ 4 * (∏ j ∈ J, P j) ^ 2 ≤
      firstMainRadius reflected K (V / ∏ j ∈ J, P j) Z ξ (3 * (a + δ)) reserve l *
        (∏ j ∈ J, P j) ^ 2 := by
    calc 2 * 16 ^ J.card * firstMainRadius reflected K V Z ξ (3 * a) reserve l *
          (∏ j ∈ J, P j) ^ 4 * (∏ j ∈ J, P j) ^ 2 =
          firstMainRadius reflected K V Z ξ (3 * a) reserve l *
            ((2 * 16 ^ J.card) * (∏ j ∈ J, P j) ^ 6) := by ring
      _ ≤ firstMainRadius reflected K V Z ξ (3 * a) reserve l *
            (Z ^ (6 * mesh) * Z ^ (6 * (δ - mesh))) := by
          gcongr
      _ = firstMainRadius reflected K V Z ξ (3 * a) reserve l * Z ^ (6 * δ) := by
          rw [← Real.rpow_add hZ0]
          ring_nf
      _ ≤ _ := hH
  exact le_of_mul_le_mul_right key hW2pos

end Radius

/-! ### Node 0: the empty block -/

section Empty
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The live slots of `B` and of `B` restricted off the empty block. -/
def emptyEquiv (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    liveIndices B.val ≃ liveIndices (allocRestrict s C B ∅ (Finset.empty_subset _)).val where
  toFun i := ⟨⟨i.val, Finset.notMem_empty _⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp i.property).2⟩⟩
  invFun i := ⟨i.val.val,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp i.property).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem empty_match (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : HeckeFamily.Character) (t : ℝ) :
    SlotMatch (emptyEquiv s C B) (child s C R B τ t)
      (child (s.restrict ∅) C R (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t) where
  slots _ := rfl
  ν _ := rfl
  W _ := rfl
  P _ := rfl
  plain₁ := rfl
  plain₂ := rfl
  W₁ := rfl
  W₂ := rfl
  X₁ := rfl
  X₂ := rfl
  Y₁ := rfl
  Y₂ := rfl

/-- **Node 0**: the corrected child energy is unchanged by restricting off the empty block. -/
theorem restrict_empty_energy (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t T H : ℝ) :
    correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H =
      correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t T H := by
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
  have hR : (gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset
          (child (s.restrict ∅) C R (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t).pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset
          (child (s.restrict ∅) C R (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t).pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset
            (child (s.restrict ∅) C R (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t).pools)) =>
          CoupledFirst.coefficient
            (child (s.restrict ∅) C R (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t)
            (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
              (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re =
      correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t T H := by
    unfold correctedChildGaussEnergy
    dsimp only
    rw [allocRestrict_marked s C B ∅ (Finset.empty_subset _)]
    generalize child (s.restrict ∅) C R (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t = s''
    apply congrArg Complex.re
    exact source_gauss_energy_pool_decEq
      (ι := liveIndices (allocRestrict s C B ∅ (Finset.empty_subset _)).val) _ _ s''.pools
      (fun I => CoupledFirst.coefficient s''
        (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
          (1 * markedProduct B.val) (poolCorr P C)) (R * C) L I *
        ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H
  rw [hL, ← hR]
  exact congrArg Complex.re (energy_transport (emptyEquiv s C B) (empty_match s C R B τ t)
    (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val) (poolCorr P C)
    (R * C) L (fun I => (Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I) ballProfile H)

/-- The trivial ray shift. -/
theorem rayShift_one {Label : Type*} {src : Label → FirstBlockSource} (reflected : Bool)
    (c : FirstColumnIndex src) : rayShift reflected c 1 = c := by
  cases reflected <;> simp [rayShift]

end Empty

/-! ### The node facts of a label (consumed by the ledger, F3 and F4)

All constants are parameters: the grid (`G.g`, `G.κ`, `G.d`), the cell width `width`, the frozen
margin `ε` and the `mesh`. The F4 point bound `hwidthlo : (b − θnode) − θ_fb ≤ Σ_res` follows from
`piece_width` once `width + κ ≤ θ_fb`; the top price needs `κ ≤ 6e` (`NodeGrid.top_slack`); the
frozen price needs `width + g + κ ≤ ε ≤ 6e`. -/

section NodeFacts
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The residual width lies in the node cell** `[(b − θ) − (width + κ), b − θ]`. -/
theorem piece_width (G : NodeGrid) (w : α → ℝ) {mesh : ℝ} (T : Finset α) (hm : 0 ≤ mesh)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh) (hg : 2 * mesh ≤ G.g) (hκ : 2 * mesh ≤ G.κ)
    (hd : 0 < G.d → 2 * mesh ≤ G.d) {b width : ℝ} (hlo : b - width ≤ ∑ i, w i)
    (hhi : ∑ i, w i ≤ b) :
    (∑ i : {i // i ∉ pieceBlock G w mesh T}, w i.val) ≤ b - G.theta (pieceNode G w T) ∧
      b - G.theta (pieceNode G w T) - (width + G.κ) ≤
        ∑ i : {i // i ∉ pieceBlock G w mesh T}, w i.val := by
  have hF := pieceFacts G w T hm hw hwm hg hκ hd
  have hres := residual_width (pieceBlock G w mesh T) w
  have hsub : (pieceNode G w T : ℝ) - G.theta (pieceNode G w T) ≤ G.κ := by
    exact_mod_cast G.sub_theta_le (pieceNode G w T)
  have h1 := hF.theta_le_act
  have h2 := hF.act_le_node
  constructor <;> linarith

/-- **The node budget**: `m + L·Σ_res ≤ B − L·θ` (the `B`-part of the face admissibility at
`vnode2 n low b δ θ`, whose budget is `n.B − n.L·θ`). -/
theorem piece_budget (G : NodeGrid) (w : α → ℝ) {mesh : ℝ} (T : Finset α) (hm : 0 ≤ mesh)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh) (hg : 2 * mesh ≤ G.g) (hκ : 2 * mesh ≤ G.κ)
    (hd : 0 < G.d → 2 * mesh ≤ G.d) {m L B : ℝ} (hL : 0 ≤ L) (hB : m + L * ∑ i, w i ≤ B) :
    m + L * ∑ i : {i // i ∉ pieceBlock G w mesh T}, w i.val ≤
      B - L * G.theta (pieceNode G w T) := by
  have hF := pieceFacts G w T hm hw hwm hg hκ hd
  have hres := residual_width (pieceBlock G w mesh T) w
  have h1 := hF.theta_le_act
  have h3 : L * ∑ i : {i // i ∉ pieceBlock G w mesh T}, w i.val ≤
      L * (∑ i, w i - G.theta (pieceNode G w T)) :=
    mul_le_mul_of_nonneg_left (by linarith) hL
  nlinarith

/-- **The δ-shift of a piece**: with the virtual amplitude `amp + δ` and the actual `amp`,
`hshift` holds with `shiftLoss = 2·mesh` at the residual volume. -/
theorem piece_shift (s : Input α) (w : α → ℝ) {Z : ℝ} (hZ : 1 < Z) (hP : ∀ i, s.P i = Z ^ w i)
    (G : NodeGrid) {mesh : ℝ} (T : Finset α) (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i)
    (hwm : ∀ i, w i ≤ mesh) (hg : 2 * mesh ≤ G.g) (hκ : 2 * mesh ≤ G.κ)
    (hd : 0 < G.d → 2 * mesh ≤ G.d) (amp : ℝ) :
    (amp + pieceNode G w T) - amp ≤
      Real.logb Z (volume s) - Real.logb Z (volume (s.restrict (pieceBlock G w mesh T))) +
        2 * mesh := by
  have hF := pieceFacts G w T hm hw hwm hg hκ hd
  rw [restrict_logb_volume s w hZ hP]
  have := hF.shift
  linarith

/-- `piece_shift` with the `Data` volume of the F4 statements (`volume s.toData`). -/
theorem piece_shift_data (s : Input α) (w : α → ℝ) {Z : ℝ} (hZ : 1 < Z)
    (hP : ∀ i, s.P i = Z ^ w i) (G : NodeGrid) {mesh : ℝ} (T : Finset α) (hm : 0 ≤ mesh)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh) (hg : 2 * mesh ≤ G.g) (hκ : 2 * mesh ≤ G.κ)
    (hd : 0 < G.d → 2 * mesh ≤ G.d) (amp : ℝ) :
    (amp + pieceNode G w T) - amp ≤
      Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume s.toData) -
        Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume
          (s.restrict (pieceBlock G w mesh T)).toData) + 2 * mesh :=
  piece_shift s w hZ hP G T hm hw hwm hg hκ hd amp

/-- **The frozen obligation of a label**, in the form of the forked LOW spine's hypothesis
`φ ≤ Σ_res w − Σ_{live_res} w` (HANDOFF.md, F3): at a non-top node,
`φ = (b − θ) − ε − X` with `X` the live non-transferable width (`0` when `T` is all live slots). -/
theorem piece_frozen_residual (G : NodeGrid) (w : α → ℝ) (mesh : ℝ) (s : Input α) {C : Ideal O}
    (B : actualAllocations s.pools C) (T : Finset α) (hT : T ⊆ liveIndices B.val)
    (hJ : pieceBlock G w mesh T ⊆ liveIndices B.val) (hw : ∀ i, 0 ≤ w i) {b width ε : ℝ}
    (hlo : b - width ≤ ∑ i, w i) (hε : width + G.g + G.κ ≤ ε) (hlow : pieceNode G w T ≠ G.d) :
    b - G.theta (pieceNode G w T) - ε - ∑ i ∈ liveIndices B.val \ T, w i ≤
      (∑ i : {i // i ∉ pieceBlock G w mesh T}, w i.val) -
        ∑ i ∈ liveIndices (allocRestrict s C B (pieceBlock G w mesh T) hJ).val, w i.val := by
  rw [residual_frozen_width s C B (pieceBlock G w mesh T) hJ w]
  apply piece_frozen_obligation G w T hw hlow _ hε
  have h1 := Finset.sum_sdiff hT (f := w)
  have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => B.val (Sum.inl i) = 1) w
  have h3 : liveIndices B.val = Finset.univ.filter (fun i => B.val (Sum.inl i) = 1) := rfl
  rw [← h3] at h2
  linarith

/-- The frozen obligation when every live slot is transferable (`T = live`): `φ = (b − θ) − ε`. -/
theorem piece_frozen_residual_live (G : NodeGrid) (w : α → ℝ) (mesh : ℝ) (s : Input α)
    {C : Ideal O} (B : actualAllocations s.pools C)
    (hJ : pieceBlock G w mesh (liveIndices B.val) ⊆ liveIndices B.val) (hw : ∀ i, 0 ≤ w i)
    {b width ε : ℝ} (hlo : b - width ≤ ∑ i, w i) (hε : width + G.g + G.κ ≤ ε)
    (hlow : pieceNode G w (liveIndices B.val) ≠ G.d) :
    b - G.theta (pieceNode G w (liveIndices B.val)) - ε ≤
      (∑ i : {i // i ∉ pieceBlock G w mesh (liveIndices B.val)}, w i.val) -
        ∑ i ∈ liveIndices (allocRestrict s C B (pieceBlock G w mesh (liveIndices B.val)) hJ).val,
          w i.val := by
  have h := piece_frozen_residual G w mesh s B (liveIndices B.val) le_rfl hJ hw hlo hε hlow
  simpa using h

/-- At the top node the price needs only `0 ≤ f`. -/
theorem piece_frozen_nonneg (s : Input α) {C : Ideal O} (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ (∑ i : {i // i ∉ J}, w i.val) - ∑ i ∈ liveIndices (allocRestrict s C B J hJ).val, w i.val := by
  rw [residual_frozen_width s C B J hJ w]
  exact Finset.sum_nonneg (fun i _ => hw i)

end NodeFacts

end
end QRH.MixedStep.Downstream

#print axioms QRH.MixedStep.Downstream.sum_pieces
#print axioms QRH.MixedStep.Downstream.card_pieces_le
#print axioms QRH.MixedStep.Downstream.residual_frozen_width
#print axioms QRH.MixedStep.Downstream.restrict_logb_volume
#print axioms QRH.MixedStep.Downstream.piece_radius
#print axioms QRH.MixedStep.Downstream.restrict_empty_energy
#print axioms QRH.MixedStep.Downstream.piece_width
#print axioms QRH.MixedStep.Downstream.piece_budget
#print axioms QRH.MixedStep.Downstream.piece_shift_data
#print axioms QRH.MixedStep.Downstream.piece_frozen_residual
#print axioms QRH.MixedStep.Downstream.piece_frozen_residual_live
#print axioms QRH.MixedStep.Downstream.piece_frozen_nonneg
