/- Mixed source step, N3 (families): new in this submission. Uses the transfer's contracts
(`Residual/Waist.lean`, `Residual/SupplierWaist.lean`) and Collet's definitions by import; no code
is adapted.

The first MAIN sum `Σ_l amplitude_l·E_l` of Collet's `eventual_selected_main`, with
`E_l = correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) 1 P (alloc l) (columnCharacter … (column l))
t (volume s) (firstMainRadius … (volume s) … (3·amp) …)`, is bounded by a sum over **families**
`(piece k, ray ξ)` (`L45_DESIGN.md` §2.3–2.4). Each family is literally the input of Collet's
`eventual_selected_second`: one common parent `s.restrict J_k`, the original `R`, the common
`T = volume (s.restrict J_k)`, labels `{l // pieceKey alloc trans l = k}`, common ideals `C l`,
seeds `L l` (unchanged under (S)), allocations `allocRestrict (alloc l) J_k`, characters
`columnCharacter … (rayShift (column l) ξ)`, radii `firstMainRadius … (volume (s.restrict J_k)) …
(3·(amp + δ_k)) …` (the virtual amplitude `a_v = amp + δ_k`), and the original amplitudes.

* `piece_label_transfer`: one label, any block `J` with `(δ = 0 ∧ J = ∅) ∨ (0 < δ ∧ Σ_J w ≤ δ − mesh)`.
  For `δ > 0` it is the transfer's `transfer_waist_column` (radius condition by `piece_radius`); for
  `δ = 0` it is `restrict_empty_energy` and the ray `ξ = 1`.
* `pieces_transfer`: the whole sum, with the node `δ_k = pieceNode G w (trans)` and the block
  `J_k = pieceBlock G w mesh (trans)` of each piece. Hypotheses beyond the grid arithmetic: (S) on
  the transferable slots (`hseed`), (Col) on the blocks (`hcol`; L3), and `H' ≤ Z^A`.
* `piece_label_transfer_supplier`, `pieces_transfer_supplier`: the same without (S) (all live slots
  transferable, `trans = live`), from `transfer_waist_supplier_column`; each label then carries a
  finite set of residual seeds `L' ∣ L l`. -/
import Submissions.arvi_mixed_step.Downstream.Pieces
import Submissions.arvi_mixed_step.Residual.SupplierWaist

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
open RayFourExpansion CanonicalQuadraticSieve Cycle61InitialMass Cycle61Moment
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer QRH.MixedStep.Residual
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-! ### One label -/

theorem prod_M_sq_le {α : Type*} [Fintype α] (s : Input α) (J : Finset α) (N : ℕ)
    (hJ : J.card ≤ N) (Mmax : ℝ) (hM1 : 1 ≤ Mmax) (hM : ∀ i, s.M i ≤ Mmax) :
    ∏ j ∈ J, s.M j ^ 2 ≤ Mmax ^ (2 * N) := by
  calc ∏ j ∈ J, s.M j ^ 2 ≤ ∏ _j ∈ J, Mmax ^ 2 :=
        Finset.prod_le_prod₀ (fun j _ => sq_nonneg _)
          (fun j _ => pow_le_pow_left₀ (zero_le_one.trans (s.M_ge_one j)) (hM j) 2)
    _ = Mmax ^ (2 * J.card) := by rw [Finset.prod_const, ← pow_mul]
    _ ≤ Mmax ^ (2 * N) := pow_le_pow_right₀ hM1 (by omega)

/-- **The transfer of one label to its piece's residual** (both node cases). -/
theorem piece_label_transfer (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      SeedFree s J L → (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ (w : α → ℝ) (Z mesh : ℝ), 1 < Z → (∀ i, s.P i = Z ^ w i) → (∀ i, 0 ≤ w i) →
      Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh →
    ∀ (δ : ℝ), (δ = 0 ∧ J = ∅) ∨ (0 < δ ∧ ∑ j ∈ J, w j ≤ δ - mesh) →
    ∀ {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (t amp reserve A : ℝ), 0 ≤ A →
      firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ≤ Z ^ A →
      NoCollision s C R L B J
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t →
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
          (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) ≤
        K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (volume (s.restrict J))
            (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
              (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) := by
  obtain ⟨K, hK0, hd⟩ := transfer_waist_column.{0, 0} ε hε N
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro α _ _ hcard s C R L P hp hPA B J hJ hSF hhi w Z mesh hZ hP hw hmesh δ hδ ι₀ _ _ reflected
    s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c t amp reserve A hA hHA hNC
  have hZ0 : 0 < Z := by linarith
  have hZA : 1 ≤ Z ^ (A * ε) := Real.one_le_rpow hZ.le (mul_nonneg hA hε.le)
  have hMJ : 1 ≤ ∏ j ∈ J, s.M j ^ 2 := by
    calc (1 : ℝ) = ∏ _j ∈ J, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ j ∈ J, s.M j ^ 2 :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (s.M_ge_one j))
  have hfac : 1 ≤ max K 1 * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) := by
    have h1 : 1 ≤ max K 1 * (∏ j ∈ J, s.M j ^ 2) :=
      one_le_mul_of_one_le_of_one_le (le_max_right _ _) hMJ
    exact one_le_mul_of_one_le_of_one_le h1 hZA
  rcases hδ with ⟨rfl, rfl⟩ | ⟨hδ0, hact⟩
  · -- node 0: no transfer
    have hV : volume (s.restrict ∅) = volume s := by
      rw [volume_restrict, Finset.prod_empty, div_one]
    rw [hV, add_zero]
    rw [restrict_empty_energy s C R L P B _ t (volume s) _]
    set E : RayCharacter → ℝ := fun ξ => correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L
      (fun _ => 1) P (allocRestrict s C B ∅ hJ)
      (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
      t (volume s) (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) with hE
    have hHpos : 0 < firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) :=
      first_main_radius_pos _ _ _ _ _ _ _ hZ0 _
    have hEnn : ∀ ξ, 0 ≤ E ξ := fun ξ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hHpos
    have h1 : correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B ∅ (Finset.empty_subset _))
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
        (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) = E 1 := by
      rw [hE]
      dsimp only
      rw [rayShift_one]
    rw [h1]
    calc E 1 ≤ ∑ ξ : RayCharacter, E ξ :=
          Finset.single_le_sum (fun ξ _ => hEnn ξ) (Finset.mem_univ _)
      _ = 1 * ∑ ξ : RayCharacter, E ξ := (one_mul _).symm
      _ ≤ max K 1 * (∏ j ∈ (∅ : Finset α), s.M j ^ 2) * Z ^ (A * ε) * ∑ ξ : RayCharacter, E ξ :=
          mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg (fun ξ _ => hEnn ξ))
  · -- positive node: the transfer
    have hJN : J.card ≤ N := (Finset.card_le_univ J).trans hcard
    have hrad := piece_radius reflected K₀ (volume s) Z ξ₀ amp δ reserve mesh
      (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) hZ N J hJN w s.P hP hw hmesh hact
    have hV : volume (s.restrict J) = volume s / ∏ j ∈ J, s.P j := volume_restrict s J
    have hHpos : 0 < firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) :=
      first_main_radius_pos _ _ _ _ _ _ _ hZ0 _
    have hrad' : 2 * 16 ^ J.card * firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) * (∏ j ∈ J, s.P j) ^ 4 ≤
        firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) := by
      rw [hV]
      exact hrad
    have h := hd hcard s C R L P hp hPA B J hJ hSF hhi reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK
      key c t (volume s) _ _ Z A hHpos hrad' hZ.le hA hHA hNC
    rw [← hV] at h
    refine h.trans ?_
    have hsum : 0 ≤ ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L
        (fun _ => 1) P (allocRestrict s C B J hJ)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
        t (volume (s.restrict J))
        (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) :=
      Finset.sum_nonneg (fun ξ _ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _))
    have hM0 : 0 ≤ ∏ j ∈ J, s.M j ^ 2 := Finset.prod_nonneg (fun j _ => sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0) (Real.rpow_nonneg hZ0.le _)) hsum

/-! ### The families of the pieces -/

section Assembly
variable {α : Type} [Fintype α] [DecidableEq α] {Label : Type} [Fintype Label]
  (s : Input α) (C : Label → Ideal O) (alloc : ∀ l, actualAllocations s.pools (C l))
  (trans : Label → Finset α) (htrans : ∀ l, trans l ⊆ liveIndices (alloc l).val)
  (G : NodeGrid) (w : α → ℝ) (mesh : ℝ)

include htrans in
/-- The block of a piece lies in the live slots of each of its labels. -/
theorem pieceBlock_sub_live {k : Finset α × Finset α} (l : {l // pieceKey alloc trans l = k}) :
    pieceBlock G w mesh k.2 ⊆ liveIndices (alloc l.val).val := by
  obtain ⟨l, rfl⟩ := l
  exact (pieceBlock_subset G w mesh _).trans (htrans l)

/-- The residual allocation of a label of the piece `k`. -/
def pieceAlloc {k : Finset α × Finset α} (l : {l // pieceKey alloc trans l = k}) :
    actualAllocations (s.restrict (pieceBlock G w mesh k.2)).pools (C l.val) :=
  allocRestrict s (C l.val) (alloc l.val) (pieceBlock G w mesh k.2)
    (pieceBlock_sub_live s C alloc trans htrans G w mesh l)

/-- The residual energy of a label `l` of the family `(k, ξ)`: Collet's corrected child energy of
the common parent `s.restrict J_k`, with `T = volume (s.restrict J_k)` and the MAIN radius at the
residual volume and the virtual amplitude `amp + δ_k`. -/
def pieceEnergy {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
    (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
    (key : ℤ × (Fin 5 → ℤ)) (column : Label → FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
    (L : Label → Ideal O) (R : Ideal O) (P : Finset (Ideal O)) (t Z amp reserve : ℝ)
    (k : Finset α × Finset α) (ξ : RayCharacter) (l : {l // pieceKey alloc trans l = k}) : ℝ :=
  correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh k.2)) 1 1 1 1 (C l.val) R (L l.val)
    (fun _ => 1) P (pieceAlloc s C alloc trans htrans G w mesh l)
    (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected (column l.val) ξ))
    t (volume (s.restrict (pieceBlock G w mesh k.2)))
    (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh k.2))) Z ξ₀
      (3 * (amp + pieceNode G w k.2)) reserve
      (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l.val)))

end Assembly

/-- **The assembly of the pieces**, from any bound of each label by the residual of its piece
(`hlab`, in the form of `piece_label_transfer`'s conclusion at `J = pieceBlock G w mesh (trans l)`). -/
theorem pieces_sum_of_labels {α : Type} [Fintype α] [DecidableEq α] (N : ℕ)
    (hcard : Fintype.card α ≤ N) (s : Input α) (w : α → ℝ) (Z mesh Mmax K A ε : ℝ) (hZ : 1 < Z)
    (hM1 : 1 ≤ Mmax) (hM : ∀ i, s.M i ≤ Mmax) (hK : 0 ≤ K) (G : NodeGrid)
    {Label : Type} [Fintype Label] (C L : Label → Ideal O)
    (alloc : ∀ l, actualAllocations s.pools (C l)) (trans : Label → Finset α)
    (htrans : ∀ l, trans l ⊆ liveIndices (alloc l).val)
    {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
    (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK₀ : 0 < K₀)
    (key : ℤ × (Fin 5 → ℤ))
    (column : Label → FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key))
    (R : Ideal O) (P : Finset (Ideal O)) (amplitude : Label → ℝ) (ha : ∀ l, 0 ≤ amplitude l)
    (t amp reserve : ℝ)
    (hlab : ∀ l, correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) (fun _ => 1) P (alloc l)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)) t (volume s)
        (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l))) ≤
      K * (∏ j ∈ pieceBlock G w mesh (trans l), s.M j ^ 2) * Z ^ (A * ε) *
        ∑ ξ : RayCharacter,
          correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R
            (L l) (fun _ => 1) P
            (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l))
              ((pieceBlock_subset G w mesh _).trans (htrans l)))
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key
              (rayShift reflected (column l) ξ)) t
            (volume (s.restrict (pieceBlock G w mesh (trans l))))
            (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
              (3 * (amp + pieceNode G w (trans l))) reserve
              (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)))) :
    ∑ l, amplitude l * correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) (fun _ => 1) P (alloc l)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)) t (volume s)
        (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l))) ≤
      K * Mmax ^ (2 * N) * Z ^ (A * ε) *
        ∑ k ∈ Finset.univ.image (pieceKey alloc trans), ∑ ξ : RayCharacter,
          ∑ l : {l // pieceKey alloc trans l = k}, amplitude l.val *
            pieceEnergy s C alloc trans htrans G w mesh reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀
              key column L R P t Z amp reserve k ξ l := by
  have hZ0 : 0 < Z := by linarith
  rw [sum_pieces (pieceKey alloc trans), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  obtain ⟨l, rfl⟩ := l
  have hJ : pieceBlock G w mesh (trans l) ⊆ liveIndices (alloc l).val :=
    (pieceBlock_subset G w mesh _).trans (htrans l)
  have hpE : ∀ ξ : RayCharacter,
      pieceEnergy s C alloc trans htrans G w mesh reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key
        column L R P t Z amp reserve (pieceKey alloc trans l) ξ ⟨l, rfl⟩ =
      correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R (L l)
        (fun _ => 1) P (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) hJ)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key
          (rayShift reflected (column l) ξ)) t
        (volume (s.restrict (pieceBlock G w mesh (trans l))))
        (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
          (3 * (amp + pieceNode G w (trans l))) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l))) := fun ξ => rfl
  simp only [hpE]
  have hJN : (pieceBlock G w mesh (trans l)).card ≤ N :=
    (Finset.card_le_univ _).trans hcard
  have hMM := prod_M_sq_le s (pieceBlock G w mesh (trans l)) N hJN Mmax hM1 hM
  have hsum : 0 ≤ ∑ ξ : RayCharacter,
      correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R (L l)
        (fun _ => 1) P (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) hJ)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key
          (rayShift reflected (column l) ξ)) t
        (volume (s.restrict (pieceBlock G w mesh (trans l))))
        (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
          (3 * (amp + pieceNode G w (trans l))) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l))) :=
    Finset.sum_nonneg (fun ξ _ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _))
  have hZA : 0 ≤ Z ^ (A * ε) := Real.rpow_nonneg hZ0.le _
  calc amplitude l * correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) (fun _ => 1) P (alloc l)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)) t (volume s)
        (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)))
      ≤ amplitude l * (K * (∏ j ∈ pieceBlock G w mesh (trans l), s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter,
            correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R
              (L l) (fun _ => 1) P (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) hJ)
              (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key
                (rayShift reflected (column l) ξ)) t
              (volume (s.restrict (pieceBlock G w mesh (trans l))))
              (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
                (3 * (amp + pieceNode G w (trans l))) reserve
                (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)))) :=
        mul_le_mul_of_nonneg_left (hlab l) (ha l)
    _ ≤ amplitude l * (K * Mmax ^ (2 * N) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter,
            correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R
              (L l) (fun _ => 1) P (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) hJ)
              (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key
                (rayShift reflected (column l) ξ)) t
              (volume (s.restrict (pieceBlock G w mesh (trans l))))
              (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
                (3 * (amp + pieceNode G w (trans l))) reserve
                (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK₀ key (column l)))) := by
        apply mul_le_mul_of_nonneg_left _ (ha l)
        apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ hZA
        exact mul_le_mul_of_nonneg_left hMM hK
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ _
        ring

/-- The window of a piece in the form of the label transfer. -/
theorem piece_window {α : Type*} [Fintype α] (G : NodeGrid) (w : α → ℝ) {mesh : ℝ} (T : Finset α)
    (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh) (hg : 2 * mesh ≤ G.g)
    (hκ : 2 * mesh ≤ G.κ) (hd : 0 < G.d → 2 * mesh ≤ G.d) :
    ((pieceNode G w T : ℝ) = 0 ∧ pieceBlock G w mesh T = ∅) ∨
      (0 < (pieceNode G w T : ℝ) ∧
        ∑ j ∈ pieceBlock G w mesh T, w j ≤ (pieceNode G w T : ℝ) - mesh) := by
  rcases (pieceFacts G w T hm hw hwm hg hκ hd).zero_or_window with ⟨h0, hJ0⟩ | ⟨hpos, hact⟩
  · left
    exact ⟨by rw [h0]; simp, hJ0⟩
  · right
    exact ⟨by exact_mod_cast hpos, hact⟩

/-- **N3: the first MAIN sum is bounded by the families of its pieces.** For every piece
`k = (live, trans)` (at most `4^N`) and ray `ξ`, the family is the input of Collet's
`eventual_selected_second` (see `pieceEnergy`). -/
theorem pieces_transfer (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (w : α → ℝ) (Z mesh Mmax : ℝ), 1 < Z → (∀ i, s.P i = Z ^ w i) →
      (∀ i, 0 ≤ s.hi i ∧ s.hi i ≤ 2) → 1 ≤ Mmax → (∀ i, s.M i ≤ Mmax) → 0 ≤ mesh →
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh →
    ∀ (G : NodeGrid), 2 * mesh ≤ G.g → 2 * mesh ≤ G.κ → (0 < G.d → 2 * mesh ≤ G.d) →
    ∀ {Label : Type} [Fintype Label] (C L : Label → Ideal O)
      (alloc : ∀ l, actualAllocations s.pools (C l)) (trans : Label → Finset α)
      (htrans : ∀ l, trans l ⊆ liveIndices (alloc l).val), (∀ l, SeedFree s (trans l) (L l)) →
    ∀ {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ))
      (column : Label → FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (R : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) → PoolAvoids P s →
    ∀ (amplitude : Label → ℝ), (∀ l, 0 ≤ amplitude l) →
    ∀ (t amp reserve A : ℝ), 0 ≤ A →
      (∀ l, firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
        (3 * (amp + pieceNode G w (trans l))) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) ≤ Z ^ A) →
      (∀ l, NoCollision s (C l) R (L l) (alloc l) (pieceBlock G w mesh (trans l))
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) t) →
      ∑ l, amplitude l * correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) (fun _ => 1) P (alloc l)
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) t (volume s)
          (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l))) ≤
        K * Mmax ^ (2 * N) * Z ^ (A * ε) *
          ∑ k ∈ Finset.univ.image (pieceKey alloc trans), ∑ ξ : RayCharacter,
            ∑ l : {l // pieceKey alloc trans l = k}, amplitude l.val *
              pieceEnergy s C alloc trans htrans G w mesh reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK
                key column L R P t Z amp reserve k ξ l := by
  obtain ⟨K, hK1, hlab⟩ := piece_label_transfer ε hε N
  refine ⟨K, hK1, ?_⟩
  intro α _ _ hcard s w Z mesh Mmax hZ hP hhi hM1 hM hm hw hwm hmesh G hg hκ hd Label _ C L alloc
    trans htrans hseed ι₀ _ _ reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key column R P hp hPA
    amplitude ha t amp reserve A hA hHA hNC
  apply pieces_sum_of_labels N hcard s w Z mesh Mmax K A ε hZ hM1 hM (by linarith) G C L alloc trans
    htrans reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key column R P amplitude ha t amp reserve
  intro l
  exact hlab hcard s (C l) R (L l) P hp hPA (alloc l) (pieceBlock G w mesh (trans l))
    ((pieceBlock_subset G w mesh _).trans (htrans l))
    (fun j hj => hseed l j (pieceBlock_subset G w mesh _ hj)) (fun j _ => hhi j) w Z mesh hZ hP hw
    hmesh (pieceNode G w (trans l)) (piece_window G w (trans l) hm hw hwm hg hκ hd) reflected s₀
    modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l) t amp reserve A hA (hHA l) (hNC l)

/-! ### The plain-family transfer contract -/

/-- **The plain-family transfer contract**: every label transfers to the plain families of its
pieces (seed unchanged, no collision families), with no (S)/(Col) premises. Under (S) and (Col)
this is `piece_label_transfer` (proved). Without them the transfer has more families (residual
seeds `L′ ∣ L`: `piece_label_transfer_supplier`; collision families: L3), which this contract does
not cover; it is the hypothesis of `balanced_of_regular3` until those families are paid. -/
def PlainTransfer : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type} [Fintype α] [DecidableEq α],
    Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ (w : α → ℝ) (Z mesh : ℝ), 1 < Z → (∀ i, s.P i = Z ^ w i) → (∀ i, 0 ≤ w i) →
      Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh →
    ∀ (δ : ℝ), (δ = 0 ∧ J = ∅) ∨ (0 < δ ∧ ∑ j ∈ J, w j ≤ δ - mesh) →
    ∀ {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (t amp reserve A : ℝ), 0 ≤ A →
      firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ≤ Z ^ A →
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
          (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) ≤
        K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (volume (s.restrict J))
            (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
              (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c))

/-- `pieces_transfer` from the plain-family contract (no (S)/(Col) hypotheses). -/
theorem pieces_transfer_plain (htr : PlainTransfer) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (w : α → ℝ) (Z mesh Mmax : ℝ), 1 < Z → (∀ i, s.P i = Z ^ w i) →
      (∀ i, 0 ≤ s.hi i ∧ s.hi i ≤ 2) → 1 ≤ Mmax → (∀ i, s.M i ≤ Mmax) → 0 ≤ mesh →
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh →
    ∀ (G : NodeGrid), 2 * mesh ≤ G.g → 2 * mesh ≤ G.κ → (0 < G.d → 2 * mesh ≤ G.d) →
    ∀ {Label : Type} [Fintype Label] (C L : Label → Ideal O)
      (alloc : ∀ l, actualAllocations s.pools (C l)) (trans : Label → Finset α)
      (htrans : ∀ l, trans l ⊆ liveIndices (alloc l).val),
    ∀ {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ))
      (column : Label → FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (R : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) → PoolAvoids P s →
    ∀ (amplitude : Label → ℝ), (∀ l, 0 ≤ amplitude l) →
    ∀ (t amp reserve A : ℝ), 0 ≤ A →
      (∀ l, firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
        (3 * (amp + pieceNode G w (trans l))) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) ≤ Z ^ A) →
      ∑ l, amplitude l * correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) (fun _ => 1) P (alloc l)
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) t (volume s)
          (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l))) ≤
        K * Mmax ^ (2 * N) * Z ^ (A * ε) *
          ∑ k ∈ Finset.univ.image (pieceKey alloc trans), ∑ ξ : RayCharacter,
            ∑ l : {l // pieceKey alloc trans l = k}, amplitude l.val *
              pieceEnergy s C alloc trans htrans G w mesh reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK
                key column L R P t Z amp reserve k ξ l := by
  obtain ⟨K, hK1, hlab⟩ := htr ε hε N
  refine ⟨K, hK1, ?_⟩
  intro α _ _ hcard s w Z mesh Mmax hZ hP hhi hM1 hM hm hw hwm hmesh G hg hκ hd Label _ C L alloc
    trans htrans ι₀ _ _ reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key column R P hp hPA
    amplitude ha t amp reserve A hA hHA
  apply pieces_sum_of_labels N hcard s w Z mesh Mmax K A ε hZ hM1 hM (by linarith) G C L alloc trans
    htrans reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key column R P amplitude ha t amp reserve
  intro l
  exact hlab hcard s (C l) R (L l) P hp hPA (alloc l) (pieceBlock G w mesh (trans l))
    ((pieceBlock_subset G w mesh _).trans (htrans l)) (fun j _ => hhi j) w Z mesh hZ hP hw
    hmesh (pieceNode G w (trans l)) (piece_window G w (trans l) hm hw hwm hg hκ hd) reflected s₀
    modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l) t amp reserve A hA (hHA l)

/-! ### Without the seed condition (S): residual seeds -/

/-- **The transfer of one label without (S)** (`transfer_waist_supplier_column`): the residual
energies carry residual seeds `L' ∣ L` from a finite set. At node 0 the set is `{L}`. -/
theorem piece_label_transfer_supplier (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s → Squarefree L →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ (w : α → ℝ) (Z mesh : ℝ), 1 < Z → (∀ i, s.P i = Z ^ w i) → (∀ i, 0 ≤ w i) →
      Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh →
    ∀ (δ : ℝ), (δ = 0 ∧ J = ∅) ∨ (0 < δ ∧ ∑ j ∈ J, w j ≤ δ - mesh) →
    ∀ {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (t amp reserve A : ℝ), 0 ≤ A →
      firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ≤ Z ^ A →
      NoCollision s C R L B J
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
          (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) ≤
        K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
              (allocRestrict s C B J hJ)
              (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
              t (volume (s.restrict J))
              (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
                (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) := by
  obtain ⟨K, hK0, hd⟩ := transfer_waist_supplier_column.{0, 0} ε hε N
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro α _ _ hcard s C R L P hp hPA hLsq B J hJ hhi w Z mesh hZ hP hw hmesh δ hδ ι₀ _ _ reflected
    s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c t amp reserve A hA hHA hNC
  have hZ0 : 0 < Z := by linarith
  have hZA : 1 ≤ Z ^ (A * ε) := Real.one_le_rpow hZ.le (mul_nonneg hA hε.le)
  have hMJ : 1 ≤ ∏ j ∈ J, s.M j ^ 2 := by
    calc (1 : ℝ) = ∏ _j ∈ J, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ j ∈ J, s.M j ^ 2 :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (s.M_ge_one j))
  have hfac : 1 ≤ max K 1 * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) := by
    have h1 : 1 ≤ max K 1 * (∏ j ∈ J, s.M j ^ 2) :=
      one_le_mul_of_one_le_of_one_le (le_max_right _ _) hMJ
    exact one_le_mul_of_one_le_of_one_le h1 hZA
  rcases hδ with ⟨rfl, rfl⟩ | ⟨hδ0, hact⟩
  · -- node 0: no transfer, the seed is kept
    refine ⟨{L}, fun L' hL' => by rw [Finset.mem_singleton.mp hL'], ?_⟩
    have hV : volume (s.restrict ∅) = volume s := by
      rw [volume_restrict, Finset.prod_empty, div_one]
    rw [hV, add_zero]
    rw [restrict_empty_energy s C R L P B _ t (volume s) _]
    simp only [Finset.sum_singleton]
    set E : RayCharacter → ℝ := fun ξ => correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L
      (fun _ => 1) P (allocRestrict s C B ∅ hJ)
      (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
      t (volume s) (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) with hE
    have hHpos : 0 < firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) :=
      first_main_radius_pos _ _ _ _ _ _ _ hZ0 _
    have hEnn : ∀ ξ, 0 ≤ E ξ := fun ξ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hHpos
    have h1 : correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B ∅ (Finset.empty_subset _))
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
        (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) = E 1 := by
      rw [hE]
      dsimp only
      rw [rayShift_one]
    rw [h1]
    calc E 1 ≤ ∑ ξ : RayCharacter, E ξ :=
          Finset.single_le_sum (fun ξ _ => hEnn ξ) (Finset.mem_univ _)
      _ = 1 * ∑ ξ : RayCharacter, E ξ := (one_mul _).symm
      _ ≤ max K 1 * (∏ j ∈ (∅ : Finset α), s.M j ^ 2) * Z ^ (A * ε) * ∑ ξ : RayCharacter, E ξ :=
          mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg (fun ξ _ => hEnn ξ))
  · -- positive node: the supplier transfer
    have hJN : J.card ≤ N := (Finset.card_le_univ J).trans hcard
    have hrad := piece_radius reflected K₀ (volume s) Z ξ₀ amp δ reserve mesh
      (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) hZ N J hJN w s.P hP hw hmesh hact
    have hV : volume (s.restrict J) = volume s / ∏ j ∈ J, s.P j := volume_restrict s J
    have hHpos : 0 < firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) :=
      first_main_radius_pos _ _ _ _ _ _ _ hZ0 _
    have hrad' : 2 * 16 ^ J.card * firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) * (∏ j ∈ J, s.P j) ^ 4 ≤
        firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) := by
      rw [hV]
      exact hrad
    obtain ⟨seeds, hseeds, h⟩ := hd hcard s C R L P hp hPA hLsq B J hJ hhi reflected s₀ modifier
      R₀ seed K₀ Z₀ ξ₀ hK key c t (volume s) _ _ Z A hHpos hrad' hZ.le hA hHA hNC
    refine ⟨seeds, hseeds, ?_⟩
    rw [← hV] at h
    refine h.trans ?_
    have hsum : 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
        correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
          (allocRestrict s C B J hJ)
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
          t (volume (s.restrict J))
          (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) :=
      Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
        corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _)))
    have hM0 : 0 ≤ ∏ j ∈ J, s.M j ^ 2 := Finset.prod_nonneg (fun j _ => sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0) (Real.rpow_nonneg hZ0.le _)) hsum

section AssemblySeed
variable {α : Type} [Fintype α] [DecidableEq α] {Label : Type} [Fintype Label]
  (s : Input α) (C : Label → Ideal O) (alloc : ∀ l, actualAllocations s.pools (C l))
  (trans : Label → Finset α) (htrans : ∀ l, trans l ⊆ liveIndices (alloc l).val)
  (G : NodeGrid) (w : α → ℝ) (mesh : ℝ)

/-- The residual energy of a label of the family `(k, ξ)` at the residual seed `L'`
(`pieceEnergy … L … k ξ l = pieceEnergySeed … (L l.val) k ξ l` by `rfl`). -/
def pieceEnergySeed {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
    (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
    (key : ℤ × (Fin 5 → ℤ)) (column : Label → FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
    (R : Ideal O) (P : Finset (Ideal O)) (t Z amp reserve : ℝ) (L' : Ideal O)
    (k : Finset α × Finset α) (ξ : RayCharacter) (l : {l // pieceKey alloc trans l = k}) : ℝ :=
  correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh k.2)) 1 1 1 1 (C l.val) R L'
    (fun _ => 1) P (pieceAlloc s C alloc trans htrans G w mesh l)
    (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected (column l.val) ξ))
    t (volume (s.restrict (pieceBlock G w mesh k.2)))
    (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh k.2))) Z ξ₀
      (3 * (amp + pieceNode G w k.2)) reserve
      (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l.val)))

end AssemblySeed

/-- **N3 without (S)**: the first MAIN sum is bounded by the families `(k, ξ)` of its pieces, each
label carrying finitely many residual seeds `L' ∣ L l`. With `trans = live` every live slot is
transferable, so the frozen obligation holds with `X = 0` (`piece_frozen_residual_live`). -/
theorem pieces_transfer_supplier (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (w : α → ℝ) (Z mesh Mmax : ℝ), 1 < Z → (∀ i, s.P i = Z ^ w i) →
      (∀ i, 0 ≤ s.hi i ∧ s.hi i ≤ 2) → 1 ≤ Mmax → (∀ i, s.M i ≤ Mmax) → 0 ≤ mesh →
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh →
    ∀ (G : NodeGrid), 2 * mesh ≤ G.g → 2 * mesh ≤ G.κ → (0 < G.d → 2 * mesh ≤ G.d) →
    ∀ {Label : Type} [Fintype Label] (C L : Label → Ideal O)
      (alloc : ∀ l, actualAllocations s.pools (C l)) (trans : Label → Finset α)
      (htrans : ∀ l, trans l ⊆ liveIndices (alloc l).val), (∀ l, Squarefree (L l)) →
    ∀ {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ))
      (column : Label → FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (R : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) → PoolAvoids P s →
    ∀ (amplitude : Label → ℝ), (∀ l, 0 ≤ amplitude l) →
    ∀ (t amp reserve A : ℝ), 0 ≤ A →
      (∀ l, firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
        (3 * (amp + pieceNode G w (trans l))) reserve
        (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) ≤ Z ^ A) →
      (∀ l, NoCollision s (C l) R (L l) (alloc l) (pieceBlock G w mesh (trans l))
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) t) →
      ∃ seeds : Label → Finset (Ideal O), (∀ l, ∀ L' ∈ seeds l, L' ∣ L l) ∧
      ∑ l, amplitude l * correctedChildGaussEnergy s 1 1 1 1 (C l) R (L l) (fun _ => 1) P (alloc l)
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)) t (volume s)
          (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
            (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l))) ≤
        K * Mmax ^ (2 * N) * Z ^ (A * ε) *
          ∑ k ∈ Finset.univ.image (pieceKey alloc trans), ∑ ξ : RayCharacter,
            ∑ l : {l // pieceKey alloc trans l = k}, ∑ L' ∈ seeds l.val, amplitude l.val *
              pieceEnergySeed s C alloc trans htrans G w mesh reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK
                key column R P t Z amp reserve L' k ξ l := by
  obtain ⟨K, hK1, hlab⟩ := piece_label_transfer_supplier ε hε N
  refine ⟨K, hK1, ?_⟩
  intro α _ _ hcard s w Z mesh Mmax hZ hP hhi hM1 hM hm hw hwm hmesh G hg hκ hd Label _ C L alloc
    trans htrans hLsq ι₀ _ _ reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key column R P hp hPA
    amplitude ha t amp reserve A hA hHA hNC
  have hZ0 : 0 < Z := by linarith
  have hJ : ∀ l, pieceBlock G w mesh (trans l) ⊆ liveIndices (alloc l).val :=
    fun l => (pieceBlock_subset G w mesh _).trans (htrans l)
  have hwin : ∀ l, ((pieceNode G w (trans l) : ℝ) = 0 ∧ pieceBlock G w mesh (trans l) = ∅) ∨
      (0 < (pieceNode G w (trans l) : ℝ) ∧
        ∑ j ∈ pieceBlock G w mesh (trans l), w j ≤ (pieceNode G w (trans l) : ℝ) - mesh) := by
    intro l
    rcases (pieceFacts G w (trans l) hm hw hwm hg hκ hd).zero_or_window with ⟨h0, hJ0⟩ |
      ⟨hpos, hact⟩
    · left
      exact ⟨by rw [h0]; simp, hJ0⟩
    · right
      exact ⟨by exact_mod_cast hpos, hact⟩
  have hE := fun l => hlab hcard s (C l) R (L l) P hp hPA (hLsq l) (alloc l)
    (pieceBlock G w mesh (trans l)) (hJ l) (fun j _ => hhi j) w Z mesh hZ hP hw hmesh
    (pieceNode G w (trans l)) (hwin l) reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l) t
    amp reserve A hA (hHA l) (hNC l)
  choose seeds hseeds hbound using hE
  refine ⟨seeds, hseeds, ?_⟩
  rw [sum_pieces (pieceKey alloc trans), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  obtain ⟨l, rfl⟩ := l
  have hpE : ∀ (ξ : RayCharacter) (L' : Ideal O),
      pieceEnergySeed s C alloc trans htrans G w mesh reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
        column R P t Z amp reserve L' (pieceKey alloc trans l) ξ ⟨l, rfl⟩ =
      correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R L'
        (fun _ => 1) P (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) (hJ l))
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
          (rayShift reflected (column l) ξ)) t
        (volume (s.restrict (pieceBlock G w mesh (trans l))))
        (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
          (3 * (amp + pieceNode G w (trans l))) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l))) := fun ξ L' => rfl
  simp only [hpE]
  have hJN : (pieceBlock G w mesh (trans l)).card ≤ N :=
    (Finset.card_le_univ _).trans hcard
  have hMM := prod_M_sq_le s (pieceBlock G w mesh (trans l)) N hJN Mmax hM1 hM
  have hsum : 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seeds l,
      correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R L'
        (fun _ => 1) P (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) (hJ l))
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
          (rayShift reflected (column l) ξ)) t
        (volume (s.restrict (pieceBlock G w mesh (trans l))))
        (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
          (3 * (amp + pieceNode G w (trans l))) reserve
          (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l))) :=
    Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
      corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _)))
  have hZA : 0 ≤ Z ^ (A * ε) := Real.rpow_nonneg hZ0.le _
  calc _ ≤ amplitude l * (K * (∏ j ∈ pieceBlock G w mesh (trans l), s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds l,
            correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R
              L' (fun _ => 1) P
              (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) (hJ l))
              (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
                (rayShift reflected (column l) ξ)) t
              (volume (s.restrict (pieceBlock G w mesh (trans l))))
              (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
                (3 * (amp + pieceNode G w (trans l))) reserve
                (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)))) :=
        mul_le_mul_of_nonneg_left (hbound l) (ha l)
    _ ≤ amplitude l * (K * Mmax ^ (2 * N) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds l,
            correctedChildGaussEnergy (s.restrict (pieceBlock G w mesh (trans l))) 1 1 1 1 (C l) R
              L' (fun _ => 1) P
              (allocRestrict s (C l) (alloc l) (pieceBlock G w mesh (trans l)) (hJ l))
              (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
                (rayShift reflected (column l) ξ)) t
              (volume (s.restrict (pieceBlock G w mesh (trans l))))
              (firstMainRadius reflected K₀ (volume (s.restrict (pieceBlock G w mesh (trans l)))) Z ξ₀
                (3 * (amp + pieceNode G w (trans l))) reserve
                (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (column l)))) := by
        apply mul_le_mul_of_nonneg_left _ (ha l)
        apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ hZA
        exact mul_le_mul_of_nonneg_left hMM (by linarith)
    _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ _
        apply Finset.sum_congr rfl
        intro L' _
        ring

end
end QRH.MixedStep.Downstream

#print axioms QRH.MixedStep.Downstream.piece_label_transfer
#print axioms QRH.MixedStep.Downstream.pieces_transfer
#print axioms QRH.MixedStep.Downstream.pieces_sum_of_labels
#print axioms QRH.MixedStep.Downstream.pieces_transfer_plain
#print axioms QRH.MixedStep.Downstream.piece_label_transfer_supplier
#print axioms QRH.MixedStep.Downstream.pieces_transfer_supplier
