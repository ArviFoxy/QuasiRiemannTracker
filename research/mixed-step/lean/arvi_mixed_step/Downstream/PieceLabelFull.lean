/- Mixed source step, N3 (families, full): new in this submission; uses the transfer's contracts
(`Residual/CollisionColumn.lean`) and Collet's definitions by import.

`piece_label_transfer_full`: the transfer of one label to the residual families of its piece, with
neither (S) nor (Col): the plain families (residual seeds `L' ∣ L`, parent `s.restrict J`) and the
collision families (parent `collParent s J D₀ D₁`, run at the plain node's MAIN radius
`collRadius`), grouped by the side products `D = (D₀, D₁)`. -/
import Submissions.arvi_mixed_step.Downstream.FamiliesFull

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
open QRH.MixedStep.Transfer QRH.MixedStep.Residual QRH.MixedStep.Collision
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- The selected weight vanishes unless the product is small: `N(∏ u) ≤ 2^|J| ∏ P`. -/
theorem sel_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (J : Finset ι)
    (K R : Ideal O) (u : J → Ideal O) (hhi : ∀ j ∈ J, s.hi j ≤ 2)
    (hw : selWeight s J K R u ≠ 0) :
    (Ideal.absNorm (selProduct J u) : ℝ) ≤ 2 ^ J.card * ∏ j ∈ J, s.P j := by
  unfold selProduct
  rw [map_prod, Nat.cast_prod]
  have h : ∀ j : J, (Ideal.absNorm (u j) : ℝ) ≤ 2 * s.P j.val := by
    intro j
    have hne := selWeight_slot_ne s J K R u hw j
    have hsup := s.support j.val hne
    have hP := s.P_pos j.val
    have h1 : (Ideal.absNorm (u j) : ℝ) / s.P j.val ≤ s.hi j.val := hsup.2
    have h2 := (div_le_iff₀ hP).mp h1
    nlinarith [hhi j.val j.property]
  calc ∏ j : J, (Ideal.absNorm (u j) : ℝ) ≤ ∏ j : J, (2 * s.P j.val) :=
        Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => h j)
    _ = 2 ^ J.card * ∏ j ∈ J, s.P j := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
        congr 1
        exact Finset.prod_coe_sort J s.P

/-- The additive form of `prod_liveBlock`. -/
theorem sum_liveBlock {α : Type*} [Fintype α] [DecidableEq α] {C : Ideal O} {s : Input α}
    (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val) (f : α → ℝ) :
    ∑ j ∈ liveBlock B J, f j.val = ∑ j ∈ J, f j := by
  unfold liveBlock
  rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem (fun j hj => hJ hj)]

/-- The norm factor of a pair of side products (`1` when a side vanishes). -/
def ndOf (D : Ideal O × Ideal O) : ℝ :=
  if D.1 ≠ 0 ∧ D.2 ≠ 0 then (Ideal.absNorm D.1 : ℝ) * Ideal.absNorm D.2 else 1

theorem one_le_absNorm_real {D : Ideal O} (h : D ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm D := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h)

theorem one_le_ndOf (D : Ideal O × Ideal O) : 1 ≤ ndOf D := by
  unfold ndOf
  split_ifs with h
  · have h1 := one_le_absNorm_real h.1
    have h2 := one_le_absNorm_real h.2
    nlinarith
  · exact le_refl 1

/-- The MAIN radius of the collision family with side products `D` at the plain node:
the shortened parent has volume `V / (W · N(D))`. -/
def collRadius (reflected : Bool) (K V W Z ξ σ reserve : ℝ) (lab : FirstSourceLabel)
    (D : Ideal O × Ideal O) : ℝ :=
  firstMainRadius reflected K (V / (W * ndOf D)) Z ξ σ reserve lab

theorem collRadius_pos (reflected : Bool) (K V W Z ξ σ reserve : ℝ) (lab : FirstSourceLabel)
    (hZ : 0 < Z) (D : Ideal O × Ideal O) : 0 < collRadius reflected K V W Z ξ σ reserve lab D :=
  first_main_radius_pos _ _ _ _ _ _ _ hZ _

theorem collRadius_le (reflected : Bool) (K V W Z ξ σ reserve : ℝ) (lab : FirstSourceLabel)
    (hZ : 1 < Z) (D : Ideal O × Ideal O) :
    collRadius reflected K V W Z ξ σ reserve lab D ≤
      firstMainRadius reflected K (V / W) Z ξ σ reserve lab := by
  unfold collRadius
  rw [← div_div]
  exact firstMainRadius_div_le _ _ _ _ _ _ _ _ _ hZ (one_le_ndOf D)

/-- The norm factor of the side products of an assignment is the norm of its product. -/
theorem ndOf_collSides {α : Type} [Fintype α] [DecidableEq α] (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (J : Finset α) (τ : HeckeFamily.Character) (t : ℝ)
    (q : Σ p : (Σ Q : Finset (liveIndices B.val), Q → Fin 2),
      {u // u ∈ selBox (child s C R B τ t) p.1}) :
    ndOf (collSides q) = (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ) := by
  have h0 := collH (child s C R B τ t) q.1.1 q.1.2 q.2 0
  have h1 := collH (child s C R B τ t) q.1.1 q.1.2 q.2 1
  unfold ndOf collSides
  simp only [h0, h1, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  rw [← sideProd_mul q.1.2 q.2.1, map_mul, Nat.cast_mul]

theorem selProduct_ne_zero {α : Type} [Fintype α] [DecidableEq α] (s : Input α) (J : Finset α)
    (u : J → Ideal O) (hu : u ∈ selBox s J) : selProduct J u ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ =>
    (s.prime j.val (u j) (Fintype.mem_piFinset.mp hu j)).ne_zero)

/-- **The transfer of one label to the residual families of its piece**, without (S) and (Col). -/
theorem piece_label_transfer_full (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
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
      ∃ seeds : Finset (Ideal O), ∃ seedsD : Ideal O × Ideal O → Finset (Ideal O),
        (∀ L' ∈ seeds, L' ∣ L) ∧ (∀ D, ∀ L' ∈ seedsD D, L' ∣ L) ∧
        correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
            (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
              (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) ≤
          K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
            ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
              correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
                (allocRestrict s C B J hJ)
                (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
                  (rayShift reflected c ξ))
                t (volume (s.restrict J))
                (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve
                  (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) +
          K * Z ^ (A * ε) *
            ∑ D ∈ (collAssign s C R B J
                (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t).image collSides,
              collWeight s C R B J
                  (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t D *
                ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D,
                  collE s C R L' P B J
                    (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t (volume s)
                    (collRadius reflected K₀ (volume s) (∏ j ∈ J, s.P j) Z ξ₀ (3 * (amp + δ))
                      reserve (firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)) D ξ := by
  obtain ⟨K₁, hK₁, hfull⟩ := transfer_full_column.{0, 0} ε hε N
  refine ⟨max K₁ 1, le_max_right _ _, ?_⟩
  intro α _ _ hcard s C R L P hp hPA hLsq B J hJ hhi w Z mesh hZ hP hw hmesh δ hδ ι₀ _ _ reflected
    s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c t amp reserve A hA hHA
  set τ := columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c with hτ
  set lab := firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c with hlab
  have hZ0 : 0 < Z := by linarith
  have hZA : 1 ≤ Z ^ (A * ε) := Real.one_le_rpow hZ.le (mul_nonneg hA hε.le)
  have hMJ : 1 ≤ ∏ j ∈ J, s.M j ^ 2 := by
    calc (1 : ℝ) = ∏ _j ∈ J, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ j ∈ J, s.M j ^ 2 :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ (s.M_ge_one j))
  have hM0 : 0 ≤ ∏ j ∈ J, s.M j ^ 2 := zero_le_one.trans hMJ
  have hHpos : 0 < firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab :=
    first_main_radius_pos _ _ _ _ _ _ _ hZ0 _
  rcases hδ with ⟨rfl, rfl⟩ | ⟨hδ0, hact⟩
  · -- node 0: no transfer, no collision pattern, the seed is kept
    refine ⟨{L}, fun _ => ∅, fun L' hL' => by rw [Finset.mem_singleton.mp hL'],
      fun D L' hL' => absurd hL' (Finset.notMem_empty L'), ?_⟩
    have hcollE : (collAssign s C R B ∅ τ t).image collSides = ∅ := by
      have h : liveBlock B (∅ : Finset α) = ∅ := by
        ext i
        simp [liveBlock]
      have h2 : collAssign s C R B ∅ τ t = ∅ := by
        unfold collAssign
        rw [h]
        simp [patterns]
      rw [h2]
      rfl
    rw [hcollE, Finset.sum_empty, mul_zero, add_zero]
    have hV : volume (s.restrict ∅) = volume s := by
      rw [volume_restrict, Finset.prod_empty, div_one]
    rw [hV, add_zero]
    rw [restrict_empty_energy s C R L P B _ t (volume s) _]
    simp only [Finset.sum_singleton]
    set E : RayCharacter → ℝ := fun ξ => correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L
      (fun _ => 1) P (allocRestrict s C B ∅ hJ)
      (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
      t (volume s) (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab) with hE
    have hEnn : ∀ ξ, 0 ≤ E ξ := fun ξ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hHpos
    have h1 : correctedChildGaussEnergy (s.restrict ∅) 1 1 1 1 C R L (fun _ => 1) P
        (allocRestrict s C B ∅ (Finset.empty_subset _)) τ t (volume s)
        (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab) = E 1 := by
      rw [hE]
      dsimp only
      rw [rayShift_one]
    rw [h1]
    have hfac : 1 ≤ max K₁ 1 * (∏ j ∈ (∅ : Finset α), s.M j ^ 2) * Z ^ (A * ε) := by
      rw [Finset.prod_empty, mul_one]
      exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) hZA
    calc E 1 ≤ ∑ ξ : RayCharacter, E ξ :=
          Finset.single_le_sum (fun ξ _ => hEnn ξ) (Finset.mem_univ _)
      _ = 1 * ∑ ξ : RayCharacter, E ξ := (one_mul _).symm
      _ ≤ max K₁ 1 * (∏ j ∈ (∅ : Finset α), s.M j ^ 2) * Z ^ (A * ε) * ∑ ξ : RayCharacter, E ξ :=
          mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg (fun ξ _ => hEnn ξ))
  · -- positive node
    have hJN : J.card ≤ N := (Finset.card_le_univ J).trans hcard
    have hrad := piece_radius reflected K₀ (volume s) Z ξ₀ amp δ reserve mesh lab hZ N J hJN w s.P hP hw
      hmesh hact
    have hV : volume (s.restrict J) = volume s / ∏ j ∈ J, s.P j := volume_restrict s J
    have hPJ1 : 1 ≤ ∏ j ∈ J, s.P j :=
      one_le_prod_real J s.P (fun j _ => by rw [hP j]; exact Real.one_le_rpow hZ.le (hw j))
    have hHH' : firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab ≤
        firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve lab := by
      have hrad2 : 2 * 16 ^ J.card * firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          lab * (∏ j ∈ J, s.P j) ^ 4 ≤
          firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve lab := by
        rw [hV]
        exact hrad
      refine le_trans ?_ hrad2
      have h1 : (1 : ℝ) ≤ 2 * 16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4 := by
        have h16 : (1 : ℝ) ≤ 16 ^ J.card := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 16)
        have h4 : (1 : ℝ) ≤ (∏ j ∈ J, s.P j) ^ 4 := one_le_pow₀ hPJ1
        nlinarith
      calc firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab
          = 1 * firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab := by ring
        _ ≤ (2 * 16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4) *
            firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab :=
          mul_le_mul_of_nonneg_right h1 hHpos.le
        _ = 2 * 16 ^ J.card * firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve
          lab * (∏ j ∈ J, s.P j) ^ 4 := by ring
    have hHZA : firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab ≤ Z ^ A :=
      hHH'.trans hHA
    -- the collision radii
    have hHcpos : ∀ D, 0 < collRadius reflected K₀ (volume s) (∏ j ∈ J, s.P j) Z ξ₀
        (3 * (amp + δ)) reserve lab D := fun D => collRadius_pos _ _ _ _ _ _ _ _ _ hZ0 D
    have hHcZ : ∀ D, collRadius reflected K₀ (volume s) (∏ j ∈ J, s.P j) Z ξ₀
        (3 * (amp + δ)) reserve lab D ≤ Z ^ A := by
      intro D
      refine (collRadius_le _ _ _ _ _ _ _ _ _ hZ D).trans ?_
      rw [← hV]
      exact hHA
    have hcoll : ∀ q ∈ collAssign s C R B J τ t, Supported (selProduct q.1.1 q.2.1) →
        selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1 ≠ 0 →
        2 * (2 * firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab /
              (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ)) *
            (∏ j ∈ restBlock (liveBlock B J) q.1.1, s.hi j.val.val * s.P j.val.val) ^ 4 ≤
          collRadius reflected K₀ (volume s) (∏ j ∈ J, s.P j) Z ξ₀ (3 * (amp + δ)) reserve lab
            (collSides q) := by
      intro q hq _ hwq
      obtain ⟨hpq, hxq⟩ := Finset.mem_sigma.mp hq
      have hpat := Finset.mem_sigma.mp hpq
      have hQsub : q.1.1 ⊆ liveBlock B J :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hpat.1).1
      have hQne : q.1.1.Nonempty := (Finset.mem_filter.mp hpat.1).2
      have hD0 := selProduct_ne_zero (child s C R B τ t) q.1.1 q.2.1 q.2.2
      have hND1 : (1 : ℝ) ≤ (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ) := one_le_absNorm_real hD0
      have hhiL : ∀ j ∈ q.1.1, (child s C R B τ t).hi j ≤ 2 := fun j hj =>
        (hhi j.val ((mem_liveBlock B J j).mp (hQsub hj))).2
      have hND := sel_norm_le (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1
        hhiL hwq
      have hcardL : (liveBlock B J).card ≤ N := by
        have h1 : (liveBlock B J).card ≤ Fintype.card (liveIndices B.val) := Finset.card_le_univ _
        have h2 : Fintype.card (liveIndices B.val) ≤ N := by
          rw [Fintype.card_coe]
          exact (Finset.card_le_univ _).trans hcard
        exact h1.trans h2
      have hact' : ∑ j ∈ liveBlock B J, (fun i : liveIndices B.val => w i.val) j ≤ δ - mesh := by
        rw [sum_liveBlock B J hJ w]
        exact hact
      have hrad' := coll_piece_radius reflected K₀ (volume s) Z ξ₀ amp δ reserve mesh lab hZ N
        (liveBlock B J) hcardL (fun i : liveIndices B.val => w i.val)
        (fun i : liveIndices B.val => s.P i.val) (fun i : liveIndices B.val => s.hi i.val)
        (fun j => hP j.val) (fun j => hw j.val)
        (fun j hj => hhi j.val ((mem_liveBlock B J j).mp hj)) hmesh hact' q.1.1 hQsub hQne
        (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ) hND1 hND
      have hprodR : ∏ j ∈ restBlock (liveBlock B J) q.1.1, s.hi j.val.val * s.P j.val.val =
          ∏ j ∈ liveBlock B J \ q.1.1, s.hi j.val * s.P j.val :=
        restBlock_prod_real (liveBlock B J) q.1.1 (fun i : liveIndices B.val => s.hi i.val * s.P i.val)
      have hprodJ : ∏ j ∈ liveBlock B J, s.P j.val = ∏ j ∈ J, s.P j := prod_liveBlock B J hJ s.P
      rw [hprodR]
      unfold collRadius
      rw [ndOf_collSides s C R B J τ t q, ← hprodJ]
      exact hrad'
    obtain ⟨seeds, seedsD, hseeds, hseedsD, hb⟩ := hfull hcard s C R L P hp hPA hLsq B J hJ hhi
      reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c t (volume s)
      (firstMainRadius reflected K₀ (volume s) Z ξ₀ (3 * amp) reserve lab)
      (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve lab) Z A
      (collRadius reflected K₀ (volume s) (∏ j ∈ J, s.P j) Z ξ₀ (3 * (amp + δ)) reserve lab)
      (volume_pos s) hHpos (by rw [hV]; exact hrad) hZ.le hA hHA hHZA hHcpos hHcZ hcoll
    refine ⟨seeds, seedsD, hseeds, hseedsD, ?_⟩
    rw [← hV] at hb
    refine hb.trans (add_le_add ?_ ?_)
    · have hsum : 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
          correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (volume (s.restrict J))
            (firstMainRadius reflected K₀ (volume (s.restrict J)) Z ξ₀ (3 * (amp + δ)) reserve lab) :=
        Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
          corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _)))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0) (Real.rpow_nonneg hZ0.le _)) hsum
    · have hsum : 0 ≤ ∑ D ∈ (collAssign s C R B J τ t).image collSides,
          collWeight s C R B J τ t D * ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D,
            collE s C R L' P B J τ t (volume s)
              (collRadius reflected K₀ (volume s) (∏ j ∈ J, s.P j) Z ξ₀ (3 * (amp + δ)) reserve lab) D ξ :=
        Finset.sum_nonneg (fun D _ => mul_nonneg
          (collWeight_nonneg s C R B J τ t (fun j hj => (hhi j hj).1) D)
          (Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
            collE_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ (hHcpos D)))))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hZ0.le _)) hsum

end
end QRH.MixedStep.Downstream

#print axioms QRH.MixedStep.Downstream.piece_label_transfer_full
#print axioms QRH.MixedStep.Downstream.sel_norm_le
#print axioms QRH.MixedStep.Downstream.collRadius_le
