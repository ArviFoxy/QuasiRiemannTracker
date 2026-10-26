/- Mixed source step, L3: new in this submission; uses the transfer's and the collision lemmas by
import.

**The full transfer of one label**, with neither (S) nor (Col). The child energy of a label is
bounded by its plain residual families (residual seeds `L' ∣ L`, `transfer_waist_split_supplier`)
and by its collision families, grouped by the pair of side products `D = (D₀, D₁)`:

* `collE`: the energy of the child of the shortened parent `collParent s J D₀ D₁` (`collEnergy`),
  with the character `childCharacter (twistChar τ (δ³)) ξ` (`δ` the primary generator of `D₀ D₁`),
  normalized by `T/(∏_J P · N(D₀) N(D₁))` (the parent's volume when `T = volume s`);
* `collWeight`: the selected weights `|w(u)|²/∏_Q P` of the assignments with these side
  products, times the remaining slot factors `∏_{J∖Q} hi·M²`. -/
import Submissions.arvi_mixed_step.Residual.CollisionParent
import Submissions.arvi_mixed_step.Residual.CollisionSplitSupplier

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
open RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.MixedStep.Transfer QRH.MixedStep.Collision
local notation "O" => ActualEisensteinCubic.O

theorem restBlock_prod_real {κ : Type*} [DecidableEq κ] (J Q : Finset κ) (f : κ → ℝ) :
    ∏ j ∈ restBlock J Q, f j.val = ∏ j ∈ J \ Q, f j := by
  unfold restBlock
  rw [Finset.prod_subtype_eq_prod_filter, Finset.sdiff_eq_filter]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The assignments of the collision patterns of the child of `B` on the block `J`. -/
abbrev collAssign (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C) (J : Finset α)
    (τ : HeckeFamily.Character) (t : ℝ) :
    Finset (Σ p : (Σ Q : Finset (liveIndices B.val), Q → Fin 2),
      {u // u ∈ selBox (child s C R B τ t) p.1}) :=
  (patterns (liveBlock B J)).sigma (fun p => (selBox (child s C R B τ t) p.1).attach)

/-- The side products of an assignment. -/
def collSides {κ : Type*} [Fintype κ] [DecidableEq κ] {s : Input κ}
    (q : Σ p : (Σ Q : Finset κ, Q → Fin 2), {u // u ∈ selBox s p.1}) : Ideal O × Ideal O :=
  (sideProd q.1.2 q.2.1 0, sideProd q.1.2 q.2.1 1)

/-- The weight of an assignment. -/
def collAssignWeight (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C) (J : Finset α)
    (τ : HeckeFamily.Character) (t : ℝ)
    (q : Σ p : (Σ Q : Finset (liveIndices B.val), Q → Fin 2),
      {u // u ∈ selBox (child s C R B τ t) p.1}) : ℝ :=
  if Supported (selProduct q.1.1 q.2.1) then
    ‖selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1‖ ^ 2 /
        (∏ j ∈ q.1.1, s.P j.val) *
      ∏ j ∈ restBlock (liveBlock B J) q.1.1, (s.hi j.val.val * s.M j.val.val ^ 2)
  else 0

/-- The weight of the collision families with side products `D`. -/
def collWeight (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C) (J : Finset α)
    (τ : HeckeFamily.Character) (t : ℝ) (D : Ideal O × Ideal O) : ℝ :=
  ∑ q ∈ (collAssign s C R B J τ t).filter (fun q => collSides q = D),
    collAssignWeight s C R B J τ t q

/-- The collision family energy with side products `D` (zero unless both are nonzero). -/
def collE (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O)) (B : actualAllocations s.pools C)
    (J : Finset α) (τ : HeckeFamily.Character) (t T : ℝ) (Hc : Ideal O × Ideal O → ℝ)
    (D : Ideal O × Ideal O) (ξ : RayCharacter) : ℝ :=
  if h : D.1 ≠ 0 ∧ D.2 ≠ 0 then
    collEnergy s C R L' P B J D.1 D.2 h.1 h.2
      (childCharacter (twistChar τ (primaryGenerator (D.1 * D.2) ^ 3)) ξ) t
      (T / ((∏ j ∈ J, s.P j) * ((Ideal.absNorm D.1 : ℝ) * Ideal.absNorm D.2))) (Hc D)
  else 0

theorem collE_nonneg (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (J : Finset α) (τ : HeckeFamily.Character) (t T : ℝ)
    (Hc : Ideal O × Ideal O → ℝ) (D : Ideal O × Ideal O) (ξ : RayCharacter) (hH : 0 < Hc D) :
    0 ≤ collE s C R L' P B J τ t T Hc D ξ := by
  unfold collE
  split_ifs
  · exact collEnergy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH
  · exact le_refl 0

/-- **One family residual at the shortened parent**, with the rescaling to `T/(∏_J P · N(D))`. -/
theorem famResidual_collE (s : Input α) (C R L' : Ideal O) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val)
    (τ : HeckeFamily.Character) (t T : ℝ) (hT : 0 < T) (Hc : Ideal O × Ideal O → ℝ)
    (Q : Finset (liveIndices B.val)) (hQ : Q ⊆ liveBlock B J) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox (child s C R B τ t) Q}) (ξ : RayCharacter) :
    famResidual (child s C R B τ t) (liveBlock B J) Q σ x (1 * B.val (Sum.inr 0))
        (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val) (R * C) L' (poolCorr P C) τ ξ t T
        (Hc (sideProd σ x.1 0, sideProd σ x.1 1)) =
      collE s C R L' P B J τ t T Hc (sideProd σ x.1 0, sideProd σ x.1 1) ξ *
        ((∏ j ∈ restBlock (liveBlock B J) Q, s.P j.val.val) /
          ((∏ j ∈ J, s.P j) *
            ((Ideal.absNorm (sideProd σ x.1 0) : ℝ) * Ideal.absNorm (sideProd σ x.1 1)))) := by
  have hn0 := absNorm_pos_of_ne (collH (child s C R B τ t) Q σ x 0)
  have hn1 := absNorm_pos_of_ne (collH (child s C R B τ t) Q σ x 1)
  have hPJ : 0 < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hPR : 0 < ∏ j ∈ restBlock (liveBlock B J) Q, s.P j.val.val :=
    Finset.prod_pos (fun j _ => s.P_pos _)
  have hT₁ : 0 < T / ∏ j ∈ restBlock (liveBlock B J) Q, s.P j.val.val := div_pos hT hPR
  have hT₂ : 0 < T / ((∏ j ∈ J, s.P j) *
      ((Ideal.absNorm (sideProd σ x.1 0) : ℝ) * Ideal.absNorm (sideProd σ x.1 1))) := by
    positivity
  unfold famResidual collE
  rw [dif_pos ⟨collH (child s C R B τ t) Q σ x 0, collH (child s C R B τ t) Q σ x 1⟩]
  rw [collResidual_eq s C R L' P B J hJ τ t Q hQ _ _ (collH (child s C R B τ t) Q σ x 0)
    (collH (child s C R B τ t) Q σ x 1) _ _ _]
  rw [← sideProd_mul σ x.1]
  dsimp only
  have hP1 : (∏ j ∈ restBlock (liveBlock B J) Q, (collInput (child s C R B τ t) Q σ x.1
      (collH (child s C R B τ t) Q σ x 0) (collH (child s C R B τ t) Q σ x 1)).P j) =
      ∏ j ∈ restBlock (liveBlock B J) Q, s.P j.val.val := rfl
  rw [hP1, collEnergy_rescale s C R L' P B J _ _ _ _ _ t _ _ _ hT₁ hT₂]
  congr 1
  field_simp

/-- **The full transfer of one label** (no (S), no (Col)): plain residual families with residual
seeds, and collision families grouped by their side products. -/
theorem transfer_full_label (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s → Squarefree L →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      (∀ j ∈ J, 0 ≤ s.hi j) →
    ∀ (τ : HeckeFamily.Character) (t T H H' : ℝ) (Hc : Ideal O × Ideal O → ℝ),
      0 < T → 0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ D, 0 < Hc D) →
      (∀ q ∈ collAssign s C R B J τ t, Supported (selProduct q.1.1 q.2.1) →
        selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1 ≠ 0 →
        2 * (2 * H / (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ)) *
          (∏ j ∈ restBlock (liveBlock B J) q.1.1, s.hi j.val.val * s.P j.val.val) ^ 4 ≤
            Hc (collSides q)) →
      ∃ seeds : Finset (Ideal O), ∃ seedsD : Ideal O × Ideal O → Finset (Ideal O),
        (∀ L' ∈ seeds, L' ∣ L) ∧ (∀ D, ∀ L' ∈ seedsD D, L' ∣ L) ∧
        correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H ≤
          K * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
            ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
              correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
                (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' +
          K * (max 1 (2 * H)) ^ ε *
            ∑ D ∈ (collAssign s C R B J τ t).image collSides,
              collWeight s C R B J τ t D * ((max 1 (Hc D)) ^ ε *
                ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ) := by
  obtain ⟨K₁, hK₁, hsplit⟩ := transfer_waist_split_supplier.{u} ε hε N
  obtain ⟨K₂, hK₂, hct⟩ := collision_transfer.{u} ε hε N
  refine ⟨max K₁ (2 * K₂), lt_max_of_lt_left hK₁, ?_⟩
  intro α _ _ hcard s C R L P hp hPA hLsq B J hJ hhi τ t T H H' Hc hT hH hH' hrad hHpos hHc
  obtain ⟨seeds, hseeds, hb⟩ := hsplit hcard s C R L P hp hPA hLsq B J hJ hhi τ t T H H' hH hH'
    hrad
  have hcard' : Fintype.card (liveIndices B.val) ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans hcard
  have hhi' : ∀ j ∈ liveBlock B J, 0 ≤ (child s C R B τ t).hi j :=
    fun j hj => hhi j.val ((mem_liveBlock B J j).mp hj)
  have hA₁ : 1 * B.val (Sum.inr 0) ≠ 0 := by rw [one_mul]; exact alloc_ne s C B _
  have hA₂ : 1 * B.val (Sum.inr 1) ≠ 0 := by rw [one_mul]; exact alloc_ne s C B _
  have hAR : 1 * B.val (Sum.inr 0) * (1 * B.val (Sum.inr 1)) ∣ R * C := by
    obtain ⟨_, hprod⟩ := Finset.mem_filter.mp B.property
    have h : B.val (Sum.inr 0) * B.val (Sum.inr 1) ∣ C := by
      have h0 : B.val (Sum.inr 0) * B.val (Sum.inr 1) ∣ ∏ i, B.val i := by
        rw [Fintype.prod_sum_type, Fin.prod_univ_two]
        exact dvd_mul_left _ _
      rwa [hprod] at h0
    rw [one_mul, one_mul]
    exact dvd_mul_of_dvd_right h R
  have hPAc : PoolAvoids P (child s C R B τ t) := fun Q hQ i I hI => hPA Q hQ i.val I hI
  have hF2 : ∀ (Q : Finset (liveIndices B.val)) (u : Q → Ideal O),
      u ∈ selBox (child s C R B τ t) Q → ∀ n : Ideal O,
        poolCorr P C (1 * (selProduct Q u ^ 2 * n)) = poolCorr P C (1 * n) := by
    intro Q u hu n
    rw [pow_two, mul_assoc, poolCorr_invariant _ P hp hPAc C Q u hu,
      poolCorr_invariant _ P hp hPAc C Q u hu]
  have hFf : ∀ p ∈ patterns (liveBlock B J), ∀ x : {u // u ∈ selBox (child s C R B τ t) p.1},
      ∀ v ∈ Fintype.piFinset (collInput (child s C R B τ t) p.1 p.2 x.1
        (collH (child s C R B τ t) p.1 p.2 x 0) (collH (child s C R B τ t) p.1 p.2 x 1)).pools,
        poolCorr P C (1 * finiteTupleProduct v) =
          poolCorr P C (1 * finiteTupleProduct (restPart (restBlock (liveBlock B J) p.1) v)) := by
    intro p _ x v hv
    have hv' := (mem_pools_iff _ v).mp (Fintype.mem_piFinset.mp hv)
    have hsel : selPart (restBlock (liveBlock B J) p.1) v ∈ selBox (collInput (child s C R B τ t)
        p.1 p.2 x.1 (collH (child s C R B τ t) p.1 p.2 x 0)
          (collH (child s C R B τ t) p.1 p.2 x 1)) (restBlock (liveBlock B J) p.1) :=
      Fintype.mem_piFinset.mpr (fun j => hv'.1 j.val)
    have hprod : finiteTupleProduct v =
        selProduct (restBlock (liveBlock B J) p.1) (selPart (restBlock (liveBlock B J) p.1) v) *
          finiteTupleProduct (restPart (restBlock (liveBlock B J) p.1) v) := by
      conv_lhs => rw [← join_parts (restBlock (liveBlock B J) p.1) v]
      exact finiteTupleProduct_join _ _ _
    rw [hprod]
    exact poolCorr_invariant _ P hp (fun Q hQ i I hI => hPA Q hQ i.val.val I hI) C _ _ hsel _
  have hHc' : ∀ p ∈ patterns (liveBlock B J), ∀ x : {u // u ∈ selBox (child s C R B τ t) p.1},
      Supported (selProduct p.1 x.1) →
      selWeight (child s C R B τ t) p.1 (1 * markedProduct B.val) (R * C) x.1 ≠ 0 →
      0 < Hc (sideProd p.2 x.1 0, sideProd p.2 x.1 1) ∧
        2 * (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ)) *
          (∏ j ∈ restBlock (liveBlock B J) p.1,
            (child s C R B τ t).hi j.val * (child s C R B τ t).P j.val) ^ 4 ≤
          Hc (sideProd p.2 x.1 0, sideProd p.2 x.1 1) :=
    fun p hp x hD hw => ⟨hHpos _,
      hHc ⟨p, x⟩ (Finset.mem_sigma.mpr ⟨hp, Finset.mem_attach _ _⟩) hD hw⟩
  obtain ⟨seedsQ, hseedsQ, hcol⟩ := hct hcard' (child s C R B τ t) (liveBlock B J)
    (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val) (R * C) L
    (poolCorr P C) τ t T H (fun p x => Hc (sideProd p.2 x.1 0, sideProd p.2 x.1 1)) hH hLsq hhi'
    hA₁ hA₂ hAR hF2 hFf hHc'
  -- the seeds of a class of side products
  set seedsD : Ideal O × Ideal O → Finset (Ideal O) := fun D =>
    ((collAssign s C R B J τ t).filter (fun q => collSides q = D)).biUnion
      (fun q => seedsQ q.1 q.2) with hseedsD
  refine ⟨seeds, seedsD, hseeds, ?_, ?_⟩
  · intro D L' hL'
    obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hL'
    exact hseedsQ q.1 q.2 L' hq
  set Φ : Ideal O × Ideal O → ℝ := fun D => (max 1 (Hc D)) ^ ε *
    ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ with hΦ
  -- one assignment
  have hterm : ∀ q ∈ collAssign s C R B J τ t,
      (if Supported (selProduct q.1.1 q.2.1) then
        ‖selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1‖ ^ 2 *
          (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ) *
          ((∏ j ∈ restBlock (liveBlock B J) q.1.1,
              (child s C R B τ t).hi j.val * (child s C R B τ t).M j.val ^ 2) *
            (max 1 (Hc (sideProd q.1.2 q.2.1 0, sideProd q.1.2 q.2.1 1))) ^ ε *
            ∑ ξ : RayCharacter, ∑ L' ∈ seedsQ q.1 q.2,
              famResidual (child s C R B τ t) (liveBlock B J) q.1.1 q.1.2 q.2
                (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val)
                (R * C) L' (poolCorr P C) τ ξ t T
                (Hc (sideProd q.1.2 q.2.1 0, sideProd q.1.2 q.2.1 1)))
      else 0) ≤ collAssignWeight s C R B J τ t q * Φ (collSides q) := by
    intro q hq
    obtain ⟨hp, _⟩ := Finset.mem_sigma.mp hq
    have hQ : q.1.1 ⊆ liveBlock B J :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).1
    have hHq := hHpos (collSides q)
    unfold collAssignWeight
    by_cases hD : Supported (selProduct q.1.1 q.2.1)
    · simp only [hD, ↓reduceIte]
      have hn0 := absNorm_pos_of_ne (collH (child s C R B τ t) q.1.1 q.1.2 q.2 0)
      have hn1 := absNorm_pos_of_ne (collH (child s C R B τ t) q.1.1 q.1.2 q.2 1)
      have hPQ : 0 < ∏ j ∈ q.1.1, s.P j.val := Finset.prod_pos (fun j _ => s.P_pos _)
      have hPR : 0 < ∏ j ∈ restBlock (liveBlock B J) q.1.1, s.P j.val.val :=
        Finset.prod_pos (fun j _ => s.P_pos _)
      have hPJ : ∏ j ∈ J, s.P j =
          (∏ j ∈ q.1.1, s.P j.val) * ∏ j ∈ restBlock (liveBlock B J) q.1.1, s.P j.val.val := by
        rw [← prod_liveBlock B J hJ s.P, restBlock_prod_real (liveBlock B J) q.1.1 (fun j => s.P j.val),
          ← Finset.prod_sdiff hQ, mul_comm]
      have hND : (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ) =
          (Ideal.absNorm (sideProd q.1.2 q.2.1 0) : ℝ) * Ideal.absNorm (sideProd q.1.2 q.2.1 1) := by
        rw [← sideProd_mul q.1.2 q.2.1, map_mul, Nat.cast_mul]
      have hfam : ∀ (ξ : RayCharacter) (L' : Ideal O),
          famResidual (child s C R B τ t) (liveBlock B J) q.1.1 q.1.2 q.2
            (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1 (1 * markedProduct B.val)
            (R * C) L' (poolCorr P C) τ ξ t T
            (Hc (sideProd q.1.2 q.2.1 0, sideProd q.1.2 q.2.1 1)) =
          collE s C R L' P B J τ t T Hc (collSides q) ξ *
            ((∏ j ∈ restBlock (liveBlock B J) q.1.1, s.P j.val.val) /
              ((∏ j ∈ J, s.P j) *
                ((Ideal.absNorm (sideProd q.1.2 q.2.1 0) : ℝ) *
                  Ideal.absNorm (sideProd q.1.2 q.2.1 1)))) :=
        fun ξ L' => famResidual_collE s C R L' P B J hJ τ t T hT Hc q.1.1 hQ q.1.2 q.2 ξ
      simp only [hfam]
      have hsub : ∀ ξ : RayCharacter, ∑ L' ∈ seedsQ q.1 q.2,
          collE s C R L' P B J τ t T Hc (collSides q) ξ ≤
            ∑ L' ∈ seedsD (collSides q), collE s C R L' P B J τ t T Hc (collSides q) ξ := by
        intro ξ
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro L' hL'
          exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, hL'⟩
        · intro L' _ _
          exact collE_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ hHq
      have hsum := Finset.sum_le_sum (fun ξ (_ : ξ ∈ (Finset.univ : Finset RayCharacter)) => hsub ξ)
      have hS : ∀ ρ : ℝ, (∑ ξ : RayCharacter, ∑ L' ∈ seedsQ q.1 q.2,
          collE s C R L' P B J τ t T Hc (collSides q) ξ * ρ) =
          (∑ ξ : RayCharacter, ∑ L' ∈ seedsQ q.1 q.2,
            collE s C R L' P B J τ t T Hc (collSides q) ξ) * ρ := by
        intro ρ
        simp only [Finset.sum_mul]
      rw [hS]
      have hw0 : 0 ≤ ‖selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1‖ ^ 2 /
          (∏ j ∈ q.1.1, s.P j.val) *
            ∏ j ∈ restBlock (liveBlock B J) q.1.1, (s.hi j.val.val * s.M j.val.val ^ 2) := by
        apply mul_nonneg (div_nonneg (sq_nonneg _) hPQ.le)
        exact Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j.val.val
          ((mem_liveBlock B J _).mp (Finset.mem_subtype.mp hj)))
          (sq_nonneg _))
      have key : ‖selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1‖ ^ 2 *
          (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ) *
          ((∏ j ∈ restBlock (liveBlock B J) q.1.1,
              (child s C R B τ t).hi j.val * (child s C R B τ t).M j.val ^ 2) *
            (max 1 (Hc (sideProd q.1.2 q.2.1 0, sideProd q.1.2 q.2.1 1))) ^ ε *
            ((∑ ξ : RayCharacter, ∑ L' ∈ seedsQ q.1 q.2,
              collE s C R L' P B J τ t T Hc (collSides q) ξ) *
            ((∏ j ∈ restBlock (liveBlock B J) q.1.1, s.P j.val.val) /
              ((∏ j ∈ J, s.P j) *
                ((Ideal.absNorm (sideProd q.1.2 q.2.1 0) : ℝ) *
                  Ideal.absNorm (sideProd q.1.2 q.2.1 1)))))) =
          ‖selWeight (child s C R B τ t) q.1.1 (1 * markedProduct B.val) (R * C) q.2.1‖ ^ 2 /
            (∏ j ∈ q.1.1, s.P j.val) *
            (∏ j ∈ restBlock (liveBlock B J) q.1.1, (s.hi j.val.val * s.M j.val.val ^ 2)) *
            ((max 1 (Hc (collSides q))) ^ ε *
              ∑ ξ : RayCharacter, ∑ L' ∈ seedsQ q.1 q.2,
                collE s C R L' P B J τ t T Hc (collSides q) ξ) := by
        have hprodR : ∏ j ∈ restBlock (liveBlock B J) q.1.1,
            (child s C R B τ t).hi j.val * (child s C R B τ t).M j.val ^ 2 =
            ∏ j ∈ restBlock (liveBlock B J) q.1.1, (s.hi j.val.val * s.M j.val.val ^ 2) := rfl
        rw [hND, hPJ, hprodR]
        unfold collSides
        field_simp
      rw [key]
      apply mul_le_mul_of_nonneg_left _ hw0
      exact mul_le_mul_of_nonneg_left hsum
        (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    · simp only [hD, ↓reduceIte, zero_mul, le_refl]
  -- the collision part
  have hcoll : collisionEnergy s C R L P B J τ t T H ≤ K₂ * (max 1 (2 * H)) ^ ε *
      ∑ D ∈ (collAssign s C R B J τ t).image collSides, collWeight s C R B J τ t D * Φ D := by
    refine le_trans hcol ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK₂.le
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
    rw [Finset.sum_sigma']
    calc _ ≤ ∑ q ∈ collAssign s C R B J τ t, collAssignWeight s C R B J τ t q * Φ (collSides q) :=
          Finset.sum_le_sum hterm
      _ = _ := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (fun q hq => Finset.mem_image_of_mem collSides hq)]
        apply Finset.sum_congr rfl
        intro D _
        unfold collWeight
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]
  -- nonnegativity
  have hplain : 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
      correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
        (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' :=
    Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
      corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH'))
  have hPiNN : 0 ≤ (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε :=
    mul_nonneg (Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j hj) (sq_nonneg _)))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hcol0 : 0 ≤ ∑ D ∈ (collAssign s C R B J τ t).image collSides,
      collWeight s C R B J τ t D * Φ D := by
    apply Finset.sum_nonneg
    intro D hD
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hD
    apply mul_nonneg
    · unfold collWeight
      apply Finset.sum_nonneg
      intro q' hq'
      unfold collAssignWeight
      split_ifs
      · have hQ' : q'.1.1 ⊆ liveBlock B J := Finset.mem_powerset.mp (Finset.mem_filter.mp
          (Finset.mem_sigma.mp (Finset.mem_sigma.mp (Finset.mem_filter.mp hq').1).1).1).1
        apply mul_nonneg (div_nonneg (sq_nonneg _)
          (Finset.prod_pos (fun j _ => s.P_pos _)).le)
        exact Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j.val.val
          ((mem_liveBlock B J _).mp (Finset.mem_subtype.mp hj)))
          (sq_nonneg _))
      · exact le_refl 0
    · apply mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      exact Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
        collE_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ (hHpos _)))
  have hM : 0 ≤ (max 1 (2 * H)) ^ ε := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  calc correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H
      ≤ K₁ * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
              (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' +
        2 * collisionEnergy s C R L P B J τ t T H := hb
    _ ≤ max K₁ (2 * K₂) * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
              (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' +
        max K₁ (2 * K₂) * (max 1 (2 * H)) ^ ε *
          ∑ D ∈ (collAssign s C R B J τ t).image collSides, collWeight s C R B J τ t D * Φ D := by
        apply add_le_add
        · rw [mul_assoc K₁, mul_assoc (max K₁ (2 * K₂))]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hPiNN) hplain
        · calc 2 * collisionEnergy s C R L P B J τ t T H
              ≤ 2 * (K₂ * (max 1 (2 * H)) ^ ε *
                ∑ D ∈ (collAssign s C R B J τ t).image collSides,
                  collWeight s C R B J τ t D * Φ D) := by linarith
            _ = (2 * K₂) * (max 1 (2 * H)) ^ ε *
                ∑ D ∈ (collAssign s C R B J τ t).image collSides,
                  collWeight s C R B J τ t D * Φ D := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
                hcol0

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.transfer_full_label
#print axioms QRH.MixedStep.Residual.famResidual_collE
