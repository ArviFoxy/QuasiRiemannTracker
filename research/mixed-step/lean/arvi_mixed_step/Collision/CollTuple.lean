/- Mixed source step, L3 (collisions): new in this submission; uses Collet's and the
transfer's definitions by import.

Collision tuples. For a block `Q` of slots, sides `σ : Q → Fin 2` and colliding primes
`u : Q → Ideal O`, put `D_k = ∏_{σ j = k} u_j` and `D = D₀ D₁ = ∏ u`. The collision
tuple `collTuple Q σ u a` has the slots `u` on `Q` and plains `D_k · a_k`; its column
is `D² · n_a`. The family input `collInput` is `(s.restrict Q).shortenPlains D₀ D₁`.

`coll_factor`: on the collision tuples the tuple coefficient factorizes exactly,

  tc_s(collTuple u a) = selWeight(u) · tc_{collInput}(a),

with the family modifier `markedSourceModifier (A₁·D₀) (A₂·D₁) Dc K F`, coprimality
ideal `R·D` and the same seed `L`, provided `L ⊥ D` and `F(Dc·D²n) = F(Dc·n)`.
The coprimality `[n_a ⊥ D]` of the family replaces the marked part of the original
squarefree projector; on the plain part it is supplied by the original plain
squarefree projector. -/
import Submissions.arvi_mixed_step.Transfer.NoCollision
import Submissions.arvi_mixed_step.Residual.Shorten

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Collision
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentRectangle
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source.High QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The colliding primes on side `k`. -/
def sideProd {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O) (k : Fin 2) : Ideal O :=
  ∏ j ∈ Finset.univ.filter (fun j => σ j = k), u j

theorem fin2_ne_zero_iff (x : Fin 2) : ¬x = 0 ↔ x = 1 := by
  fin_cases x <;> simp

theorem sideProd_mul {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O) :
    sideProd σ u 0 * sideProd σ u 1 = selProduct Q u := by
  unfold sideProd selProduct
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => σ j = 0)]
  congr 1
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (fin2_ne_zero_iff (σ j)).symm

theorem sideProd_ne_zero {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O)
    (hu : ∀ j, u j ≠ 0) (k : Fin 2) : sideProd σ u k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => hu j)

theorem sideProd_dvd {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O) (k : Fin 2) :
    sideProd σ u k ∣ selProduct Q u := by
  rw [← sideProd_mul σ u]
  fin_cases k
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

/-- Plains multiplied by the colliding primes of their side. -/
def liftPlains {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O) (a : Tuple {i // i ∉ Q}) :
    Tuple {i // i ∉ Q} :=
  Sum.elim (fun i => a (Sum.inl i)) (fun k => sideProd σ u k * a (Sum.inr k))

/-- The collision tuple. -/
def collTuple (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O) (a : Tuple {i // i ∉ Q}) :
    Tuple κ :=
  joinTuple Q u (liftPlains σ u a)

theorem collTuple_inr (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O) (a : Tuple {i // i ∉ Q})
    (k : Fin 2) : collTuple Q σ u a (Sum.inr k) = sideProd σ u k * a (Sum.inr k) := rfl

theorem collTuple_sel (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O) (a : Tuple {i // i ∉ Q}) :
    selPart Q (collTuple Q σ u a) = u := selPart_join Q u _

theorem markedProduct_liftPlains {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O)
    (a : Tuple {i // i ∉ Q}) : markedProduct (liftPlains σ u a) = markedProduct a := rfl

theorem collTuple_marked (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (a : Tuple {i // i ∉ Q}) :
    markedProduct (collTuple Q σ u a) = selProduct Q u * markedProduct a := by
  unfold collTuple
  rw [markedProduct_join, markedProduct_liftPlains]

theorem liftPlains_product {Q : Finset κ} (σ : Q → Fin 2) (u : Q → Ideal O)
    (a : Tuple {i // i ∉ Q}) :
    finiteTupleProduct (liftPlains σ u a) = selProduct Q u * finiteTupleProduct a := by
  rw [finiteTupleProduct_split, finiteTupleProduct_split a, markedProduct_liftPlains,
    ← sideProd_mul σ u]
  change markedProduct a * ((sideProd σ u 0 * a (Sum.inr 0)) * (sideProd σ u 1 * a (Sum.inr 1))) = _
  ring

theorem collTuple_product (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (a : Tuple {i // i ∉ Q}) :
    finiteTupleProduct (collTuple Q σ u a) = selProduct Q u ^ 2 * finiteTupleProduct a := by
  unfold collTuple
  rw [finiteTupleProduct_join, liftPlains_product]
  ring

/-- The family input of a collision pattern. -/
abbrev collInput (s : Input κ) (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (h₀ : sideProd σ u 0 ≠ 0) (h₁ : sideProd σ u 1 ≠ 0) : Input {i // i ∉ Q} :=
  (s.restrict Q).shortenPlains (sideProd σ u 0) (sideProd σ u 1) h₀ h₁

theorem collTuple_mem (s : Input κ) (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (h₀ : sideProd σ u 0 ≠ 0) (h₁ : sideProd σ u 1 ≠ 0) (hu : u ∈ selBox s Q)
    (a : Tuple {i // i ∉ Q}) (ha : a ∈ Fintype.piFinset (collInput s Q σ u h₀ h₁).pools) :
    collTuple Q σ u a ∈ Fintype.piFinset s.pools := by
  have ha' := (mem_pools_iff _ a).mp (Fintype.mem_piFinset.mp ha)
  apply Fintype.mem_piFinset.mpr
  apply (mem_pools_iff s _).mpr
  have hu' := Fintype.mem_piFinset.mp hu
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases h : i ∈ Q
    · unfold collTuple
      rw [joinTuple_inl_mem Q _ _ i h]
      exact hu' ⟨i, h⟩
    · unfold collTuple
      rw [joinTuple_inl_not_mem Q _ _ i h]
      exact ha'.1 ⟨i, h⟩
  · rw [collTuple_inr]
    exact (mem_shortenPlains_plain₁ (s.restrict Q) _ _ h₀ h₁ _).mp ha'.2.1
  · rw [collTuple_inr]
    exact (mem_shortenPlains_plain₂ (s.restrict Q) _ _ h₀ h₁ _).mp ha'.2.2

/-- Squarefree plains with a factor `D₀·D₁` are coprime to `D`. -/
theorem plain_coprime (A₁ A₂ D₀ D₁ a₀ a₁ : Ideal O)
    (h : Squarefree (A₁ * (D₀ * a₀) * A₂ * (D₁ * a₁))) : IsCoprime (D₀ * D₁) (a₀ * a₁) := by
  have he : A₁ * (D₀ * a₀) * A₂ * (D₁ * a₁) = ((D₀ * D₁) * (a₀ * a₁)) * (A₁ * A₂) := by ring
  rw [he] at h
  exact isCoprime_of_isRelPrime (squarefree_mul_iff.mp h.of_mul_left).1

/-- **Exact factorization on collision tuples.** -/
theorem coll_factor (s : Input κ) (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (h₀ : sideProd σ u 0 ≠ 0) (h₁ : sideProd σ u 1 ≠ 0) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (a : Tuple {i // i ∉ Q}) (hL : IsCoprime L (selProduct Q u))
    (hF : F (Dc * (selProduct Q u ^ 2 * finiteTupleProduct a)) = F (Dc * finiteTupleProduct a)) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (collTuple Q σ u a) =
      selWeight s Q K R u *
        CoupledFirst.tupleCoefficient (collInput s Q σ u h₀ h₁)
          (markedSourceModifier (A₁ * sideProd σ u 0) (A₂ * sideProd σ u 1) Dc K F)
          (R * selProduct Q u) L a := by
  set D := selProduct Q u with hD
  set D₀ := sideProd σ u 0 with hD₀
  set D₁ := sideProd σ u 1 with hD₁
  have hDD : D₀ * D₁ = D := sideProd_mul σ u
  -- the marked projector
  have hmark : squarefreeIndicator (K * markedProduct (collTuple Q σ u a)) =
      squarefreeIndicator D * coprimalityIndicator D K * coprimalityIndicator D (markedProduct a) *
        squarefreeIndicator (K * markedProduct a) := by
    rw [collTuple_marked, show K * (D * markedProduct a) = D * (K * markedProduct a) by ring,
      squarefreeIndicator_mul]
    have hc : coprimalityIndicator D (K * markedProduct a) =
        coprimalityIndicator D K * coprimalityIndicator D (markedProduct a) := by
      unfold coprimalityIndicator
      by_cases h1 : IsRelPrime D K <;> by_cases h2 : IsRelPrime D (markedProduct a) <;>
        simp [IsRelPrime.mul_right_iff, h1, h2]
    rw [hc]
    ring
  -- the plain projectors
  have hhole : ordinaryHoleIndicator (A₁ * collTuple Q σ u a (Sum.inr 0))
      (A₂ * collTuple Q σ u a (Sum.inr 1)) =
      ordinaryHoleIndicator (A₁ * D₀ * a (Sum.inr 0)) (A₂ * D₁ * a (Sum.inr 1)) := by
    rw [collTuple_inr, collTuple_inr, ← mul_assoc, ← mul_assoc]
  have hsqp : A₁ * collTuple Q σ u a (Sum.inr 0) * A₂ * collTuple Q σ u a (Sum.inr 1) =
      A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1) := by
    rw [collTuple_inr, collTuple_inr]
    ring
  -- the column
  have hcol : finiteTupleProduct (collTuple Q σ u a) = D ^ 2 * finiteTupleProduct a :=
    collTuple_product Q σ u a
  -- the slot amplitudes
  have hslots : (∏ i, s.ν i (collTuple Q σ u a (Sum.inl i)) *
      s.W i ((Ideal.absNorm (collTuple Q σ u a (Sum.inl i)) : ℝ) / s.P i)) =
      slotAmplitude s Q u * ∏ i : {i // i ∉ Q}, s.ν i.val (a (Sum.inl i)) *
        s.W i.val ((Ideal.absNorm (a (Sum.inl i)) : ℝ) / s.P i.val) :=
    join_marked_prod Q u (liftPlains σ u a)
      (fun j I => s.ν j I * s.W j ((Ideal.absNorm I : ℝ) / s.P j))
  -- coprimality to R
  have hR : (if IsCoprime (D ^ 2 * finiteTupleProduct a) R then (1:ℂ) else 0) =
      (if IsCoprime D R then 1 else 0) * (if IsCoprime (finiteTupleProduct a) R then 1 else 0) := by
    by_cases h1 : IsCoprime D R <;> by_cases h2 : IsCoprime (finiteTupleProduct a) R <;>
      simp [IsCoprime.mul_left_iff, IsCoprime.pow_left_iff (by norm_num : 0 < 2), h1, h2]
  -- the seed
  have hseed : (if L ∣ D ^ 2 * finiteTupleProduct a then (1:ℂ) else 0) =
      (if L ∣ finiteTupleProduct a then 1 else 0) := by
    have hh : L ∣ D ^ 2 * finiteTupleProduct a ↔ L ∣ finiteTupleProduct a :=
      ⟨fun h => (hL.pow_right (n := 2)).dvd_of_dvd_mul_left h, fun h => h.trans (dvd_mul_left _ _)⟩
    simp only [hh]
  -- the rectangle
  have hrect : idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (1 * collTuple Q σ u a (Sum.inr 0))
      (1 * collTuple Q σ u a (Sum.inr 1)) =
      idealRectangle s.W₁ s.W₂ (s.X₁ / Ideal.absNorm D₀) (s.X₂ / Ideal.absNorm D₁)
        (s.Y₁ / Ideal.absNorm D₀) (s.Y₂ / Ideal.absNorm D₁) (1 * a (Sum.inr 0)) (1 * a (Sum.inr 1)) := by
    rw [rectangle_shorten, collTuple_inr, collTuple_inr, one_mul, one_mul, one_mul, one_mul]
  -- the family coprimality
  have hRD : (if IsCoprime (finiteTupleProduct a) (R * D) then (1:ℂ) else 0) =
      (if IsCoprime (finiteTupleProduct a) R then 1 else 0) *
        (if IsCoprime (finiteTupleProduct a) D then 1 else 0) := by
    by_cases h1 : IsCoprime (finiteTupleProduct a) R <;>
      by_cases h2 : IsCoprime (finiteTupleProduct a) D <;>
      simp [IsCoprime.mul_right_iff, h1, h2]
  -- left side unfolded
  unfold CoupledFirst.tupleCoefficient markedSourceModifier sourceModifier coupledFactor
    profileCoefficient selWeight
  rw [hmark, hhole, hsqp, hcol, hF, hslots, hR, hseed, hrect, hRD]
  -- the residual input data are those of `s`
  change _ = _ * (squarefreeIndicator (K * markedProduct a) *
      (ordinaryHoleIndicator (A₁ * D₀ * a (Sum.inr 0)) (A₂ * D₁ * a (Sum.inr 1)) *
        (squarefreeIndicator (A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1)) *
          F (Dc * finiteTupleProduct a))) *
      ((∏ i : {i // i ∉ Q}, s.ν i.val (a (Sum.inl i)) *
          s.W i.val ((Ideal.absNorm (a (Sum.inl i)) : ℝ) / s.P i.val)) *
        ((if IsCoprime (finiteTupleProduct a) R then (1:ℂ) else 0) *
          (if IsCoprime (finiteTupleProduct a) D then 1 else 0)) *
        idealRectangle s.W₁ s.W₂ (s.X₁ / Ideal.absNorm D₀) (s.X₂ / Ideal.absNorm D₁)
          (s.Y₁ / Ideal.absNorm D₀) (s.Y₂ / Ideal.absNorm D₁) (1 * a (Sum.inr 0))
          (1 * a (Sum.inr 1)) *
        (if L ∣ finiteTupleProduct a then 1 else 0)))
  -- remaining: the marked coprimality equals `[n_a ⊥ D]` on the plain support
  by_cases hsq : Squarefree (A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1))
  · have hpc : IsCoprime D (a (Sum.inr 0) * a (Sum.inr 1)) := by
      rw [← hDD]
      apply plain_coprime A₁ A₂ D₀ D₁ (a (Sum.inr 0)) (a (Sum.inr 1))
      have he : A₁ * (D₀ * a (Sum.inr 0)) * A₂ * (D₁ * a (Sum.inr 1)) =
          A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1) := by ring
      rw [he]
      exact hsq
    have hiff : coprimalityIndicator D (markedProduct a) =
        (if IsCoprime (finiteTupleProduct a) D then (1:ℂ) else 0) := by
      unfold coprimalityIndicator
      rw [finiteTupleProduct_split a]
      by_cases hm : IsCoprime (markedProduct a) D
      · have hr : IsRelPrime D (markedProduct a) := hm.symm.isRelPrime
        have hc : IsCoprime (markedProduct a * (a (Sum.inr 0) * a (Sum.inr 1))) D :=
          IsCoprime.mul_left hm hpc.symm
        simp only [hr, hc, ↓reduceIte]
      · have hr : ¬IsRelPrime D (markedProduct a) :=
          fun h => hm (isCoprime_of_isRelPrime h).symm
        have hc : ¬IsCoprime (markedProduct a * (a (Sum.inr 0) * a (Sum.inr 1))) D :=
          fun h => hm (IsCoprime.of_mul_left_left h)
        simp only [hr, hc, ↓reduceIte]
    rw [hiff]
    ring
  · have hz : squarefreeIndicator (A₁ * D₀ * a (Sum.inr 0) * (A₂ * D₁) * a (Sum.inr 1)) = 0 := by
      simp [squarefreeIndicator, hsq]
    rw [hz]
    ring

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.coll_factor
