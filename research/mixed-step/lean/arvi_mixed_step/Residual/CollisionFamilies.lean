/- Mixed source step, L3: new in this submission; uses the collision lemmas (Collision/) and
the transfer's lemmas (Transfer/, Residual/) by import.

The collision part of a source is bounded by its collision families.

* `coll_factor_supplier`, `coll_factor_mask_supplier`: `coll_factor` and `coll_factor_mask`
  for a squarefree seed `L` that may share primes with the colliding primes; the family then
  carries the residual seed `residualSeed Q L u = L / gcd(L, D_u)`. -/
import Submissions.arvi_mixed_step.Residual.CollisionSplitSupplier
import Submissions.arvi_mixed_step.Residual.CollisionWeight
import Submissions.arvi_mixed_step.Collision.CollPattern
import Submissions.arvi_mixed_step.Collision.CollRow
import Submissions.arvi_mixed_step.Collision.CollTwist

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

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

/-- `coll_factor` with a seed that may share primes with the colliding primes. -/
theorem coll_factor_supplier (s : Input κ) (Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (h₀ : sideProd σ u 0 ≠ 0) (h₁ : sideProd σ u 1 ≠ 0) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (a : Tuple {i // i ∉ Q}) (hLsq : Squarefree L) (hu : u ∈ selBox s Q)
    (hF : F (Dc * (selProduct Q u ^ 2 * finiteTupleProduct a)) = F (Dc * finiteTupleProduct a)) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (collTuple Q σ u a) =
      selWeight s Q K R u *
        CoupledFirst.tupleCoefficient (collInput s Q σ u h₀ h₁)
          (markedSourceModifier (A₁ * sideProd σ u 0) (A₂ * sideProd σ u 1) Dc K F)
          (R * selProduct Q u) (residualSeed Q L u) a := by
  rw [tupleCoefficient_seed s _ R L,
    coll_factor s Q σ u h₀ h₁ A₁ A₂ Dc K R 1 F a isCoprime_one_left hF, collTuple_product,
    tupleCoefficient_seed (collInput s Q σ u h₀ h₁) _ _ (residualSeed Q L u)]
  by_cases hw : selWeight s Q K R u = 0
  · rw [hw]
    ring
  · have hinj := sel_injective_of_weight s Q K R u hu hw
    have hiff := seed_iff L (residualSeed Q L u) (supplied Q L u) (selProduct Q u ^ 2)
      (finiteTupleProduct a) ((supplied_dvd_sel Q L u).trans (dvd_pow_self _ two_ne_zero))
      (residualSeed_spec Q L u (supplied_dvd_seed s Q L u hu hinj))
      ((residualSeed_coprime s Q L hLsq u hu hinj).pow_right)
    simp only [hiff]
    ring

/-- `coll_factor_mask` with a seed that may share primes with the colliding primes. -/
theorem coll_factor_mask_supplier (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (u : Q → Ideal O)
    (h₀ : sideProd σ u 0 ≠ 0) (h₁ : sideProd σ u 1 ≠ 0) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (a : Tuple {i // i ∉ Q}) (hLsq : Squarefree L) (hu : u ∈ selBox s Q)
    (hF : F (Dc * (selProduct Q u ^ 2 * finiteTupleProduct a)) = F (Dc * finiteTupleProduct a)) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (collTuple Q σ u a) *
        patMask J Q σ (collTuple Q σ u a) =
      selWeight s Q K R u *
        noColPart (restBlock J Q)
          (CoupledFirst.tupleCoefficient (collInput s Q σ u h₀ h₁)
            (markedSourceModifier (A₁ * sideProd σ u 0) (A₂ * sideProd σ u 1) Dc K F)
            (R * selProduct Q u) (residualSeed Q L u)) a := by
  have h1 := coll_factor_mask s J Q σ u h₀ h₁ A₁ A₂ Dc K R 1 F a isCoprime_one_left hF
  rw [tupleCoefficient_seed s _ R L, collTuple_product, mul_right_comm, h1]
  unfold noColPart
  rw [tupleCoefficient_seed (collInput s Q σ u h₀ h₁) _ _ (residualSeed Q L u)]
  by_cases hw : selWeight s Q K R u = 0
  · rw [hw]
    ring
  · have hinj := sel_injective_of_weight s Q K R u hu hw
    have hiff := seed_iff L (residualSeed Q L u) (supplied Q L u) (selProduct Q u ^ 2)
      (finiteTupleProduct a) ((supplied_dvd_sel Q L u).trans (dvd_pow_self _ two_ne_zero))
      (residualSeed_spec Q L u (supplied_dvd_seed s Q L u hu hinj))
      ((residualSeed_coprime s Q L hLsq u hu hinj).pow_right)
    simp only [hiff]
    ring

/-! ### The collision part as a sum of family polynomials -/

open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentLiveDomain RayFourExpansion
open CenteredMomentChildRows CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstColumns CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open Candidate.FourthPower

/-- The quotient of `z` by `d` when `d ∣ z` (zero otherwise). -/
def quotOf (d z : O) : O := if h : d ∣ z then Classical.choose h else 0

theorem quotOf_spec {d z : O} (h : d ∣ z) : z = d * quotOf d z := by
  unfold quotOf
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

/-- The family polynomial of a collision assignment `x` of the pattern `(Q, σ)`: the
no-collision part (on `J \ Q`) of the family coefficient, with the row twist `δ³`
(`δ` the primary generator of the colliding product). -/
def famPoly (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ)
    (z : O) : ℂ :=
  gaussPolynomial Finset.univ
    (sourceGenerator (finiteColumns (collBox s Q σ x)))
    (sourceGenerator_supported (finiteColumns (collBox s Q σ x)))
    (fun I : supportedColumns (finiteColumns (collBox s Q σ x)) =>
      finiteColumnCoefficient (collBox s Q σ x)
        (noColPart (restBlock J Q)
          (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
            (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
            (R * selProduct Q x.1) (residualSeed Q L x.1))) I *
        ((Real.sqrt T : ℂ)⁻¹ *
          rowWeight τ fixedBadMask 1 (primaryGenerator (selProduct Q x.1) ^ 3) t I)) z

/-- The row factor of a collision assignment at the frequency `z`. -/
def collRowFactor (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ)
    (z : O) : ℂ :=
  if primaryGenerator (selProduct Q x.1) ∣ z then
    primaryGaussRow (selProduct Q x.1 ^ 2) z *
      famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T (quotOf (primaryGenerator (selProduct Q x.1)) z)
  else 0

/-- One collision assignment: the sum over its tuples is the square row times the family
polynomial at `z/δ`. -/
theorem coll_assignment_identity (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox s Q}) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) (hw : selWeight s Q K R x.1 ≠ 0) (z : O) :
    ∑ a ∈ collBox s Q σ x,
        noColPart (restBlock J Q)
          (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
            (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
            (R * selProduct Q x.1) (residualSeed Q L x.1)) a *
          (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t
              (selProduct Q x.1 ^ 2 * finiteTupleProduct a)) *
            primaryGaussRow (selProduct Q x.1 ^ 2 * finiteTupleProduct a) z) =
      rowWeight τ fixedBadMask 1 1 t (selProduct Q x.1 ^ 2) *
        collRowFactor s J Q σ x A₁ A₂ Dc K R L F τ t T z := by
  unfold collRowFactor famPoly
  set D := selProduct Q x.1 with hD
  set δ := primaryGenerator D with hδ
  set nc := noColPart (restBlock J Q)
    (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
      (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
      (R * D) (residualSeed Q L x.1)) with hnc
  have hu : ∀ j, Prime (x.1 j) := fun j => s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)
  have hinj := sel_injective_of_weight s Q K R x.1 x.2 hw
  -- on the support of the family coefficient the column is coprime to `D`
  have hcop : ∀ a, nc a ≠ 0 → IsCoprime D (finiteTupleProduct a) := by
    intro a ha
    have hne : CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
        (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
        (R * D) (residualSeed Q L x.1) a ≠ 0 := by
      intro h0
      apply ha
      simp only [hnc, noColPart, h0, zero_mul]
    have h := profile_coprime _ _ _ _ a hne
    exact (IsCoprime.of_mul_right_right h).symm
  by_cases hdz : δ ∣ z
  · simp only [hdz, ↓reduceIte]
    set z' := quotOf δ z with hz'
    have hzz : z = δ * z' := quotOf_spec hdz
    rw [gauss_tuple_sum _ _ (fun I => (Real.sqrt T : ℂ)⁻¹ *
      rowWeight τ fixedBadMask 1 (δ ^ 3) t I) z', Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : nc a = 0
    · rw [ha]
      ring
    · have hc := hcop a ha
      rw [hzz, coll_row_twist x.1 _ hc z', map_mul, rowWeight_twist_eq τ (δ ^ 3) t (finiteTupleProduct a)]
      ring
  · simp only [hdz, ↓reduceIte, mul_zero]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : nc a = 0
    · rw [ha, zero_mul]
    · rw [coll_row_zero x.1 hu hinj _ (hcop a ha) z hdz]
      ring

/-- **The collision polynomial as a sum over patterns and assignments.** -/
theorem coll_poly_identity (s : Input κ) (J : Finset κ) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (hLsq : Squarefree L)
    (hF : ∀ (Q : Finset κ) (u : Q → Ideal O), u ∈ selBox s Q → ∀ n : Ideal O,
      F (Dc * (selProduct Q u ^ 2 * n)) = F (Dc * n))
    (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
          finiteColumnCoefficient (Fintype.piFinset s.pools)
            (colPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) z =
      ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
        selWeight s p.1 K R x.1 * rowWeight τ fixedBadMask 1 1 t (selProduct p.1 x.1 ^ 2) *
          collRowFactor s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T z := by
  set tc := CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L with htc
  set Φ : Tuple κ → ℂ := fun v => (Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t
    (finiteTupleProduct v) * primaryGaussRow (finiteTupleProduct v) z with hΦ
  rw [gauss_tuple_sum _ _ (fun I => (Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I) z]
  have hstep : ∀ v ∈ Fintype.piFinset s.pools,
      colPart J tc v * ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct v) *
        primaryGaussRow (finiteTupleProduct v) z) =
      ∑ p ∈ patterns J, tc v * patMask J p.1 p.2 v * Φ v := by
    intro v hv
    rw [colPart_patterns J tc v (fun hne => tc_structure s J A₁ A₂ Dc K R L F v hv hne),
      Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [pattern_sum s J p.1 p.2 A₁ A₂ Dc K R L F Φ]
  apply Finset.sum_congr rfl
  intro x _
  have hfac : ∀ a ∈ collBox s p.1 p.2 x,
      tc (collTuple p.1 p.2 x.1 a) * patMask J p.1 p.2 (collTuple p.1 p.2 x.1 a) *
          Φ (collTuple p.1 p.2 x.1 a) =
        selWeight s p.1 K R x.1 *
          (noColPart (restBlock J p.1)
            (CoupledFirst.tupleCoefficient (collInput s p.1 p.2 x.1 (collH s p.1 p.2 x 0)
                (collH s p.1 p.2 x 1))
              (markedSourceModifier (A₁ * sideProd p.2 x.1 0) (A₂ * sideProd p.2 x.1 1) Dc K F)
              (R * selProduct p.1 x.1) (residualSeed p.1 L x.1)) a *
            (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t
                (selProduct p.1 x.1 ^ 2 * finiteTupleProduct a)) *
              primaryGaussRow (selProduct p.1 x.1 ^ 2 * finiteTupleProduct a) z)) := by
    intro a _
    rw [htc, coll_factor_mask_supplier s J p.1 p.2 x.1 (collH s p.1 p.2 x 0) (collH s p.1 p.2 x 1)
      A₁ A₂ Dc K R L F a hLsq x.2 (hF p.1 x.1 x.2 _)]
    simp only [hΦ, collTuple_product]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  by_cases hw : selWeight s p.1 K R x.1 = 0
  · rw [hw]
    ring
  · rw [coll_assignment_identity s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T hw z]
    ring

/-! ### Bounds on the assignment terms -/

/-- The family energy of a collision assignment at the ball radius `H`. -/
def famEnergy (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H : ℝ) : ℝ :=
  (gaussEnergy Finset.univ
    (sourceGenerator (finiteColumns (collBox s Q σ x)))
    (sourceGenerator_supported (finiteColumns (collBox s Q σ x)))
    (fun I : supportedColumns (finiteColumns (collBox s Q σ x)) =>
      finiteColumnCoefficient (collBox s Q σ x)
        (noColPart (restBlock J Q)
          (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
            (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
            (R * selProduct Q x.1) (residualSeed Q L x.1))) I *
        ((Real.sqrt T : ℂ)⁻¹ *
          rowWeight τ fixedBadMask 1 (primaryGenerator (selProduct Q x.1) ^ 3) t I))
    ballProfile H).re

theorem famPoly_rows (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H : ℝ)
    (hH : 0 < H) (rows : Finset O) (hrows : ∀ z ∈ rows, normValue z ≤ H) :
    ∑ z ∈ rows, ‖famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T z‖ ^ 2 ≤
      famEnergy s J Q σ x A₁ A₂ Dc K R L F τ t T H :=
  finite_energy_le_gaussEnergy _ _ _ _ ballProfile H hH rows (fun _ => ballProfile_nonneg _)
    (fun z hz => ballProfile_majorizes H hH z (hrows z hz))

theorem famEnergy_nonneg (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H : ℝ)
    (hH : 0 < H) : 0 ≤ famEnergy s J Q σ x A₁ A₂ Dc K R L F τ t T H :=
  ball_energy_nonneg _ _ _ _ H hH

/-- On the support of the family coefficient the column is coprime to the colliding product. -/
theorem fam_support_coprime (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox s Q}) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (a : Tuple {i // i ∉ Q})
    (ha : noColPart (restBlock J Q)
      (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
        (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
        (R * selProduct Q x.1) (residualSeed Q L x.1)) a ≠ 0) :
    IsCoprime (selProduct Q x.1) (finiteTupleProduct a) := by
  have hne : CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
      (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
      (R * selProduct Q x.1) (residualSeed Q L x.1) a ≠ 0 := by
    intro h0
    apply ha
    simp only [noColPart, h0, zero_mul]
  exact (IsCoprime.of_mul_right_right (profile_coprime _ _ _ _ a hne)).symm

/-- An assignment term vanishes at the zero frequency (the pattern is nonempty). -/
theorem assign_term_zero (s : Input κ) (J Q : Finset κ) (hQ : Q.Nonempty) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox s Q}) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) :
    selWeight s Q K R x.1 * rowWeight τ fixedBadMask 1 1 t (selProduct Q x.1 ^ 2) *
      collRowFactor s J Q σ x A₁ A₂ Dc K R L F τ t T 0 = 0 := by
  by_cases hw : selWeight s Q K R x.1 = 0
  · rw [hw, zero_mul, zero_mul]
  have hu : ∀ j, Prime (x.1 j) := fun j => s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)
  have hinj := sel_injective_of_weight s Q K R x.1 x.2 hw
  rw [mul_assoc, ← coll_assignment_identity s J Q σ x A₁ A₂ Dc K R L F τ t T hw 0]
  rw [Finset.sum_eq_zero, mul_zero]
  intro a _
  by_cases ha : noColPart (restBlock J Q)
      (CoupledFirst.tupleCoefficient (collInput s Q σ x.1 (collH s Q σ x 0) (collH s Q σ x 1))
        (markedSourceModifier (A₁ * sideProd σ x.1 0) (A₂ * sideProd σ x.1 1) Dc K F)
        (R * selProduct Q x.1) (residualSeed Q L x.1)) a = 0
  · rw [ha, zero_mul]
  · rw [coll_row_zero_at_zero hQ x.1 hu hinj _ (fam_support_coprime s J Q σ x A₁ A₂ Dc K R L F a ha),
      mul_zero, mul_zero]

theorem collRowFactor_eq_zero_of_not_dvd (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox s Q}) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) (z : O)
    (h : ¬primaryGenerator (selProduct Q x.1) ∣ z) :
    collRowFactor s J Q σ x A₁ A₂ Dc K R L F τ t T z = 0 := by
  unfold collRowFactor
  simp only [h, ↓reduceIte]

theorem collRowFactor_eq_zero_of_not_supported (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox s Q}) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) (z : O) (h : ¬Supported (selProduct Q x.1)) :
    collRowFactor s J Q σ x A₁ A₂ Dc K R L F τ t T z = 0 := by
  have h2 : ¬Supported (selProduct Q x.1 ^ 2) := by
    intro hs
    rw [pow_two, supported_mul_iff] at hs
    exact h hs.1
  unfold collRowFactor
  split_ifs
  · rw [primaryGaussRow_of_not_supported _ h2, zero_mul]
  · rfl

/-- The norm of an assignment term. -/
theorem assign_term_norm (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2)
    (x : {u // u ∈ selBox s Q}) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) (z : O) :
    ‖selWeight s Q K R x.1 * rowWeight τ fixedBadMask 1 1 t (selProduct Q x.1 ^ 2) *
        collRowFactor s J Q σ x A₁ A₂ Dc K R L F τ t T z‖ ^ 2 ≤
      ‖selWeight s Q K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct Q x.1) : ℝ) *
        ‖famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T
          (quotOf (primaryGenerator (selProduct Q x.1)) z)‖ ^ 2 := by
  by_cases hw : selWeight s Q K R x.1 = 0
  · rw [hw]
    simp only [zero_mul, norm_zero]
    norm_num
  have hu : ∀ j, Prime (x.1 j) := fun j => s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)
  have hinj := sel_injective_of_weight s Q K R x.1 x.2 hw
  have hrw := CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all τ fixedBadMask 1 1 t
    (selProduct Q x.1 ^ 2)
  have hrow := coll_square_norm x.1 hu hinj z
  have hN : (0 : ℝ) ≤ (Ideal.absNorm (selProduct Q x.1) : ℝ) := Nat.cast_nonneg _
  unfold collRowFactor
  split_ifs with hd
  · rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow]
    have hrow2 : ‖primaryGaussRow (selProduct Q x.1 ^ 2) z‖ ^ 2 ≤
        (Ideal.absNorm (selProduct Q x.1) : ℝ) := by
      calc _ ≤ (Real.sqrt (Ideal.absNorm (selProduct Q x.1) : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hrow 2
        _ = _ := Real.sq_sqrt hN
    have hrw2 : ‖rowWeight τ fixedBadMask 1 1 t (selProduct Q x.1 ^ 2)‖ ^ 2 ≤ 1 := by
      calc _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hrw 2
        _ = 1 := one_pow 2
    have h1 := sq_nonneg ‖selWeight s Q K R x.1‖
    have h2 := sq_nonneg ‖famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T
      (quotOf (primaryGenerator (selProduct Q x.1)) z)‖
    calc _ ≤ ‖selWeight s Q K R x.1‖ ^ 2 * 1 *
          ((Ideal.absNorm (selProduct Q x.1) : ℝ) *
            ‖famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T
              (quotOf (primaryGenerator (selProduct Q x.1)) z)‖ ^ 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hrw2 h1)
            (mul_le_mul_of_nonneg_right hrow2 h2) (mul_nonneg (sq_nonneg _) h2)
            (mul_nonneg h1 zero_le_one)
      _ = _ := by ring
  · simp only [mul_zero, norm_zero]
    norm_num
    positivity

/-- The number of assignments of a pattern whose square factor can be nonzero at `z ≠ 0`. -/
theorem assign_count (ε : ℝ) (N : ℕ) (Cf : ℝ)
    (hfib : ∀ m : ℕ, m ≤ N → ∀ r : O, r ≠ 0 →
      ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {r})).card : ℝ) ^ m ≤ Cf * (normValue r) ^ ε)
    (s : Input κ) (hcard : Fintype.card κ ≤ N) (Q : Finset κ) (K R : Ideal O) (z : O) (hz : z ≠ 0) :
    (((selBox s Q).attach.filter (fun x => selWeight s Q K R x.1 ≠ 0 ∧
        Supported (selProduct Q x.1) ∧ primaryGenerator (selProduct Q x.1) ∣ z)).card : ℝ) ≤
      Cf * (normValue z) ^ ε := by
  have hI : (Ideal.span {z} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hz
  have hle : ((selBox s Q).attach.filter (fun x => selWeight s Q K R x.1 ≠ 0 ∧
        Supported (selProduct Q x.1) ∧ primaryGenerator (selProduct Q x.1) ∣ z)).card ≤
      ((selBox s Q).filter (fun u => (∏ j, u j) ∣ Ideal.span {z})).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.1)
    · intro x hx
      obtain ⟨_, _, hs, hd⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨x.2, ?_⟩
      change selProduct Q x.1 ∣ Ideal.span {z}
      rw [Ideal.dvd_iff_le, ← primary_span_supported _ hs]
      exact Ideal.span_singleton_le_span_singleton.mpr hd
    · intro x _ y _ h
      exact Subtype.ext h
  have hc := QRH.MixedStep.Residual.divisor_assignments_card (selBox s Q) (Ideal.span {z}) hI
  have hQN : Fintype.card Q ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ Q).trans hcard
  calc _ ≤ (((selBox s Q).filter (fun u => (∏ j, u j) ∣ Ideal.span {z})).card : ℝ) := by
        exact_mod_cast hle
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {z})).card : ℝ) ^ Fintype.card Q := by
        exact_mod_cast hc
    _ ≤ _ := hfib _ hQN z hz

theorem patterns_card_le (J : Finset κ) : (patterns J).card ≤ 4 ^ J.card := by
  unfold patterns
  rw [Finset.card_sigma]
  calc ∑ Q ∈ J.powerset.filter (fun Q => Q.Nonempty), (Finset.univ : Finset (Q → Fin 2)).card
      ≤ ∑ _Q ∈ J.powerset, 2 ^ J.card := by
        apply (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
        apply Finset.sum_le_sum
        intro Q hQ
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
        exact Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card (Finset.mem_powerset.mp hQ))
    _ = 4 ^ J.card := by
        rw [Finset.sum_const, Finset.card_powerset, smul_eq_mul, ← mul_pow]
        norm_num

theorem nonempty_of_mem_patterns {J : Finset κ} {p : Σ Q : Finset κ, Q → Fin 2}
    (hp : p ∈ patterns J) : p.1.Nonempty := by
  unfold patterns at hp
  exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).1).2

/-- The family rows of one assignment, pulled back to the family frequencies. -/
theorem fam_rows_bound (s : Input κ) (J Q : Finset κ) (σ : Q → Fin 2) (x : {u // u ∈ selBox s Q})
    (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T H : ℝ)
    (hH : 0 < H) :
    ∑ z ∈ ((ballRows H).erase 0).filter
        (fun z => Supported (selProduct Q x.1) ∧ primaryGenerator (selProduct Q x.1) ∣ z),
      ‖famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T
        (quotOf (primaryGenerator (selProduct Q x.1)) z)‖ ^ 2 ≤
      famEnergy s J Q σ x A₁ A₂ Dc K R L F τ t T
        (2 * H / (Ideal.absNorm (selProduct Q x.1) : ℝ)) := by
  have hD0 : selProduct Q x.1 ≠ 0 := by
    unfold selProduct
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact (s.prime j.val (x.1 j) (Fintype.mem_piFinset.mp x.2 j)).ne_zero
  have hN : (0 : ℝ) < (Ideal.absNorm (selProduct Q x.1) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have hH' : 0 < 2 * H / (Ideal.absNorm (selProduct Q x.1) : ℝ) := by positivity
  by_cases hs : Supported (selProduct Q x.1)
  · set δ := primaryGenerator (selProduct Q x.1) with hδ
    have hδN : normValue δ = (Ideal.absNorm (selProduct Q x.1) : ℝ) := by
      unfold normValue
      rw [hδ, primary_span_supported _ hs]
    set Z := ((ballRows H).erase 0).filter
      (fun z => Supported (selProduct Q x.1) ∧ δ ∣ z) with hZ
    have hinj : Set.InjOn (quotOf δ) Z := by
      intro z₁ h₁ z₂ h₂ he
      have hd₁ := (Finset.mem_filter.mp h₁).2.2
      have hd₂ := (Finset.mem_filter.mp h₂).2.2
      rw [quotOf_spec hd₁, quotOf_spec hd₂, he]
    rw [← Finset.sum_image (f := fun z' => ‖famPoly s J Q σ x A₁ A₂ Dc K R L F τ t T z'‖ ^ 2) hinj]
    apply famPoly_rows s J Q σ x A₁ A₂ Dc K R L F τ t T _ hH'
    intro z' hz'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hz'
    obtain ⟨hzb, hzs, hzd⟩ := Finset.mem_filter.mp hz
    have hlt := (mem_ballRows H z).mp (Finset.mem_erase.mp hzb).2
    rw [quotOf_spec hzd, normValue_mul, hδN] at hlt
    rw [le_div_iff₀ hN]
    linarith
  · have hZ : ((ballRows H).erase 0).filter
        (fun z => Supported (selProduct Q x.1) ∧ primaryGenerator (selProduct Q x.1) ∣ z) = ∅ := by
      apply Finset.filter_false_of_mem
      intro z _ h
      exact hs h.1
    rw [hZ, Finset.sum_empty]
    exact famEnergy_nonneg s J Q σ x A₁ A₂ Dc K R L F τ t T _ hH'

/-- **The collision part of a source is bounded by its collision families.** -/
theorem collision_energy_families (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type u} [Fintype κ] [DecidableEq κ], Fintype.card κ ≤ N →
    ∀ (s : Input κ) (J : Finset κ) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H : ℝ), 0 < H → Squarefree L →
      (∀ (Q : Finset κ) (u : Q → Ideal O), u ∈ selBox s Q → ∀ n : Ideal O,
        F (Dc * (selProduct Q u ^ 2 * n)) = F (Dc * n)) →
      (gaussEnergy Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            finiteColumnCoefficient (Fintype.piFinset s.pools)
              (colPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re ≤
        C * (max 1 (2 * H)) ^ ε *
          ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
            if Supported (selProduct p.1 x.1) then
              ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
                famEnergy s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
                  (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ))
            else 0 := by
  obtain ⟨Cf, hCf, hfib⟩ := fiber_power_bound ε hε N
  refine ⟨4 ^ N * Cf, by positivity, ?_⟩
  intro κ _ _ hcard s J A₁ A₂ Dc K R L F τ t T H hH hLsq hF
  set a : (p : Σ Q : Finset κ, Q → Fin 2) → {u // u ∈ selBox s p.1} → O → ℂ :=
    fun p x z => selWeight s p.1 K R x.1 * rowWeight τ fixedBadMask 1 1 t (selProduct p.1 x.1 ^ 2) *
      collRowFactor s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T z with ha
  set g : (p : Σ Q : Finset κ, Q → Fin 2) → {u // u ∈ selBox s p.1} → O → ℝ :=
    fun p x z => ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
      ‖famPoly s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
        (quotOf (primaryGenerator (selProduct p.1 x.1)) z)‖ ^ 2 with hg
  have hg0 : ∀ p x z, 0 ≤ g p x z := fun p x z => by
    simp only [hg]
    positivity
  set Z : (p : Σ Q : Finset κ, Q → Fin 2) → {u // u ∈ selBox s p.1} → Finset O :=
    fun p x => ((ballRows H).erase 0).filter
      (fun z => Supported (selProduct p.1 x.1) ∧ primaryGenerator (selProduct p.1 x.1) ∣ z) with hZ
  refine (ball_energy_le_sum _ _ _ _ H hH).trans ?_
  have hid : ∀ z, gaussPolynomial Finset.univ
      (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
      (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
      (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
        finiteColumnCoefficient (Fintype.piFinset s.pools)
          (colPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
          ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) z =
      ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x z :=
    fun z => coll_poly_identity s J A₁ A₂ Dc K R L F τ t T hLsq hF z
  simp only [hid]
  -- the zero frequency contributes nothing
  have hzero : (∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro x _
    exact assign_term_zero s J p.1 (nonempty_of_mem_patterns hp) p.2 x A₁ A₂ Dc K R L F τ t T
  have hdrop : ∑ z ∈ ballRows H, ‖∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2 =
      ∑ z ∈ (ballRows H).erase 0, ‖∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2 := by
    by_cases h0 : (0 : O) ∈ ballRows H
    · rw [← Finset.add_sum_erase _ _ h0, hzero, norm_zero, zero_pow (by norm_num), zero_add]
    · rw [Finset.erase_eq_of_notMem h0]
  rw [hdrop]
  have hpc : ((patterns J).card : ℝ) ≤ 4 ^ N := by
    have h := patterns_card_le J
    have hJ : J.card ≤ N := (Finset.card_le_univ J).trans hcard
    calc ((patterns J).card : ℝ) ≤ ((4 ^ J.card : ℕ) : ℝ) := by exact_mod_cast h
      _ = (4 : ℝ) ^ J.card := by push_cast; ring
      _ ≤ 4 ^ N := pow_le_pow_right₀ (by norm_num) hJ
  have hM : 0 ≤ (max 1 (2 * H)) ^ ε := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  -- the bound at one frequency
  have hpoint : ∀ z ∈ (ballRows H).erase 0,
      ‖∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2 ≤
        4 ^ N * Cf * (max 1 (2 * H)) ^ ε *
          ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, if z ∈ Z p x then g p x z else 0 := by
    intro z hz
    obtain ⟨hz0, hzb⟩ := Finset.mem_erase.mp hz
    have hnz : normValue z ^ ε ≤ (max 1 (2 * H)) ^ ε := by
      apply Real.rpow_le_rpow (by unfold normValue; positivity) _ hε.le
      exact ((mem_ballRows H z).mp hzb).le.trans (le_max_right _ _)
    have hinner : ∀ p ∈ patterns J, ‖∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2 ≤
        Cf * (max 1 (2 * H)) ^ ε *
          ∑ x ∈ (selBox s p.1).attach, if z ∈ Z p x then g p x z else 0 := by
      intro p _
      set S := (selBox s p.1).attach.filter (fun x => selWeight s p.1 K R x.1 ≠ 0 ∧
        Supported (selProduct p.1 x.1) ∧ primaryGenerator (selProduct p.1 x.1) ∣ z) with hS
      have hsum : ∑ x ∈ (selBox s p.1).attach, a p x z = ∑ x ∈ S, a p x z := by
        rw [hS, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs with hc
        · rfl
        · simp only [not_and_or] at hc
          rcases hc with hc | hc | hc
          · simp only [ha, not_not.mp hc, zero_mul]
          · simp only [ha, collRowFactor_eq_zero_of_not_supported s J p.1 p.2 x A₁ A₂ Dc K R L F
              τ t T z hc, mul_zero]
          · simp only [ha, collRowFactor_eq_zero_of_not_dvd s J p.1 p.2 x A₁ A₂ Dc K R L F
              τ t T z hc, mul_zero]
      have hcount := assign_count ε N Cf hfib s hcard p.1 K R z hz0
      have hS2 : ∑ x ∈ S, ‖a p x z‖ ^ 2 ≤
          ∑ x ∈ (selBox s p.1).attach, if z ∈ Z p x then g p x z else 0 := by
        rw [← Finset.sum_filter]
        calc ∑ x ∈ S, ‖a p x z‖ ^ 2 ≤ ∑ x ∈ S, g p x z :=
              Finset.sum_le_sum (fun x _ =>
                assign_term_norm s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T z)
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x hx
                obtain ⟨hxa, _, hs, hd⟩ := Finset.mem_filter.mp hx
                exact Finset.mem_filter.mpr ⟨hxa, Finset.mem_filter.mpr ⟨hz, hs, hd⟩⟩
              · intro x _ _
                exact hg0 p x z
      have hite : 0 ≤ ∑ x ∈ (selBox s p.1).attach, if z ∈ Z p x then g p x z else 0 :=
        Finset.sum_nonneg (fun x _ => by
          split_ifs
          · exact hg0 p x z
          · exact le_refl 0)
      have hnv : 0 ≤ normValue z ^ ε := Real.rpow_nonneg (by unfold normValue; positivity) _
      rw [hsum]
      calc ‖∑ x ∈ S, a p x z‖ ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖a p x z‖ ^ 2 :=
            norm_sum_sq_le_card S _
        _ ≤ (Cf * normValue z ^ ε) *
              ∑ x ∈ (selBox s p.1).attach, (if z ∈ Z p x then g p x z else 0) :=
            mul_le_mul hcount hS2 (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
              (mul_nonneg hCf.le hnv)
        _ ≤ Cf * (max 1 (2 * H)) ^ ε *
              ∑ x ∈ (selBox s p.1).attach, (if z ∈ Z p x then g p x z else 0) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnz hCf.le) hite
    have hinnerNonneg : ∀ p ∈ patterns J,
        0 ≤ Cf * (max 1 (2 * H)) ^ ε *
          ∑ x ∈ (selBox s p.1).attach, (if z ∈ Z p x then g p x z else 0) := by
      intro p _
      apply mul_nonneg (mul_nonneg hCf.le hM)
      exact Finset.sum_nonneg (fun x _ => by
        split_ifs
        · exact hg0 p x z
        · exact le_refl 0)
    calc ‖∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2
        ≤ ((patterns J).card : ℝ) *
            ∑ p ∈ patterns J, ‖∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2 :=
          norm_sum_sq_le_card _ _
      _ ≤ 4 ^ N * ∑ p ∈ patterns J, Cf * (max 1 (2 * H)) ^ ε *
            ∑ x ∈ (selBox s p.1).attach, (if z ∈ Z p x then g p x z else 0) :=
          mul_le_mul hpc (Finset.sum_le_sum hinner) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
            (by positivity)
      _ = _ := by
          rw [← Finset.mul_sum]
          ring
  calc ∑ z ∈ (ballRows H).erase 0,
        ‖∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach, a p x z‖ ^ 2
      ≤ ∑ z ∈ (ballRows H).erase 0, 4 ^ N * Cf * (max 1 (2 * H)) ^ ε *
          ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
            (if z ∈ Z p x then g p x z else 0) :=
        Finset.sum_le_sum hpoint
    _ = 4 ^ N * Cf * (max 1 (2 * H)) ^ ε * ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
          ∑ z ∈ Z p x, g p x z := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_ite_mem]
        congr 1
        exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    _ ≤ 4 ^ N * Cf * (max 1 (2 * H)) ^ ε * ∑ p ∈ patterns J, ∑ x ∈ (selBox s p.1).attach,
          if Supported (selProduct p.1 x.1) then
            ‖selWeight s p.1 K R x.1‖ ^ 2 * (Ideal.absNorm (selProduct p.1 x.1) : ℝ) *
              famEnergy s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T
                (2 * H / (Ideal.absNorm (selProduct p.1 x.1) : ℝ))
          else 0 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro x _
        by_cases hs : Supported (selProduct p.1 x.1)
        · rw [if_pos hs]
          simp only [hg]
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (fam_rows_bound s J p.1 p.2 x A₁ A₂ Dc K R L F τ t T H hH) (by positivity)
        · rw [if_neg hs]
          have hZe : Z p x = ∅ := by
            apply Finset.filter_false_of_mem
            intro z _ h
            exact hs h.1
          rw [hZe, Finset.sum_empty]

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.coll_factor_supplier
#print axioms QRH.MixedStep.Collision.coll_factor_mask_supplier
#print axioms QRH.MixedStep.Collision.coll_poly_identity
#print axioms QRH.MixedStep.Collision.collision_energy_families
